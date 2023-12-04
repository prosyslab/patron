open Core
open Z3env
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map

let rec fixedpoint rels terms deps =
  let deps', terms' =
    Chc.fold
      (fun c (deps, terms) ->
        let is_nec, terms' = Chc.prop_deps terms c in
        ((if is_nec then Chc.add c deps else deps), terms'))
      rels (deps, terms)
  in
  if Chc.subset deps' deps && Chc.subset terms' terms then (deps', terms')
  else fixedpoint rels terms' deps'

let remove_before_src_after_snk src snk rels =
  let src_node, snk_node = (Chc.Elt.FDNumeral src, Chc.Elt.FDNumeral snk) in
  let before_src = Chc.collect_node ~before:true src_node rels in
  let after_snk = Chc.collect_node ~before:false snk_node rels in
  let before_deps = fixedpoint rels before_src Chc.empty |> fst in
  let after_deps = fixedpoint rels after_snk Chc.empty |> fst in
  rels |> (Fun.flip Chc.diff) before_deps |> (Fun.flip Chc.diff) after_deps

let collect_deps src snk terms chc =
  let func_apps =
    Chc.extract_func_apps chc |> remove_before_src_after_snk src snk
  in
  fixedpoint func_apps terms Chc.empty
  |> fst
  |> Chc.filter (fun dep -> Chc.Elt.is_duedge dep |> not)
  |> Chc.inter chc

let sort_rule_optimize ref deps =
  let get_args = function
    | Chc.Elt.FuncApply (s, args) -> (s, args)
    | _ -> failwith "not implemented"
  in
  let hv_common_elt rel1 rel2 =
    let name1, args1 = get_args rel1 in
    let _, args2 = get_args rel2 in
    let eq_elt arg1 arg2 =
      Chc.Elt.equal arg1 arg2
      && (not (String.equal name1 "BinOP"))
      && not (String.equal name1 "UnOP")
    in
    List.exists
      ~f:(fun arg1 -> List.exists ~f:(fun arg2 -> eq_elt arg1 arg2) args2)
      args1
  in
  let init =
    List.filter ~f:(fun dep -> hv_common_elt ref dep) deps |> List.hd_exn
  in
  let deps = List.filter ~f:(fun dep -> not (Chc.Elt.equal init dep)) deps in
  let rec mk_lcs_list record1 lst record2 acc cand out =
    match lst with
    | [] ->
        if List.length record2 = 0 then out
        else
          let prev = List.hd_exn cand in
          let cand' = List.tl_exn cand in
          let prev_rec = List.hd_exn record2 in
          let record = List.tl_exn record2 in
          let snapshot = List.tl_exn record1 in
          mk_lcs_list snapshot prev_rec record prev cand' (acc :: out)
    | hd :: tl ->
        let last = List.hd_exn acc in
        if hv_common_elt hd last then
          let new_deps = List.hd_exn record1 in
          let new_lst =
            List.filter ~f:(fun dep -> not (Chc.Elt.equal dep hd)) new_deps
          in
          let record1 =
            if List.hd_exn record1 |> List.length = List.length new_lst then
              record1
            else new_lst :: record1
          in
          mk_lcs_list record1 new_lst (tl :: record2) (hd :: acc) (acc :: cand)
            out
        else mk_lcs_list record1 tl record2 acc cand out
  in
  let _, lcs =
    mk_lcs_list [ deps ] deps [] [ init ] [] []
    |> List.fold_left ~init:(0, []) ~f:(fun (len, acc) lst ->
           if List.length lst > len then (List.length lst, lst) else (len, acc))
  in
  let unsorted =
    List.filter
      ~f:(fun dep ->
        not (List.mem lcs ~equal:(fun x y -> Chc.Elt.equal x y) dep))
      deps
  in
  (lcs |> List.rev) @ (unsorted |> List.rev)

let abstract_bug_pattern donor src snk alarm =
  let alarm_rels = Chc.filter_func_app alarm in
  let init_terms =
    Chc.fold
      (fun rel terms -> Chc.add_args_to_terms terms rel)
      alarm_rels Chc.empty
  in
  let deps = collect_deps src snk init_terms donor |> Chc.to_list in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.src := src;
  Z3env.snk := snk;
  let deps = sort_rule_optimize errtrace deps in
  let errtrace_rule = Chc.Elt.Implies (deps, errtrace) |> Chc.Elt.numer2var in
  let error_cons = Chc.Elt.numer2var alarm in
  let err_rel = Chc.Elt.get_head error_cons in
  let bug_rule =
    Chc.Elt.Implies ([ errtrace (*; err_rel*) ], Chc.Elt.FuncApply ("Bug", []))
  in
  Chc.of_list [ errtrace_rule; (*error_cons;*) bug_rule ]

let run (i_opt, w_opt) target_dir donor_dir patch_dir db_dir =
  L.info "Add Bug Pattern to DB...";
  let out_dir =
    (Filename.dirname target_dir |> Filename.basename)
    ^ "-"
    ^ Filename.basename target_dir
    |> Filename.concat db_dir
  in
  let donor_maps, patch_maps = (Maps.create_maps (), Maps.create_maps ()) in
  Maps.reset_maps donor_maps;
  Maps.reset_maps patch_maps;
  let donor_ast =
    Parser.parse_ast donor_dir |> fun f ->
    if List.length i_opt <> 0 then Inline.perform i_opt f else f
  in
  let patch_ast =
    Parser.parse_ast patch_dir |> fun f ->
    if List.length i_opt <> 0 then Inline.perform i_opt f else f
  in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff donor_ast patch_ast in
  L.info "Mapping CFG Elements to AST nodes...";
  let sym_diff = SymDiff.define_sym_diff donor_dir donor_ast ast_diff in
  if w_opt then L.info "Writing out the edit script...";
  SymDiff.to_json sym_diff ast_diff out_dir;
  (* TODO: iter this process so that there will be n Chcs *)
  let donor = Parser.make donor_dir donor_ast sym_diff in
  Chc.pretty_dump (Filename.concat out_dir "donor") donor;
  Chc.sexp_dump (Filename.concat out_dir "donor") donor;
  L.info "Make CHC done";
  let alarm_map = Parser.mk_alarm_map donor_dir in
  let (src, snk), one_alarm = Parser.AlarmMap.choose alarm_map in
  let pattern = abstract_bug_pattern donor src snk one_alarm in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern") pattern;
  L.info "Try matching with Donor...";
  reset_env ();
  (* let z3env = get_env () in *)
  Chc.match_and_log out_dir "donor" donor_maps donor pattern;
  (* L.info "Try matching with Patch...";
     Chc.match_and_log out_dir "patch" patch_maps patch pattern [ z3env.bug ]; *)
  Maps.dump "donor" donor_maps out_dir;
  (* Maps.dump "patch" patch_maps out_dir; *)
  L.info "Done."
