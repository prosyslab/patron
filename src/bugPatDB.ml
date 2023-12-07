open Core
open Z3env
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module Sys = Stdlib.Sys

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

let collect_deps src snk aexps chc =
  let func_apps =
    Chc.extract_func_apps chc |> remove_before_src_after_snk src snk
  in
  let snk_term = Chc.Elt.FDNumeral snk in
  let terms = Chc.add snk_term aexps in
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

let abstract_bug_pattern buggy src snk aexps =
  let deps = collect_deps src snk aexps buggy |> Chc.to_list in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.src := src;
  Z3env.snk := snk;
  (* let deps = sort_rule_optimize errtrace deps in *)
  let errtrace_rule = Chc.Elt.Implies (deps, errtrace) |> Chc.Elt.numer2var in
  (* let error_cons = Chc.Elt.numer2var alarm in
     let err_rel = Chc.Elt.get_head error_cons in *)
  let bug_rule =
    Chc.Elt.Implies ([ errtrace (*; err_rel*) ], Chc.Elt.FuncApply ("Bug", []))
  in
  Chc.of_list [ errtrace_rule; (*error_cons;*) bug_rule ]

let parse_ast dir i_opt =
  Parser.parse_ast dir |> fun f ->
  if List.length i_opt <> 0 then Inline.perform i_opt f else f

let match_bug_for_one_prj pattern buggy_dir target_alarm ast out_dir =
  let maps = Maps.create_maps () in
  Maps.reset_maps maps;
  try
    let facts, _ =
      Parser.make_facts buggy_dir target_alarm ast out_dir maps.ast_map
    in
    Chc.match_and_log out_dir target_alarm maps facts pattern;
    Maps.dump target_alarm maps out_dir;
    reset_env ();
    L.info "Try matching with %s..." target_alarm;
    L.info "match_bug_for_one_prj: %s is done" target_alarm
  with Parser.Not_impl_aexp -> L.info "PASS"

let run (i_opt, w_opt) target_alarm buggy_dir patch_dir out_dir =
  let buggy_maps = Maps.create_maps () in
  Maps.reset_maps buggy_maps;
  let buggy_ast = parse_ast buggy_dir i_opt in
  let patch_ast = parse_ast patch_dir i_opt in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff buggy_ast patch_ast in
  L.info "Mapping CFG Elements to AST nodes...";
  let sym_diff =
    SymDiff.define_sym_diff buggy_dir target_alarm buggy_ast ast_diff
  in
  if w_opt then (
    L.info "Writing out the edit script...";
    SymDiff.to_json sym_diff ast_diff out_dir);
  L.info "Make Facts in buggy done";
  let buggy_facts, (src, snk, aexps) =
    Parser.make_facts buggy_dir target_alarm buggy_ast out_dir
      buggy_maps.ast_map
  in
  let pattern = abstract_bug_pattern buggy_facts src snk aexps in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern") pattern;
  reset_env ();
  L.info "Try matching with buggy...";
  Chc.match_and_log out_dir "buggy" buggy_maps buggy_facts pattern;
  Maps.dump "buggy" buggy_maps out_dir;
  Sys.readdir (Filename.concat buggy_dir "sparrow-out/taint/datalog")
  |> Array.iter ~f:(fun ta ->
         if
           (not (String.equal target_alarm ta))
           && Sys.is_directory
                (Filename.concat buggy_dir ("sparrow-out/taint/datalog/" ^ ta))
         then match_bug_for_one_prj pattern buggy_dir ta buggy_ast out_dir);
  L.info "Done."
