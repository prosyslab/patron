open Core
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module Sys = Stdlib.Sys

let get_func str = String.split_on_chars ~on:[ '-' ] str |> List.hd_exn
let get_id str = String.split_on_chars ~on:[ '-' ] str |> List.last_exn

let extract_id elt =
  List.fold_left ~init:[]
    ~f:(fun acc e ->
      match e with
      | Chc.Elt.FDNumeral s | Chc.Elt.Var s -> get_id s :: acc
      | _ -> acc)
    elt

let extract_func elt =
  List.fold_left ~init:[]
    ~f:(fun acc e ->
      match e with
      | Chc.Elt.FDNumeral s | Chc.Elt.Var s -> get_func s :: acc
      | _ -> acc)
    elt

let extract_funcs_from_facts facts =
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply (_, elt) -> extract_func elt @ acc
      | _ -> acc)
    facts []
  |> List.dedup_and_sort ~compare:String.compare

let reduce_parent_facts maps ast facts =
  let func_lst = extract_funcs_from_facts facts in
  let interesting_stmts =
    List.fold ~init:[]
      ~f:(fun acc f ->
        (Utils.extract_target_func_stmt_lst ast f
        |> List.map ~f:(fun s -> Ast.stmt2ast (Some s)))
        @ acc)
      func_lst
    |> List.fold ~init:[] ~f:(fun acc s ->
           try (Hashtbl.find maps.Maps.ast_map s |> string_of_int) :: acc
           with _ -> acc)
  in
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply ("AstParent", elt) ->
          let nodes = [ List.hd_exn elt; List.last_exn elt ] |> extract_id in
          List.fold_left ~init:Chc.empty
            ~f:(fun acc' node ->
              if List.exists ~f:(fun n -> String.equal n node) interesting_stmts
              then Chc.add c acc'
              else acc')
            nodes
          |> Chc.union acc
      | Chc.Elt.FuncApply ("EqNode", elt) ->
          let (func : string) =
            [ List.hd_exn elt ] |> extract_func |> List.hd_exn
          in
          if List.exists ~f:(fun y -> String.equal func y) func_lst then
            Chc.add c acc
          else acc
      | _ -> acc)
    facts Chc.empty

let remove_before_src_after_snk src snk rels =
  let src_node, snk_node = (Chc.Elt.FDNumeral src, Chc.Elt.FDNumeral snk) in
  let before_src = Chc.collect_node ~before:true src_node rels in
  let after_snk = Chc.collect_node ~before:false snk_node rels in
  let before_deps =
    Chc.fixedpoint (Chc.prop_deps ~ignore_duedge:true) rels before_src Chc.empty
    |> fst
  in
  let after_deps =
    Chc.fixedpoint (Chc.prop_deps ~ignore_duedge:true) rels after_snk Chc.empty
    |> fst
  in
  rels |> (Fun.flip Chc.diff) before_deps |> (Fun.flip Chc.diff) after_deps

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

let is_patch_under_func parent ast_map =
  Stdlib.Hashtbl.fold
    (fun k v acc -> if int_of_string parent = v then k :: acc else acc)
    ast_map []
  |> List.hd_exn
  |> fun node -> Ast.is_glob node || Ast.is_fun node

let mk_file_diff orig_path patch_path target_alarm out_dir =
  Sys.command
    (String.concat
       [
         "diff -u ";
         orig_path;
         " ";
         patch_path;
         " > ";
         Filename.concat out_dir ("result_" ^ target_alarm ^ "_diff.patch");
       ])
  |> ignore

let match_bug_for_one_prj pattern buggy_maps donee_dir target_alarm ast cfg
    out_dir diff =
  let target_maps = Maps.create_maps () in
  Maps.reset_maps target_maps;
  try
    let du_facts, parent_facts, (src, snk, _) =
      Parser.make_facts donee_dir target_alarm ast cfg out_dir target_maps
    in
    let parent_facts' = reduce_parent_facts target_maps ast parent_facts in
    let combined_facts = Chc.union du_facts parent_facts' in
    let z3env = Z3env.get_env () in
    L.info "Try matching with %s..." target_alarm;
    let status =
      Chc.match_and_log z3env out_dir target_alarm target_maps combined_facts
        src snk pattern
    in
    Maps.dump target_alarm target_maps out_dir;
    if Option.is_some status then
      Modeling.match_ans buggy_maps target_maps target_alarm out_dir;
    L.info "Matching with %s is done" target_alarm;
    let patch_parent_lst =
      AbsDiff.extract_parent diff buggy_maps.Maps.ast_map |> List.map ~f:fst
    in
    let ef =
      EditFunction.translate ast diff
        (Filename.concat out_dir (target_alarm ^ "_sol.map"))
        target_maps patch_parent_lst parent_facts
    in
    L.info "Applying patch on the target file ...";
    let out_file_orig =
      String.concat [ out_dir; "/orig_"; target_alarm; ".c" ]
    in
    Patch.write_out out_file_orig ast;
    let patch_file = Patch.apply diff ast ef in
    let out_file_patch =
      String.concat [ out_dir; "/patch_"; target_alarm; ".c" ]
    in
    Patch.write_out out_file_patch patch_file;
    L.info "Patch for %s is done, written at %s" target_alarm out_file_patch;
    mk_file_diff out_file_orig out_file_patch target_alarm out_dir
  with Parser.Not_impl_alarm_comps -> L.info "PASS"

let is_new_alarm buggy_dir true_alarm donee_dir target_alarm =
  (not
     (String.equal buggy_dir donee_dir && String.equal true_alarm target_alarm))
  && Sys.is_directory
       (Filename.concat donee_dir ("sparrow-out/taint/datalog/" ^ target_alarm))

let match_with_new_alarms buggy_dir true_alarm donee_dir buggy_maps buggy_ast
    buggy_cfg pattern out_dir diff =
  Sys.readdir (Filename.concat donee_dir "sparrow-out/taint/datalog")
  |> Array.iter ~f:(fun ta ->
         if is_new_alarm buggy_dir true_alarm donee_dir ta then
           match_bug_for_one_prj pattern buggy_maps donee_dir ta buggy_ast
             buggy_cfg out_dir diff)

let run (inline_funcs, write_out) true_alarm buggy_dir patch_dir donee_dir
    out_dir =
  let buggy_maps = Maps.create_maps () in
  Maps.reset_maps buggy_maps;
  let buggy_ast = Parser.parse_ast buggy_dir inline_funcs in
  let patch_ast = Parser.parse_ast patch_dir inline_funcs in
  let donee_ast =
    if String.equal (buggy_dir ^ "/bug") donee_dir then patch_ast
    else Parser.parse_ast donee_dir inline_funcs
  in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff buggy_ast patch_ast in
  L.info "Loading CFG Elements...";
  let buggy_cfg =
    Utils.parse_node_json (Filename.concat buggy_dir "sparrow-out")
  in
  L.info "CFG Elements Loading Done!";
  let du_facts, parent_facts, (src, snk, alarm_comps) =
    Parser.make_facts buggy_dir true_alarm buggy_ast buggy_cfg out_dir
      buggy_maps
  in
  L.info "Make Facts in buggy done";
  let parent_facts' = reduce_parent_facts buggy_maps buggy_ast parent_facts in
  let combined_facts = Chc.union du_facts parent_facts' in
  L.info "Mapping CFG Elements to AST nodes...";
  let dug = Dug.of_facts du_facts in
  let abs_diff =
    AbsDiff.define_abs_diff buggy_maps buggy_ast ast_diff du_facts
      (Dug.copy dug) (src, snk)
  in
  let patch_comps = AbsDiff.mk_patch_comp buggy_maps.cfg_map abs_diff in
  if write_out then (
    L.info "Writing out the edit script...";
    AbsDiff.to_json abs_diff out_dir);
  Maps.dump_ast "buggy" buggy_maps out_dir;
  let pattern_in_numeral, pattern =
    AbsPat.run du_facts parent_facts' dug patch_comps src snk alarm_comps
      buggy_maps abs_diff buggy_ast
  in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern") pattern;
  let z3env = Z3env.get_env () in
  L.info "Try matching with buggy...";
  ( Chc.match_and_log z3env out_dir "buggy" buggy_maps combined_facts src snk
      pattern
  |> fun status -> assert (Option.is_some status) );
  Maps.dump "buggy" buggy_maps out_dir;
  L.info "Try matching with buggy numeral...";
  ( Chc.match_and_log z3env out_dir "buggy_numer" buggy_maps combined_facts src
      snk pattern_in_numeral
  |> fun status -> assert (Option.is_some status) );
  Maps.dump "buggy_numer" buggy_maps out_dir;
  match_with_new_alarms buggy_dir true_alarm donee_dir buggy_maps donee_ast
    buggy_cfg pattern out_dir abs_diff;
  L.info "Done."
