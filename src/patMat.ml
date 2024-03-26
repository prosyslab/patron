open Core
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module Sys = Stdlib.Sys

let sort_rule_optimize ref deps =
  let get_args = function
    | Chc.Elt.FuncApply (s, args) -> (s, args)
    | _ -> L.error "not implemented"
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

let match_bug_for_one_prj i_str pattern buggy_maps donee_dir target_alarm ast
    out_dir diff =
  let facts, (src, snk, _, _), target_maps =
    Parser.make_facts donee_dir target_alarm ast out_dir
  in
  L.info "Try matching with %s..." target_alarm;
  let status =
    Chc.match_and_log Z3env.z3env out_dir target_alarm target_maps facts src snk
      pattern
  in
  Maps.dump target_alarm target_maps out_dir;
  if Option.is_some status then (
    Modeling.match_ans buggy_maps target_maps target_alarm i_str out_dir;
    L.info "Matching with %s is done" target_alarm;
    let target_diff =
      EditFunction.translate target_maps out_dir target_alarm diff
    in
    L.info "Applying patch on the target file ...";
    let out_file_orig =
      String.concat [ out_dir; "/orig_"; target_alarm; "_"; i_str; ".c" ]
    in
    Patch.write_out out_file_orig ast;
    let patch_file = Patch.apply ast target_diff in
    let out_file_patch =
      String.concat [ out_dir; "/patch_"; target_alarm; "_"; i_str; ".c" ]
    in
    Patch.write_out out_file_patch patch_file;
    L.info "Patch for %s is done, written at %s" target_alarm out_file_patch;
    mk_file_diff out_file_orig out_file_patch target_alarm out_dir)
  else L.info "%s is Not Matched" target_alarm

let is_new_alarm buggy_dir true_alarm donee_dir target_alarm =
  (not
     (String.equal buggy_dir donee_dir && String.equal true_alarm target_alarm))
  && Sys.is_directory
       (Filename.concat donee_dir ("sparrow-out/taint/datalog/" ^ target_alarm))

let match_with_new_alarms buggy_dir true_alarm donee_dir buggy_maps buggy_ast
    i_str pattern out_dir diff =
  Sys.readdir (Filename.concat donee_dir "sparrow-out/taint/datalog")
  |> Array.iter ~f:(fun ta ->
         if is_new_alarm buggy_dir true_alarm donee_dir ta then
           match_bug_for_one_prj i_str pattern buggy_maps donee_dir ta buggy_ast
             out_dir diff)

let match_each_pattern inline_funcs true_alarm buggy_dir donee_dir out_dir
    patch_ast maps facts src snk i (pattern_in_numeral, pattern, abs_diff) =
  let i_str = string_of_int i in
  let donee_ast =
    if String.equal (buggy_dir ^ "/bug") donee_dir then patch_ast
    else Parser.parse_ast donee_dir inline_funcs
  in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern_" ^ i_str) pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern_" ^ i_str) pattern;
  Maps.dump "buggy" maps out_dir;
  L.info "Try matching with buggy numeral...";
  ( Chc.match_and_log Z3env.z3env out_dir ("buggy_numer_" ^ i_str) maps facts
      src snk pattern_in_numeral
  |> fun status -> assert (Option.is_some status) );
  Maps.dump ("buggy_numer_" ^ i_str) maps out_dir;
  match_with_new_alarms buggy_dir true_alarm donee_dir maps donee_ast i_str
    pattern out_dir abs_diff;
  L.info "Done."

let run (inline_funcs, write_out) true_alarm buggy_dir patch_dir donee_dir
    out_dir =
  let buggy_ast = Parser.parse_ast buggy_dir inline_funcs in
  let patch_ast = Parser.parse_ast patch_dir inline_funcs in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff out_dir buggy_ast patch_ast in
  let facts, (src, snk, alarm_exps, alarm_lvs), maps =
    Parser.make_facts buggy_dir true_alarm buggy_ast out_dir
  in
  L.info "Making Facts in buggy done";
  L.info "Making DUG...";
  let dug = Dug.of_facts maps.lval_map maps.cmd_map facts in
  L.info "Making DUG is done";
  L.info "Making Abstract Diff...";
  let abs_diff, patch_comps =
    AbsDiff.define_abs_diff maps buggy_ast dug ast_diff
  in
  L.info "Making Abstract Diff is done";
  if write_out then (
    L.info "Writing out the edit script...";
    DiffJson.dump abs_diff out_dir);
  let patterns =
    AbsPat.run maps dug patch_comps alarm_exps alarm_lvs src snk facts abs_diff
  in
  (* NOTE: always try matching alt_pat for testing *)
  List.iteri
    ~f:
      (match_each_pattern inline_funcs true_alarm buggy_dir donee_dir out_dir
         patch_ast maps facts src snk)
    patterns
