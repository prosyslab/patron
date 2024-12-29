open Core
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module Sys = Stdlib.Sys

let preproc_using_pattern is_altpat_useful z3env maps src snk facts out_dir i
    (pattern_in_numeral, pattern, patpat, diff) =
  if (not is_altpat_useful) && i = 1 then
    L.info
      "No useful alternative pattern found. Skipping the alternative pattern."
  else
    let i_str = string_of_int i in
    Chc.sexp_dump (Filename.concat out_dir "pattern_" ^ i_str) pattern;
    Chc.pretty_dump (Filename.concat out_dir "pattern_" ^ i_str) pattern;
    Chc.sexp_dump (Filename.concat out_dir "patch_pattern_" ^ i_str) patpat;
    Chc.pretty_dump (Filename.concat out_dir "patch_pattern_" ^ i_str) patpat;
    Maps.dump "buggy" maps out_dir;
    L.info "Try matching with buggy numeral...";
    ( Chc.match_and_log z3env out_dir ("buggy_numer_" ^ i_str) maps facts src
        snk pattern_in_numeral
    |> fun status -> assert (Option.is_some status) );
    Maps.dump ("buggy_numer_" ^ i_str) maps out_dir;
    let src_oc = Filename.concat out_dir "src" in
    Out_channel.write_all src_oc ~data:src;
    let snk_oc = Filename.concat out_dir "snk" in
    Out_channel.write_all snk_oc ~data:snk;
    let diff_oc =
      Filename.concat out_dir ("abs_diff_" ^ i_str ^ ".marshal")
      |> Out_channel.create
    in
    Marshal.to_channel diff_oc diff [];
    Out_channel.close diff_oc

let run z3env inline_funcs write_out true_alarm buggy_dir patch_dir out_dir cmd
    is_strong_pat =
  let buggy_ast = Parser.parse_ast buggy_dir inline_funcs in
  let patch_ast = Parser.parse_ast patch_dir inline_funcs in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff out_dir buggy_ast patch_ast in
  let facts, (src, snk, alarm_exps, alarm_lvs), maps =
    Parser.make_facts buggy_dir true_alarm buggy_ast out_dir cmd
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
  let patterns, is_altpat_useful =
    AbsPat.run maps dug patch_comps alarm_exps alarm_lvs src snk facts abs_diff
      cmd is_strong_pat
  in
  L.info "Making Bug Pattern is done";
  List.iteri
    ~f:(preproc_using_pattern is_altpat_useful z3env maps src snk facts out_dir)
    patterns;
  L.info "Preprocessing with pattern is done."
