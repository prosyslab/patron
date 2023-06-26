module D = Diff
module S = SymDiff
module T = Translator
module P = Transplanter
module F = Format
module L = Logger
module H = TransformerHelper

let extract_edit_function doner_dir patch_dir db_dir =
  let doner_file = Filename.concat doner_dir "main.c" in
  let patch_file = Filename.concat patch_dir "main.c" in
  let doner_sparrow_dir = Filename.concat doner_dir "sparrow-out" in
  let donor, patch = (D.parse_file doner_file, D.parse_file patch_file) in
  let ast_diff = D.define_diff donor patch in
  L.info "#ast_diff: %d\n%a\n" (List.length ast_diff) D.Diff.pp_edit_script
    ast_diff;
  let sym_diff =
    S.define_sym_diff doner_sparrow_dir
      (S.map_cil_to_cmd doner_sparrow_dir donor)
      ast_diff
  in
  S.to_json sym_diff ast_diff db_dir;
  L.info
    "Given bug pattern is successfully written into an edit function at %s\n"
    db_dir

let transplant db_dir donee_dir patron_out_dir =
  let edit_function_path = Filename.concat db_dir "example01/diff.json" in
  let donee_file = Filename.concat donee_dir "main.c" in
  let donee_sparrow_dir = Filename.concat donee_dir "sparrow-out" in
  let solution_path = Filename.concat patron_out_dir "sol.map" in
  let donee = D.parse_file donee_file in
  let sink_node =
    H.extract_snk
      (Filename.concat donee_sparrow_dir "taint/datalog/IOErrorConstraint.rules")
  in
  let edit_function = S.parse_edit_function sink_node edit_function_path in
  let translated =
    T.translate donee_sparrow_dir donee edit_function solution_path
  in
  P.apply donee translated patron_out_dir;
  L.info "Patch is successfully written at %s/applied.c\n" patron_out_dir
