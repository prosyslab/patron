module D = Diff
module S = SymDiff
module T = Translator
module P = Transplanter
module F = Format
module L = Logger
module H = TransformerHelper

let extract_edit_function doner_dir patch_dir db_dir =
  let doner_file =
    Sys.readdir doner_dir |> Array.to_list
    |> List.filter (fun x -> Filename.check_suffix x ".c")
    |> List.hd |> Filename.concat doner_dir
  in
  let patch_file =
    Sys.readdir patch_dir |> Array.to_list
    |> List.filter (fun x -> Filename.check_suffix x ".c")
    |> List.hd |> Filename.concat patch_dir
  in
  let donor, patch =
    ( Diff.parse_file doner_file, Diff.parse_file patch_file)
  in
  L.info "Constructing AST diff...";
  let ast_diff = D.define_diff donor patch in
  L.info "AST diff is constructed";
  D.Diff.pp_edit_script F.std_formatter ast_diff;
  let sym_diff = S.define_sym_diff doner_dir donor ast_diff in
  L.info "Mapping CFG Elements to AST nodes...";
  S.to_json sym_diff ast_diff db_dir;
  L.info "Done";
  L.info
    "Given bug pattern is successfully written into an edit function at %s\n"
    db_dir

(* let transplant db_dir donee_dir patron_out_dir =
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
  P.apply donee translated

let write_out out_dir donee =
  let out_file = out_dir ^ "/applied.c" in
  let out_chan = open_out out_file in
  Cil.dumpFile Cil.defaultCilPrinter out_chan "" donee;
  close_out out_chan *)
