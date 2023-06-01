module D = Diff
module S = SymDiff
module T = Translator
module P = Transplanter
module F = Format
module L = Logger

let patron_out_dir = "patron_out"

let init () =
  Cil.initCIL ();
  Cil.insertImplicitCasts := false;
  (try Unix.mkdir patron_out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ patron_out_dir);
  Filename.concat patron_out_dir "transformer.log.txt" |> L.from_file;
  L.set_level L.DEBUG

let main () =
  init ();
  let arg_error =
    "Argument mismatch: usage:  -database <Donor File> <Patch File> <Donor \
     Sparrow Dir> |  -transplant <Edit Function> <Donee File> <Donee Sparrow \
     Dir> <Sol>"
  in
  match Array.to_list Sys.argv |> List.tl with
  | [ opt; a; b; c ] -> (
      match opt with
      | "-d" | "-db" | "-database" ->
          let donor, patch = (D.parse_file a, D.parse_file b) in
          let ast_diff = D.define_diff donor patch in
          L.info "#ast_diff: %d\n%a\n" (List.length ast_diff)
            D.Diff.pp_edit_script ast_diff;
          let sym_diff =
            S.define_sym_diff (S.map_cil_to_cmd c donor) ast_diff
          in
          S.to_json sym_diff ast_diff patron_out_dir;
          L.debug
            "Given bug pattern is successfully written into an edit function \
             at %s\n"
            patron_out_dir
      | _ -> failwith arg_error)
  | [ opt; a; b; c; d ] -> (
      match opt with
      | "-t" | "-tp" | "-transplant" ->
          let donee = D.parse_file b in
          let edit_function = S.parse_edit_function a in
          let translated = T.translate c donee edit_function d in
          P.apply donee translated patron_out_dir;
          L.debug "Patch is successfully written at %s/applied.c\n"
            patron_out_dir
      | _ -> failwith arg_error)
  | _ -> failwith arg_error

let _ =
  Printexc.record_backtrace true;
  main ()
