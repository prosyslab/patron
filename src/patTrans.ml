open Core
open Z3utils
module L = Logger

let fold_db f db_dir =
  Sys_unix.fold_dir ~init:(false, "")
    ~f:(fun (matched, donor) cand ->
      if matched then (matched, donor)
      else (
        L.debug "Try matching with %s..." cand;
        let cand_path = Filename.concat db_dir cand in
        if f cand_path then (true, cand) else (matched, donor)))
    db_dir

let match_bug out_dir donee donee_maps donor_cand_path =
  let pattern =
    Parser.parse_chc (Filename.concat donor_cand_path "pattern_mach.chc")
    |> Chc.map Chc.numer2var
  in
  let status = Chc.pattern_match donee_maps donee pattern [ z3env.bug ] in
  if Option.is_some status then (
    Option.iter
      ~f:(fun ans ->
        L.info "Donee Matched";
        Z3utils.dump_expr_to_smt "donee_ans" ans out_dir)
      status;
    true)
  else (
    L.info "Donee Not Matched";
    false)

let match_ans out_dir donor_dir donee_dir = ()

let run db_dir donee_dir out_dir =
  L.info "Finding bug pattern from DB...";
  let donee_maps = Maps.create_maps () in
  Maps.reset_maps donee_maps;
  Maps.reset_globals ();
  let donee = Parser.make donee_dir in
  Chc.pretty_dump (Filename.concat out_dir "donee") donee;
  Chc.sexp_dump (Filename.concat out_dir "donee") donee;
  L.info "Make CHC done";
  let _, donor_dir = fold_db (match_bug out_dir donee donee_maps) db_dir in
  let donor_dir = Filename.concat db_dir donor_dir in
  match_ans out_dir donor_dir donee_dir
