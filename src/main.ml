let init donee_dir =
  let out_dir = Filename.concat donee_dir !Cmdline.out_dir in
  (try Unix.mkdir out_dir 0o775 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir);
  Filename.concat out_dir "log.txt" |> Logger.from_file;
  Logger.set_level !Cmdline.log_level

let main () =
  let usage = "Usage: patron <Donor dir> <Patch dir> <Donee dir> [options]" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  if
    not
      (Sys.file_exists !Cmdline.donor_dir
      && Sys.file_exists !Cmdline.patch_dir
      && Sys.file_exists !Cmdline.donee_dir)
  then (
    prerr_endline "Error: No target directory specified";
    exit 1)
  else
    let donor_dir, patch_dir, donee_dir =
      (!Cmdline.donor_dir, !Cmdline.patch_dir, !Cmdline.donee_dir)
    in
    init donee_dir;
    Patmat.pattern_match donor_dir patch_dir donee_dir

let _ = main ()
