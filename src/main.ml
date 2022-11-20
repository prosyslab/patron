let init work_dir =
  let out_dir = Filename.concat work_dir !Cmdline.out_dir in
  (try Unix.mkdir out_dir 0o775 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir);
  Filename.concat !Cmdline.out_dir "log.txt" |> Logger.from_file

let main () =
  let usage = "Usage: patron [options] [work dir]" in
  Arg.parse Cmdline.options Cmdline.parse_arg usage;
  match !Cmdline.work_dir with
  | None ->
      prerr_endline "Error: No work directory specified";
      exit 1
  | Some work_dir ->
      init work_dir;
      Patmat.pattern_match work_dir

let _ = main ()
