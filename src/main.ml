let extract_bug_pattern target_dir db_dir =
  let donor_dir = Filename.concat target_dir "bug" in
  let patch_dir = Filename.concat target_dir "patch" in
  if
    (Sys.file_exists donor_dir && Sys.file_exists patch_dir
   && Sys.file_exists db_dir)
    |> not
  then (
    prerr_endline "Error: No target directory specified";
    exit 1)
  else BugPatDB.run target_dir donor_dir patch_dir db_dir

let patch_transplant db_dir donee_dir out_dir =
  if
    (Sys.file_exists db_dir && Sys.file_exists donee_dir
   && Sys.file_exists out_dir)
    |> not
  then (
    prerr_endline "Error: No target directory specified";
    exit 1)
  else PatTrans.run db_dir donee_dir out_dir

let main () =
  let options = Options.parse () in
  if options.Options.memtrace then
    Memtrace.start_tracing ~context:(Some "patron") ~sampling_rate:1e-6
      ~filename:(Filename.concat options.Options.db_dir "memtrace")
    |> ignore;
  match options.Options.command with
  | Options.DB ->
      extract_bug_pattern options.Options.target_dir options.Options.db_dir
  | Options.Patch ->
      patch_transplant options.Options.db_dir options.Options.donee_dir
        options.Options.patron_out_dir

let _ = main ()
