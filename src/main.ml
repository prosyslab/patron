let extract_bug_pattern donor_dir patch_dir db_dir =
  if
    (Sys.file_exists donor_dir && Sys.file_exists patch_dir
   && Sys.file_exists db_dir)
    |> not
  then (
    prerr_endline "Error: No target directory specified";
    exit 1)
  else BugPatDB.run donor_dir patch_dir db_dir

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
  match options.Options.command with
  | Options.DB ->
      extract_bug_pattern options.Options.donor_dir options.Options.patch_dir
        options.Options.db_dir
  | Options.Patch ->
      patch_transplant options.Options.db_dir options.Options.donee_dir
        options.Options.patron_out_dir

let _ = main ()
