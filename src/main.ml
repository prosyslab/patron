let extract_bug_pattern opts bench_dir true_alarm out_dir =
  let buggy_dir = Filename.concat bench_dir "bug" in
  let patch_dir = Filename.concat bench_dir "patch" in
  if (Sys.file_exists buggy_dir && Sys.file_exists patch_dir) |> not then (
    prerr_endline "Error: No target directory specified";
    exit 1)
  else PatMat.run opts true_alarm buggy_dir patch_dir out_dir

let main () =
  let options = Options.parse () in
  if options.Options.memtrace then
    Memtrace.start_tracing ~context:(Some "patron") ~sampling_rate:1e-6
      ~filename:(Filename.concat options.Options.out_dir "memtrace")
    |> ignore;
  let opts = (options.Options.inline, options.Options.write_out) in
  Logger.info "Starting Patron...";
  extract_bug_pattern opts options.Options.bench_dir options.Options.true_alarm
    options.Options.out_dir

let _ = main ()
