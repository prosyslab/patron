module L = Logger

let exist_all = List.for_all Sys.file_exists

let summary cmd donor_dir donee_dir =
  match cmd with
  | Options.DB ->
      L.info "Patron procedure on DB Generation for %s is finished" donor_dir
  | Patch ->
      L.info "Patron procedure on Patch Transplantation for %s is finished"
        donee_dir
  | DonorToDonee ->
      L.info
        "Patron procedure on Donor to Donee direct transplantation is finished\n\
         Donor: %s => Donee: %s" donor_dir donee_dir

let db z3env inline_fns write_out donor_dir true_alarm db_dir out_dir cmd =
  let buggy_dir = Filename.concat donor_dir "bug" in
  let patch_dir = Filename.concat donor_dir "patch" in
  if exist_all [ buggy_dir; patch_dir; db_dir; out_dir ] then
    BugPatDB.run z3env inline_fns write_out true_alarm buggy_dir patch_dir
      out_dir cmd
  else L.error "No target directory specified"

let patch z3env inline_fns db_dir donee_dir out_dir cmd =
  if exist_all [ donee_dir; out_dir ] then
    Patch.run ~db:true z3env inline_fns db_dir donee_dir out_dir cmd
  else L.error "No target directory specified"

let dtd z3env inline_fns write_out donor_dir donee_dir true_alarm out_dir cmd =
  let buggy_dir = Filename.concat donor_dir "bug" in
  let patch_dir = Filename.concat donor_dir "patch" in
  if exist_all [ buggy_dir; patch_dir; donor_dir ] then
    PatMat.run z3env inline_fns write_out true_alarm buggy_dir patch_dir
      donee_dir out_dir cmd
  else L.error "No target directory specified"

let main () =
  let options = Options.parse () in
  Logger.info "Starting Patron...";
  if options.memtrace then
    Memtrace.start_tracing ~context:(Some "patron") ~sampling_rate:1e-6
      ~filename:(Filename.concat options.out_dir "memtrace")
    |> ignore;
  if options.Options.z3_mem_limit then
    Z3.set_global_param "memory_high_watermark" "4294967295";
  let z3env = Z3env.mk_env options.sort_size in
  (match options.Options.command with
  | DB ->
      db z3env options.inline options.write_out options.donor_dir
        options.true_alarm options.db_dir options.out_dir
        options.Options.command
  | Patch ->
      patch z3env options.inline options.db_dir options.donee_dir
        options.out_dir options.Options.command
  | DonorToDonee ->
      dtd z3env options.inline options.write_out options.donor_dir
        options.donee_dir options.true_alarm options.out_dir
        options.Options.command);
  summary options.Options.command options.donor_dir options.donee_dir

let _ = main ()
