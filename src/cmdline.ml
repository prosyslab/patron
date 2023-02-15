let donor_dir = ref ""
let patch_dir = ref ""
let donee_dir = ref ""
let out_dir = ref "patron-out"
let log_level = ref Logger.INFO
let set_debug () = log_level := Logger.DEBUG

let options =
  [
    ("-outdir", Arg.Set_string out_dir, "Output directory");
    ("-debug", Arg.Unit set_debug, "Enable debug logging");
  ]

let parse_arg arg =
  if !Arg.current = 1 then donor_dir := arg
  else if !Arg.current = 2 then patch_dir := arg
  else if !Arg.current = 3 then donee_dir := arg
  else ()
