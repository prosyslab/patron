let donor_dir = ref ""
let patch_dir = ref ""
let donee_dir = ref ""
let out_dir = ref "patron-out"
let options = [ ("-outdir", Arg.Set_string out_dir, "Output directory") ]

let parse_arg arg =
  if !Arg.current = 1 then donor_dir := arg
  else if !Arg.current = 2 then patch_dir := arg
  else if !Arg.current = 3 then donee_dir := arg
  else ()
