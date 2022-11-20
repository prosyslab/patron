let work_dir : string option ref = ref None
let out_dir = ref "patron-out"
let options = [ ("-outdir", Arg.Set_string out_dir, "Output directory") ]
let parse_arg x = work_dir := Some x
