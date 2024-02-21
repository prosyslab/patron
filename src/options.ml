module C = Cmdliner
module Cmd = C.Cmd
module Arg = C.Arg
module Manpage = C.Manpage
module Term = C.Term
module F = Format
module L = Logger

let verbose = ref 0

type t = {
  donor_dir : string;
  donee_dir : string;
  true_alarm : string;
  out_dir : string;
  inline : string list;
  write_out : bool;
  debug : bool;
  z3_mem_limit : bool;
  memtrace : bool;
}

let mkdir dirname =
  if Sys.file_exists dirname && Sys.is_directory dirname then ()
  else if Sys.file_exists dirname && not (Sys.is_directory dirname) then
    let _ = L.error "Error: %s already exists." dirname in
    exit 1
  else Unix.mkdir dirname 0o755

let init donor_dir donee_dir true_alarm out_dir debug inline memtrace write_out
    z3_mem_limit =
  if debug then L.set_level L.DEBUG else L.set_level L.INFO;
  mkdir out_dir;
  Filename.concat out_dir "log.txt" |> L.from_file;
  {
    donor_dir;
    donee_dir;
    true_alarm;
    out_dir;
    inline;
    write_out;
    debug;
    z3_mem_limit;
    memtrace;
  }

let main_cmd =
  let name = "patron" in
  let doc = "A vaccine for programs" in
  let man =
    [
      `S Manpage.s_description;
      `P "$(tname) transplant a correct patch from matched bug pattern.";
      `S Manpage.s_bugs;
      `P "Report bugs to <jaeho.kim@prosys.kaist.ac.kr>";
    ]
  in
  let info = Cmd.info name ~version:"0.0.1" ~doc ~man in
  let donor_dir =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"DONOR_DIR"
          ~doc:"The DONOR directory that has bug and patch directories")
  in
  let donee_dir =
    Arg.(
      required
      & pos 1 (some file) None
      & info [] ~docv:"DONEE_DIR"
          ~doc:"The donee directory that has bug directory")
  in
  let true_alarm =
    Arg.(
      required
      & pos 2 (some string) None
      & info [] ~docv:"true_alarm"
          ~doc:"The true alarm that patched by developer")
  in
  let docs = Manpage.s_options in
  let out_dir =
    Arg.(
      value
      & opt string Filename.(concat current_dir_name "patron-out")
      & info [ "o"; "out_dir" ] ~docs ~docv:"OUT_DIR"
          ~doc:"The output directory")
  in
  let debug =
    Arg.(
      value & flag
      & info [ "g"; "debug" ] ~doc:"Enable debug mode (verbose logging)")
  in
  let inline_opt =
    Arg.(
      value & opt_all string []
      & info [ "i"; "inline" ] ~docv:"INLINE"
          ~doc:"Inline functions in the given list")
  in
  let memtrace =
    Arg.(value & flag & info [ "memtrace" ] ~docv:"BOOL" ~doc:"do memtrace")
  in
  let write_out =
    Arg.(
      value & flag
      & info [ "w"; "write_out" ]
          ~doc:"write out the diff.json file containing the detailed diff info")
  in
  let z3_mem_limit =
    Arg.(value & flag & info [ "m"; "mem_limit" ] ~doc:"Memory limit for Z3")
  in
  Cmd.v info
    Term.(
      const init $ donor_dir $ donee_dir $ true_alarm $ out_dir $ debug
      $ inline_opt $ memtrace $ write_out $ z3_mem_limit)

let parse () =
  match Cmd.eval_value main_cmd with
  | Ok v -> ( match v with `Ok t -> t | _ -> exit 1)
  | _ -> exit 1
