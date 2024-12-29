open Core
module Sys = Stdlib.Sys
module C = Cmdliner
module Cmd = C.Cmd
module Arg = C.Arg
module Manpage = C.Manpage
module Term = C.Term
module F = Format
module L = Logger

type command = DB | Patch | DonorToDonee

let is_dtd = function DonorToDonee -> true | _ -> false
let verbose = ref 0

type t = {
  (* common options *)
  command : command;
  inline : string list;
  z3_mem_limit : bool;
  sort_size : int;
  memtrace : bool;
  debug : bool;
  (* DB/DTD options *)
  db_dir : string;
  donor_dir : string;
  true_alarm : string;
  write_out : bool;
  (* Patch/DTD options *)
  donee_dir : string;
  out_dir : string;
  (* pattern *)
  strong_pattern : bool;
}

let empty =
  {
    (* common options *)
    command = DB;
    inline = [];
    z3_mem_limit = false;
    sort_size = 1000000;
    memtrace = false;
    debug = false;
    (* DB/DTD options *)
    db_dir = "";
    donor_dir = "";
    true_alarm = "";
    write_out = false;
    (* Patch/DTD options *)
    donee_dir = "";
    out_dir = "";
    (* pattern *)
    strong_pattern = false;
  }

let mkdir dirname =
  if Sys.file_exists dirname && Sys.is_directory dirname then ()
  else if Sys.file_exists dirname && not (Sys.is_directory dirname) then
    let _ = L.error "Error: %s already exists." dirname in
    exit 1
  else Core_unix.mkdir ~perm:0o755 dirname

let init inline z3_mem_limit sort_size memtrace debug strong_pattern =
  if debug then L.set_level L.DEBUG else L.set_level L.INFO;
  {
    empty with
    debug;
    inline;
    z3_mem_limit;
    sort_size;
    memtrace;
    strong_pattern;
  }

let common_opt =
  let docs = Manpage.s_common_options in
  let debug =
    Arg.(
      value & flag
      & info [ "g"; "debug" ] ~docs ~doc:"Enable debug mode (verbose logging)")
  in
  let inline_opt =
    Arg.(
      value & opt_all string []
      & info [ "i"; "inline" ] ~docs ~docv:"INLINE"
          ~doc:"Inline functions in the given list")
  in
  let memtrace =
    Arg.(
      value & flag
      & info [ "memtrace" ] ~docs ~docv:"MEMTRACE" ~doc:"do memtrace")
  in
  let z3_mem_limit =
    Arg.(
      value & flag
      & info [ "m"; "mem_limit" ] ~docs ~docv:"MEMLIM"
          ~doc:"Memory limit for Z3")
  in
  let sort_size =
    Arg.(
      value & opt int 1000000
      & info [ "s"; "sort_size" ] ~docs ~docv:"SORT_SIZE"
          ~doc:"Size of finite domain in Z3 context")
  in
  let strong_pattern =
    Arg.(
      value & flag
      & info [ "strong_pattern" ] ~docs ~docv:"STRONG_PATTERN"
          ~doc:"Use strong pattern")
  in
  Term.(
    const init $ inline_opt $ z3_mem_limit $ sort_size $ memtrace $ debug
    $ strong_pattern)

let db_opt copt donor_dir true_alarm db_dir write_out =
  mkdir db_dir;
  let buggy_dir = Filename.concat donor_dir "bug" in
  let bug_type = Utils.find_bug_type buggy_dir true_alarm in
  let bt_dir = Filename.concat db_dir bug_type in
  mkdir bt_dir;
  let out_dir =
    (Filename.dirname donor_dir |> Filename.basename)
    ^ "-"
    ^ Filename.basename donor_dir
    |> Filename.concat bt_dir
  in
  mkdir out_dir;
  Filename.concat out_dir "log.txt" |> L.from_file;
  { copt with command = DB; donor_dir; true_alarm; db_dir; write_out; out_dir }

let db_cmd =
  let name = "db" in
  let doc = "Extract patch pattern from donor project and add it to DB" in
  let man = [ `S Manpage.s_description ] in
  let info = Cmd.info name ~doc ~man in
  let donor_dir =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"DONOR_DIR"
          ~doc:"The target directory that has bug and patch directories")
  in
  let true_alarm =
    Arg.(
      required
      & pos 1 (some string) None
      & info [] ~docv:"true_alarm"
          ~doc:"The true alarm that patched by developer")
  in
  let db_dir =
    let default =
      (Sys.getcwd () |> Filename_unix.realpath |> Filename.concat) "patron-DB"
    in
    Arg.(
      value & opt string default & info [ "db" ] ~docv:"DIR" ~doc:"DB directory")
  in
  let write_out =
    Arg.(
      value & flag
      & info [ "w"; "write_out" ]
          ~doc:"write out the diff.json file containing the detailed diff info")
  in
  Cmd.v info
    Term.(
      const db_opt $ common_opt $ donor_dir $ true_alarm $ db_dir $ write_out)

let patch_opt copt donee_dir db_dir out_dir =
  mkdir db_dir;
  mkdir out_dir;
  Filename.concat out_dir "log.txt" |> L.from_file;
  { copt with command = Patch; donee_dir; db_dir; out_dir }

let patch_cmd =
  let name = "patch" in
  let doc = "Apply patch to donee project using patron DB" in
  let man = [ `S Manpage.s_description ] in
  let info = Cmd.info name ~doc ~man in
  let donee_dir =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"DONEE" ~doc:"The donee directory")
  in
  let db_dir =
    let default =
      (Sys.getcwd () |> Filename_unix.realpath |> Filename.concat) "patron-DB"
    in
    Arg.(
      value & opt string default & info [ "db" ] ~docv:"DIR" ~doc:"DB directory")
  in
  let out_dir =
    let default =
      (Sys.getcwd () |> Filename_unix.realpath |> Filename.concat) "patron-out"
    in
    Arg.(
      value & opt string default
      & info [ "o"; "out-dir" ] ~docv:"DIR" ~doc:"Output directory")
  in
  Cmd.v info Term.(const patch_opt $ common_opt $ donee_dir $ db_dir $ out_dir)

let dtd_opt copt donor_dir true_alarm donee_dir out_dir write_out =
  mkdir out_dir;
  Filename.concat out_dir "log.txt" |> L.from_file;
  {
    copt with
    command = DonorToDonee;
    donor_dir;
    true_alarm;
    donee_dir;
    out_dir;
    write_out;
  }

let dtd_cmd =
  let name = "dtd" in
  let doc = "One Donor to One Donee Patch Transplantation" in
  let man = [ `S Manpage.s_description ] in
  let info = Cmd.info name ~doc ~man in
  let donor_dir =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"DONOR_DIR"
          ~doc:"The target directory that has bug and patch directories")
  in
  let donee_dir =
    Arg.(
      required
      & pos 1 (some file) None
      & info [] ~docv:"DONEE" ~doc:"The donee directory")
  in
  let true_alarm =
    Arg.(
      required
      & pos 2 (some string) None
      & info [] ~docv:"true_alarm"
          ~doc:"The true alarm that patched by developer")
  in
  let out_dir =
    let default =
      (Sys.getcwd () |> Filename_unix.realpath |> Filename.concat) "patron-out"
    in
    Arg.(
      value & opt string default
      & info [ "o"; "out-dir" ] ~docv:"DIR" ~doc:"Output directory")
  in
  let write_out =
    Arg.(
      value & flag
      & info [ "w"; "write_out" ]
          ~doc:"write out the diff.json file containing the detailed diff info")
  in
  Cmd.v info
    Term.(
      const dtd_opt $ common_opt $ donor_dir $ true_alarm $ donee_dir $ out_dir
      $ write_out)

let main_cmd =
  let name = "patron" in
  let doc = "A vaccine for programs" in
  let man =
    [
      `S Manpage.s_description;
      `P "$(tname) transplant a correct patch from matched bug pattern.";
      `S Manpage.s_bugs;
      `P "Report bugs to <changgong.lee@prosys.kaist.ac.kr>";
    ]
  in
  let info = Cmd.info name ~version:"0.0.1" ~doc ~man in
  Cmd.group info [ db_cmd; patch_cmd; dtd_cmd ]

let parse () =
  match Cmd.eval_value main_cmd with
  | Ok v -> ( match v with `Ok t -> t | _ -> exit 1)
  | _ -> exit 1
