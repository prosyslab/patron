module C = Cmdliner
module Cmd = C.Cmd
module Arg = C.Arg
module Manpage = C.Manpage
module Term = C.Term
module F = Format
module L = Logger

type command = DB | Patch

let verbose = ref 0

type t = {
  (* common options *)
  command : command;
  debug : bool;
  (* bug pattern DB options *)
  db_dir : string;
  memtrace : bool;
  target_dir : string;
  donee_dir : string;
  patron_out_dir : string;
  inline : string list;
}

let empty =
  {
    (* common options *)
    command = DB;
    debug = false;
    db_dir = "";
    memtrace = false;
    (* bug pattern DB options *)
    target_dir = "";
    (* Patch options *)
    donee_dir = "";
    patron_out_dir = "";
    inline = [];
  }

let init debug db_dir inline memtrace =
  if debug then L.set_level L.DEBUG else L.set_level L.INFO;
  (try Unix.mkdir db_dir 0o775 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  { empty with debug; db_dir; inline; memtrace }

let common_opt =
  let docs = Manpage.s_common_options in
  let debug =
    Arg.(
      value & flag
      & info [ "g"; "debug" ] ~docs ~doc:"Enable debug mode (verbose logging)")
  in
  let db_dir =
    let default =
      (Sys.getcwd () |> Unix.realpath |> Filename.concat) "patron-DB"
    in
    Arg.(
      value & opt string default & info [ "db" ] ~docv:"DIR" ~doc:"DB directory")
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
  Term.(const init $ debug $ db_dir $ inline_opt $ memtrace)

let db_opt copt target_dir =
  let out_dir =
    (Filename.dirname target_dir |> Filename.basename)
    ^ "-"
    ^ Filename.basename target_dir
    |> Filename.concat copt.db_dir
  in
  (try Unix.mkdir out_dir 0o775 with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  Filename.concat out_dir "log.txt" |> L.from_file;
  { copt with command = DB; target_dir }

let db_cmd =
  let name = "db" in
  let doc =
    "Extract (bug pattern, edit script) pair from donor project and add it to \
     DB"
  in
  let man = [ `S Manpage.s_description ] in
  let info = Cmd.info name ~doc ~man in
  let target_dir =
    Arg.(
      required
      & pos 0 (some file) None
      & info [] ~docv:"TARGET_DIR"
          ~doc:"The target directory that has bug and patch directories")
  in
  Cmd.v info Term.(const db_opt $ common_opt $ target_dir)

let patch_opt copt donee_dir patron_out_dir =
  (try Unix.mkdir patron_out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  Filename.concat patron_out_dir "log.txt" |> L.from_file;
  { copt with command = Patch; donee_dir; patron_out_dir }

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
  let patch_out_dir =
    let default =
      (Sys.getcwd () |> Unix.realpath |> Filename.concat) "patron-out"
    in
    Arg.(
      value & opt string default
      & info [ "o"; "out-dir" ] ~docv:"DIR" ~doc:"Output directory")
  in
  Cmd.v info Term.(const patch_opt $ common_opt $ donee_dir $ patch_out_dir)

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
  Cmd.group info [ db_cmd; patch_cmd ]

let parse () =
  match Cmd.eval_value main_cmd with
  | Ok v -> ( match v with `Ok t -> t | _ -> exit 1)
  | _ -> exit 1
