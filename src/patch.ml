open Core
open Continue_or_stop
module F = Format
module L = Logger
module Sys = Stdlib.Sys

let mk_file_diff orig_path patch_path target_alarm out_dir =
  Sys.command
    (String.concat
       [
         "diff -u ";
         orig_path;
         " ";
         patch_path;
         " > ";
         Filename.concat out_dir ("result_" ^ target_alarm ^ "_diff.patch");
       ])
  |> ignore

let match_once z3env cand_donor donor_dir buggy_maps donee_dir target_alarm ast
    out_dir i =
  let src_ic = Filename.concat donor_dir "src" in
  Z3env.buggy_src := In_channel.read_all src_ic;
  let snk_ic = Filename.concat donor_dir "snk" in
  Z3env.buggy_snk := In_channel.read_all snk_ic;
  let pattern =
    F.asprintf "pattern_%d_mach.chc" i
    |> Filename.concat donor_dir |> Parser.parse_chc
    |> Chc.map Chc.Elt.numer2var
  in
  let cdp_ic =
    F.asprintf "abs_diff_%d.marshal" i
    |> Filename.concat donor_dir |> In_channel.create
  in
  let diff = Marshal.from_channel cdp_ic in
  In_channel.close cdp_ic;
  let facts, (src, snk, _, _), target_maps =
    Parser.make_facts donee_dir target_alarm ast out_dir
  in
  let status =
    Chc.match_and_log z3env out_dir target_alarm target_maps facts src snk
      pattern
  in
  Maps.dump target_alarm target_maps out_dir;
  if Option.is_some status then (
    Modeling.match_ans buggy_maps target_maps target_alarm i cand_donor
      donor_dir out_dir;
    L.info "Matching with %s is done" target_alarm;
    let target_diff =
      EditFunction.translate cand_donor target_maps out_dir target_alarm diff
    in
    L.info "Applying patch on the target file ...";
    let out_file_orig =
      F.asprintf "%s/orig_%s_%s_%d.c" out_dir cand_donor target_alarm i
    in
    DoEdit.write_out out_file_orig ast;
    let patch_file = DoEdit.run ast target_diff in
    let out_file_patch =
      F.asprintf "%s/patch_%s_%s_%d.c" out_dir cand_donor target_alarm i
    in
    DoEdit.write_out out_file_patch patch_file;
    L.info "Patch for %s is done, written at %s" target_alarm out_file_patch;
    mk_file_diff out_file_orig out_file_patch target_alarm out_dir;
    Stop ())
  else (
    L.info "%s is Not Matched" target_alarm;
    Continue ())

let match_one_by_one ?(db = false) z3env bt_dir donee_dir target_alarm donee_ast
    out_dir cand_donor =
  L.info "Try matching with %s..." cand_donor;
  let donor_dir = if db then Filename.concat bt_dir cand_donor else out_dir in
  let buggy_maps = Maps.create_maps () in
  let buggy_ic =
    Filename.concat donor_dir "buggy_numeral.map" |> In_channel.create
  in
  Maps.load_numeral_map buggy_ic buggy_maps.numeral_map;
  List.fold_until ~init:()
    ~f:(fun _ i ->
      match_once z3env cand_donor donor_dir buggy_maps donee_dir target_alarm
        donee_ast out_dir i)
    [ 0; 1 ] ~finish:ignore

let match_one_alarm ?(db = false) z3env donee_dir donee_ast out_dir db_dir
    target_alarm =
  L.info "Target Alarm: %s" target_alarm;
  let bug_type = Utils.find_bug_type donee_dir target_alarm in
  if db then
    let bt_dir = Filename.concat db_dir bug_type in
    Sys_unix.ls_dir bt_dir
    |> List.iter
         ~f:
           (match_one_by_one ~db z3env bt_dir donee_dir target_alarm donee_ast
              out_dir)
  else match_one_by_one ~db z3env "" donee_dir target_alarm donee_ast out_dir ""

let run ?(db = false) z3env inline_funcs db_dir donee_dir out_dir =
  let donee_ast = Parser.parse_ast donee_dir inline_funcs in
  Sys.readdir (Filename.concat donee_dir "sparrow-out/taint/datalog")
  |> Array.iter
       ~f:(match_one_alarm ~db z3env donee_dir donee_ast out_dir db_dir)
