open Core
open Continue_or_stop
module Hashtbl = Stdlib.Hashtbl
module F = Format
module L = Logger
module Sys = Stdlib.Sys
module H = Utils
module Cil = ProsysCil.Cil

let mk_file_diff orig_path patch_path cand_donor target_alarm out_dir =
  Sys.command
    (String.concat
       [
         "diff -u ";
         orig_path;
         " ";
         patch_path;
         " > ";
         Filename.concat out_dir
           ("result_" ^ cand_donor ^ "_" ^ target_alarm ^ "_diff.patch");
       ])
  |> ignore

let match_once z3env cand_donor donor_dir buggy_maps target_maps
    (donee_facts, donee_src, donee_snk) target_alarm ast out_dir i cmd =
  match
    F.asprintf "pattern_%d_mach.chc" i
    |> Filename.concat donor_dir |> Sys_unix.file_exists
  with
  | `No | `Unknown -> Continue ()
  | `Yes ->
      let src_ic = Filename.concat donor_dir "src" in
      Z3env.buggy_src := In_channel.read_all src_ic;
      let snk_ic = Filename.concat donor_dir "snk" in
      Z3env.buggy_snk := In_channel.read_all snk_ic;
      let pattern =
        F.asprintf "pattern_%d_mach.chc" i
        |> Filename.concat donor_dir |> Parser.parse_chc
        |> Chc.map Chc.Elt.numer2var
      in
      let patpat =
        F.asprintf "patch_pattern_%d_mach.chc" i
        |> Filename.concat donor_dir |> Parser.parse_chc
        |> Chc.map Chc.Elt.numer2var
      in
      let cdp_ic =
        F.asprintf "abs_diff_%d.marshal" i
        |> Filename.concat donor_dir |> In_channel.create
      in
      let diff = Marshal.from_channel cdp_ic in
      In_channel.close cdp_ic;
      L.info "Pattern Matching on %d-th level pattern" i;
      L.info "First, trying to match %s with bug pattern" target_alarm;
      let is_bug =
        Chc.match_and_log z3env out_dir target_alarm target_maps donee_facts
          donee_src donee_snk pattern
      in
      Maps.dump target_alarm target_maps out_dir;
      if Option.is_some is_bug then
        let is_pat =
          L.info "%s is Matched with bug pattern" target_alarm;
          L.info "Now, trying to match %s with patch pattern" target_alarm;
          match cmd with
          | Options.DonorToDonee -> None
          | _ ->
              Chc.match_and_log z3env out_dir target_alarm target_maps
                donee_facts donee_src donee_snk patpat
        in
        if Option.is_none is_pat then (
          L.info "%s is not Matched with patch pattern (Good)" target_alarm;
          Modeling.match_ans buggy_maps target_maps target_alarm i cand_donor
            donor_dir out_dir;
          L.info "Matching with %s is done" target_alarm;
          let target_diff =
            EditFunction.translate cand_donor target_maps out_dir target_alarm
              diff
          in
          L.info "Applying patch on the target file ...";
          let out_file_orig =
            F.asprintf "%s/orig_%s_%s_%d.c" out_dir cand_donor target_alarm i
          in
          DoEdit.write_out out_file_orig ast;
          let patch_file =
            Ast.extract_snk_stmt target_maps.ast_map donee_snk
            |> DoEdit.run ast target_diff
          in
          let out_file_patch =
            F.asprintf "%s/patch_%s_%s_%d.c" out_dir cand_donor target_alarm i
          in
          DoEdit.write_out out_file_patch patch_file;
          L.info "Patch for %s is done, written at %s" target_alarm
            out_file_patch;
          mk_file_diff out_file_orig out_file_patch cand_donor target_alarm
            out_dir;
          Stop ())
        else (
          L.info "%s is Matched with patch pattern (Bad)" target_alarm;
          Continue ())
      else (
        L.info "%s is Not Matched with bug pattern" target_alarm;
        Continue ())

let match_one_by_one ?(db = false) z3env bt_dir donee_dir target_alarm
    inline_funcs out_dir cmd cand_donor =
  L.info "Try matching with %s..." cand_donor;
  let donor_dir = if db then Filename.concat bt_dir cand_donor else out_dir in
  let buggy_maps = Maps.create_maps () in
  let buggy_ic =
    Filename.concat donor_dir "buggy_numeral.map" |> In_channel.create
  in
  Maps.load_numeral_map buggy_ic buggy_maps.numeral_map;
  Cil.resetCIL ();
  let donee_ast = Parser.parse_ast donee_dir inline_funcs in
  let facts, (src, snk, _, _), target_maps =
    Parser.make_facts donee_dir target_alarm donee_ast out_dir cmd
  in
  List.fold_until ~init:()
    ~f:(fun _ i ->
      match_once z3env cand_donor donor_dir buggy_maps target_maps
        (facts, src, snk) target_alarm donee_ast out_dir i cmd)
    [ 0; 1; 2; 3 ] ~finish:ignore

let match_one_alarm ?(db = false) z3env donee_dir inline_funcs out_dir db_dir
    target_alarm cmd =
  L.info "Target Alarm: %s" target_alarm;
  let bug_type = Utils.find_bug_type donee_dir target_alarm in
  if db then
    let bt_dir = Filename.concat db_dir bug_type in
    Sys_unix.ls_dir bt_dir
    |> List.iter
         ~f:
           (match_one_by_one ~db z3env bt_dir donee_dir target_alarm
              inline_funcs out_dir cmd)
  else
    match_one_by_one ~db z3env "" donee_dir target_alarm inline_funcs out_dir
      cmd ""

let run ?(db = false) z3env inline_funcs db_dir donee_dir out_dir cmd =
  Sys_unix.ls_dir (Filename.concat donee_dir "sparrow-out/taint/datalog")
  |> List.rev
  |> List.iter ~f:(fun ta ->
         if String.is_suffix ta ~suffix:".map" then ()
         else
           try
             match_one_alarm ~db z3env donee_dir inline_funcs out_dir db_dir ta
               cmd
           with e -> L.warn "%s" (Exn.to_string e))
