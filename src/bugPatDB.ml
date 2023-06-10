open Core
open Z3utils
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map

let collect_deps terms chc =
  let func_apps = Chc.extract_func_apps chc in
  let rec fixedpoint terms deps =
    let deps', terms' =
      Chc.fold
        (fun c (deps, terms) ->
          let is_nec, terms' = Chc.prop_deps terms c in
          ((if is_nec then Chc.add c deps else deps), terms'))
        func_apps (deps, terms)
    in
    if Chc.subset deps' deps && Chc.subset terms' terms then (deps', terms')
    else fixedpoint terms' deps'
  in
  fixedpoint terms Chc.empty |> snd |> Chc.inter chc

let abstract_bug_pattern donor alarm =
  let alarm_rels = Chc.filter_func_app alarm in
  let init_terms =
    Chc.fold
      (fun rel terms -> Chc.get_args rel |> Chc.add_args_to_terms terms)
      alarm_rels Chc.empty
  in
  let deps = collect_deps init_terms donor in
  ()

let run donor_dir patch_dir db_dir =
  Logger.info "Extract Bug Pattern...";
  let out_dir = Filename.basename donor_dir |> Filename.concat db_dir in
  let donor_maps, patch_maps = (Maps.create_maps (), Maps.create_maps ()) in
  Maps.reset_maps donor_maps;
  Maps.reset_maps patch_maps;
  Maps.reset_globals ();
  let donor = Parser.make donor_dir in
  let patch = Parser.make patch_dir in
  let oc_donor = Out_channel.create (Filename.concat out_dir "donor.chc") in
  let fmt_donor = F.formatter_of_out_channel oc_donor in
  F.fprintf fmt_donor "%a" Chc.pp donor;
  F.pp_print_flush fmt_donor ();
  Out_channel.close oc_donor;
  let oc_patch = Out_channel.create (Filename.concat out_dir "patch.chc") in
  let fmt_patch = F.formatter_of_out_channel oc_patch in
  F.fprintf fmt_patch "%a" Chc.pp patch;
  F.pp_print_flush fmt_patch ();
  Out_channel.close oc_patch;
  (* Maps.dump "donor" donor_maps z3env.donor_solver out_dir;
     Maps.dump "patch" patch_maps z3env.patch_solver out_dir; *)
  Logger.info "Make facts done";
  let alarm_map = Parser.mk_alarm_map donor_dir in
  let src_snk, one_alarm = Parser.AlarmMap.choose alarm_map in
  ()
(* abstract_bug_pattern out_dir *)
