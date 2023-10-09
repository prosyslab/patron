open Core
open Z3env
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module TF = Transformer

let rec fixedpoint rels terms deps =
  let deps', terms' =
    Chc.fold
      (fun c (deps, terms) ->
        let is_nec, terms' = Chc.prop_deps terms c in
        ((if is_nec then Chc.add c deps else deps), terms'))
      rels (deps, terms)
  in
  if Chc.subset deps' deps && Chc.subset terms' terms then (deps', terms')
  else fixedpoint rels terms' deps'

let remove_before_src_after_snk src snk rels =
  let src_node, snk_node = (Chc.Elt.FDNumeral src, Chc.Elt.FDNumeral snk) in
  let before_src = Chc.collect_node ~before:true src_node rels in
  let after_snk = Chc.collect_node ~before:false snk_node rels in
  let before_deps = fixedpoint rels before_src Chc.empty |> fst in
  let after_deps = fixedpoint rels after_snk Chc.empty |> fst in
  rels |> (Fun.flip Chc.diff) before_deps |> (Fun.flip Chc.diff) after_deps

let collect_deps src snk terms chc =
  let func_apps =
    Chc.extract_func_apps chc |> remove_before_src_after_snk src snk
  in
  fixedpoint func_apps terms Chc.empty
  |> fst
  |> Chc.filter (fun dep -> Chc.Elt.is_duedge dep |> not)
  |> Chc.inter chc

let abstract_bug_pattern donor src snk alarm =
  let alarm_rels = Chc.filter_func_app alarm in
  let init_terms =
    Chc.fold
      (fun rel terms -> Chc.add_args_to_terms terms rel)
      alarm_rels Chc.empty
  in
  let deps = collect_deps src snk init_terms donor |> Chc.to_list in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.src := src;
  Z3env.snk := snk;
  let errtrace_rule = Chc.Elt.Implies (deps, errtrace) |> Chc.Elt.numer2var in
  let error_cons = Chc.Elt.numer2var alarm in
  let err_rel = Chc.Elt.get_head error_cons in
  let bug_rule =
    Chc.Elt.Implies ([ errtrace (*; err_rel*) ], Chc.Elt.FuncApply ("Bug", []))
  in
  Chc.of_list [ errtrace_rule; (*error_cons;*) bug_rule ]

let run target_dir donor_dir patch_dir db_dir =
  L.info "Add Bug Pattern to DB...";
  let out_dir =
    (Filename.dirname target_dir |> Filename.basename)
    ^ "-"
    ^ Filename.basename target_dir
    |> Filename.concat db_dir
  in
  let donor_maps, patch_maps = (Maps.create_maps (), Maps.create_maps ()) in
  Maps.reset_maps donor_maps;
  Maps.reset_maps patch_maps;
  let donor = Parser.make donor_dir in
  let patch = Parser.make patch_dir in
  Chc.pretty_dump (Filename.concat out_dir "donor") donor;
  Chc.sexp_dump (Filename.concat out_dir "donor") donor;
  Chc.pretty_dump (Filename.concat out_dir "patch") patch;
  Chc.sexp_dump (Filename.concat out_dir "patch") patch;
  L.info "Make CHC done";
  let alarm_map = Parser.mk_alarm_map donor_dir in
  let (src, snk), one_alarm = Parser.AlarmMap.choose alarm_map in
  let pattern = abstract_bug_pattern donor src snk one_alarm in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern") pattern;
  L.info "Try matching with Donor...";
  reset_env ();
  let z3env = get_env () in
  Chc.match_and_log out_dir "donor" donor_maps donor pattern [ z3env.bug ];
  (* L.info "Try matching with Patch...";
     Chc.match_and_log out_dir "patch" patch_maps patch pattern [ z3env.bug ]; *)
  Maps.dump "donor" donor_maps out_dir;
  Maps.dump "patch" patch_maps out_dir;
  (* TODO: work on symdiff after encoding work is done *)
  (* TF.extract_edit_function donor_dir patch_dir out_dir; *)
  L.info "Done."
