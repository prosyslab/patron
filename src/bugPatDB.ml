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
  fixedpoint terms Chc.empty |> fst |> Chc.inter chc

let abstract_bug_pattern donor snk alarm =
  let alarm_rels = Chc.filter_func_app alarm in
  let init_terms =
    Chc.fold
      (fun rel terms -> Chc.get_args rel |> Chc.add_args_to_terms terms)
      alarm_rels Chc.empty
  in
  let deps =
    collect_deps init_terms donor |> (fun deps -> deps) |> Chc.to_list
  in
  let errnode = Chc.FuncApply ("ErrNode", [ Chc.Var snk ]) in
  let errnode_rule = Chc.Implies (deps, errnode) |> Chc.numer2var in
  let error_cons = Chc.numer2var alarm in
  let err_rel = Chc.get_head error_cons in
  let bug_rule =
    Chc.Implies ([ errnode; err_rel ], Chc.FuncApply ("Bug", []))
  in
  Chc.of_list [ errnode_rule; error_cons; bug_rule ]

let match_rule maps chc pattern =
  let solver = mk_fixedpoint z3env.z3ctx in
  reg_rel_to_solver z3env solver;
  Chc.add_all maps solver (Chc.union chc pattern);
  L.debug "All:\n%a" Chc.pp (Chc.union chc pattern);
  let status = Z3.Fixedpoint.query solver (Z3.FuncDecl.apply z3env.bug []) in
  match status with
  | Z3.Solver.UNSATISFIABLE -> None
  | Z3.Solver.SATISFIABLE -> Z3.Fixedpoint.get_answer solver
  | Z3.Solver.UNKNOWN -> None

let run donor_dir patch_dir db_dir =
  Logger.info "Extract Bug Pattern...";
  let out_dir = Filename.basename donor_dir |> Filename.concat db_dir in
  let donor_maps, patch_maps = (Maps.create_maps (), Maps.create_maps ()) in
  Maps.reset_maps donor_maps;
  Maps.reset_maps patch_maps;
  Maps.reset_globals ();
  let donor = Parser.make donor_dir in
  let patch = Parser.make patch_dir in
  Chc.dump (Filename.concat out_dir "donor.chc") donor;
  Chc.dump (Filename.concat out_dir "patch.chc") patch;
  Logger.info "Make facts done";
  let alarm_map = Parser.mk_alarm_map donor_dir in
  let (_, snk), one_alarm = Parser.AlarmMap.choose alarm_map in
  let pattern = abstract_bug_pattern donor snk one_alarm in
  Chc.dump (Filename.concat out_dir "pattern.chc") pattern;
  let donor_status = match_rule donor_maps donor pattern in
  if Option.is_some donor_status then
    Option.iter
      ~f:(fun ans -> L.info "Answer: %s" (Z3.Expr.to_string ans))
      donor_status
  else L.info "Donor not matched"
