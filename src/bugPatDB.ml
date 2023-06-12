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

let match_rule out_dir ver_name maps chc pattern =
  let solver = mk_fixedpoint z3env.z3ctx in
  reg_rel_to_solver z3env solver;
  Chc.add_all maps solver (Chc.union chc pattern);
  Z3utils.dump_solver_to_smt (ver_name ^ "_match") solver out_dir;
  let status = Z3.Fixedpoint.query_r solver [ z3env.bug ] in
  match status with
  | Z3.Solver.UNSATISFIABLE -> None
  | Z3.Solver.SATISFIABLE -> Z3.Fixedpoint.get_answer solver
  | Z3.Solver.UNKNOWN -> None

let pattern_match out_dir ver_name maps chc pattern =
  let status = match_rule out_dir ver_name maps chc pattern in
  Option.iter
    ~f:(fun ans ->
      L.info "Matched";
      Z3utils.dump_expr_to_smt (ver_name ^ "_ans") ans out_dir)
    status

let run donor_dir patch_dir db_dir =
  L.info "Add Bug Pattern to DB...";
  let out_dir = Filename.basename donor_dir |> Filename.concat db_dir in
  let donor_maps, patch_maps = (Maps.create_maps (), Maps.create_maps ()) in
  Maps.reset_maps donor_maps;
  Maps.reset_maps patch_maps;
  Maps.reset_globals ();
  let donor = Parser.make donor_dir in
  let patch = Parser.make patch_dir in
  Chc.pretty_dump (Filename.concat out_dir "donor") donor;
  Chc.pretty_dump (Filename.concat out_dir "patch") patch;
  Logger.info "Make CHC done";
  let alarm_map = Parser.mk_alarm_map donor_dir in
  let (_, snk), one_alarm = Parser.AlarmMap.choose alarm_map in
  let pattern = abstract_bug_pattern donor snk one_alarm in
  Logger.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  L.info "Try matching with Donor...";
  pattern_match out_dir "donor" donor_maps donor pattern;
  L.info "Try matching with Patch...";
  pattern_match out_dir "patch" patch_maps patch pattern
