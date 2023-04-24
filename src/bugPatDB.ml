open Core
open Z3utils
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map

let rec get_args_rec expr =
  Z3.Expr.get_args expr
  |> List.fold_left ~init:[] ~f:(fun args a ->
         if Z3.Expr.is_const a then a :: args else get_args_rec a @ args)
  |> List.rev

let collect_vars =
  Fun.flip
    (ExprSet.fold (fun r vars ->
         get_args_rec r |> List.fold_left ~init:vars ~f:(Fun.flip ExprSet.add)))
    ExprSet.empty

let collect_sem_vars =
  Fun.flip
    (ExprSet.fold (fun r vars ->
         get_args_rec r |> List.tl_exn
         |> List.fold_left ~init:vars ~f:(Fun.flip ExprSet.add)))
    ExprSet.empty

let collect_children var rels =
  ExprSet.filter
    (fun r ->
      get_args_rec r
      |> (if is_sem_rels r then (Fun.flip List.nth_exn) 1 else List.hd_exn)
      |> Z3.Expr.equal var)
    rels

let collect_correls var rels =
  ExprSet.filter
    (fun r ->
      get_args_rec r |> List.tl_exn
      |> (Fun.flip List.mem ~equal:Z3.Expr.equal) var)
    rels

let collect_rels var rels =
  ExprSet.filter
    (fun r -> get_args_rec r |> List.exists ~f:(Z3.Expr.equal var))
    rels

let collect_cfpath rels = ExprSet.filter is_cfpath rels
let collect_dupath rels = ExprSet.filter is_dupath rels

let is_removable rels rel =
  let have_no_child =
    List.for_all ~f:(fun var ->
        if
          Z3.Expr.get_sort var |> Z3.Sort.equal z3env.int_sort
          && Z3.Expr.is_numeral var
        then true
        else collect_children var rels |> ExprSet.cardinal = 0)
  in
  let vars = get_args_rec rel in
  if (is_cfpath ||| is_dupath) rel then
    List.exists
      ~f:(fun var ->
        let rels = collect_children var rels in
        ExprSet.filter (is_cfpath ||| is_dupath |> neg) rels
        |> ExprSet.cardinal = 0)
      vars
  else if is_binop rel then
    let v1 = List.nth_exn vars 1 in
    let v2 = List.nth_exn vars 2 in
    collect_children v1 rels |> ExprSet.cardinal = 0
    || collect_children v2 rels |> ExprSet.cardinal = 0
  else if is_unop rel then
    collect_children (List.nth_exn vars 1) rels |> ExprSet.cardinal = 0
  else if is_node_rels rel then
    match vars with
    | node_var :: tl_vars ->
        let alarm_rel = ExprSet.filter is_alarm rels |> ExprSet.choose in
        let src_snk = get_args_rec alarm_rel in
        let src_node, snk_node =
          (List.hd_exn src_snk, List.nth_exn src_snk 1)
        in
        (Z3.Expr.equal src_node ||| Z3.Expr.equal snk_node) node_var |> not
        && have_no_child tl_vars
    | _ -> Logger.error "is_removable: Invalid arguments"
  else List.tl_exn vars |> have_no_child

let rec elim_rel ~remove_cands ~must_rel ~must_var except_sem_cons sem_cons
    patch_facts =
  Logger.info "Try Matching... Elim Phase - # of rel: %d"
    (ExprSet.cardinal except_sem_cons);
  let rc = ExprSet.diff remove_cands must_rel in
  if ExprSet.is_empty rc then except_sem_cons
  else
    let selected = ExprSet.min_elt rc in
    Logger.debug "selected: %s" (Z3.Expr.to_string selected);
    let rc' = ExprSet.remove selected rc in
    let except_sem_cons' = ExprSet.remove selected except_sem_cons in
    let patch_matched = match_rule patch_facts except_sem_cons' in
    if Option.is_some patch_matched then (
      Logger.info "Patch Matched: selected rel is %s"
        (Z3.Expr.to_string selected);
      elim_rel ~remove_cands:rc
        ~must_rel:(ExprSet.add selected must_rel)
        ~must_var except_sem_cons sem_cons patch_facts)
    else (
      Logger.info "Patch Not Matched: removed rel is %s"
        (Z3.Expr.to_string selected);
      let new_remove_cand_vars = get_args_rec selected in
      let new_rcc =
        List.fold_left ~init:ExprSet.empty
          ~f:(fun rcc var ->
            collect_rels var except_sem_cons' |> ExprSet.union rcc)
          new_remove_cand_vars
      in
      let pat_cand' = ExprSet.union except_sem_cons' sem_cons in
      let new_rc = ExprSet.filter (is_removable pat_cand') new_rcc in
      elim_rel ~remove_cands:(ExprSet.union rc' new_rc) ~must_rel ~must_var
        except_sem_cons' sem_cons patch_facts)

let collect_nodes_after_alarm node cfpaths =
  let afters =
    ExprSet.fold
      (fun du nodes ->
        let from_to = Z3.Expr.get_args du in
        let _from, _to = (List.hd_exn from_to, List.nth_exn from_to 1) in
        if Z3.Expr.equal node _from then ExprSet.add _to nodes else nodes)
      cfpaths ExprSet.empty
  in
  let fliped_path n after = Z3.FuncDecl.apply z3env.cfpath [ after; n ] in
  ExprSet.filter
    (fun after ->
      fliped_path node after |> (Fun.flip ExprSet.mem) cfpaths |> not)
    afters

let collect_after_alarm node rels =
  let cfpaths = ExprSet.filter is_cfpath rels in
  let rels_except_cfpaths = ExprSet.diff rels cfpaths in
  let afters = collect_nodes_after_alarm node cfpaths in
  ExprSet.fold
    (fun after rs ->
      collect_children after rels_except_cfpaths |> ExprSet.union rs)
    afters ExprSet.empty

let remove_rels_after_alarms alarm syn_rels sem_rels =
  let except_sem_cons = ExprSet.union syn_rels sem_rels in
  let alarm_node = get_args_rec alarm |> List.tl_exn |> List.hd_exn in
  let after_rels = collect_after_alarm alarm_node except_sem_cons in
  ExprSet.diff except_sem_cons after_rels

let collect_sem_deps sem_rels sem_cons =
  let rec fixedpoint deps =
    let vars = collect_sem_vars deps in
    let new_deps =
      ExprSet.fold
        (fun var deps -> collect_rels var sem_rels |> ExprSet.union deps)
        vars deps
    in
    if ExprSet.equal new_deps deps then new_deps else fixedpoint new_deps
  in
  let must_vars = collect_vars sem_cons in
  let deps =
    ExprSet.fold
      (fun var deps -> collect_rels var sem_rels |> ExprSet.union deps)
      must_vars ExprSet.empty
  in
  fixedpoint deps

let remove_no_deps_from_sem_cons except_sem_cons sem_cons =
  let sem_rels = ExprSet.filter is_sem_rels except_sem_cons in
  let syn_rels = ExprSet.diff except_sem_cons sem_rels in
  let sem_deps = collect_sem_deps sem_rels sem_cons in
  (syn_rels, sem_deps)

let abstract_bug_pattern out_dir =
  let patch_facts = Z3.Fixedpoint.get_rules z3env.patch_solver in
  let pat_cand =
    Z3.Fixedpoint.get_rules z3env.pattern_solver
    |> List.filter ~f:(neg (is_skip ||| is_ret))
    |> ExprSet.of_list
  in
  let alarm =
    ExprSet.filter is_alarm pat_cand |> ExprSet.choose (* TODO: iteration *)
  in
  let sem_cons = ExprSet.filter is_sem_cons pat_cand in
  let sem_rels = ExprSet.filter is_sem_rels pat_cand in
  let syn_rels =
    ExprSet.filter (neg (is_alarm ||| is_sem_rels ||| is_sem_cons)) pat_cand
    |> ExprSet.add alarm
  in
  let except_sem_cons = remove_rels_after_alarms alarm syn_rels sem_rels in
  let syn_rels', sem_rels' =
    remove_no_deps_from_sem_cons except_sem_cons sem_cons
  in
  let except_sem_cons' = ExprSet.union syn_rels' sem_rels' in
  let pat_cand = ExprSet.union except_sem_cons' sem_cons in
  Logger.info "Pattern Candidate:\n%a\n" ExprSet.pp pat_cand;
  let remove_cands = ExprSet.filter (is_removable pat_cand) except_sem_cons' in
  let syn_rels'' =
    elim_rel ~remove_cands ~must_rel:sem_rels' ~must_var:ExprSet.empty
      except_sem_cons' sem_cons patch_facts
  in
  let except_sem_cons'' = ExprSet.union syn_rels'' sem_rels' in
  let pattern_smt_file = Filename.concat out_dir "pattern.smt2" in
  let oc = Out_channel.create pattern_smt_file in
  ExprSet.union except_sem_cons'' sem_cons
  |> set2list
  |> List.map ~f:Z3.Expr.to_string
  |> String.concat ~sep:"\n"
  |> (fun s ->
       Logger.info "Bug Pattern Rule:\n%s" s;
       s)
  |> Out_channel.output_string oc;
  Out_channel.close oc

let run donor_dir patch_dir db_dir =
  Logger.info "Extract Bug Pattern...";
  let out_dir = Filename.basename donor_dir |> Filename.concat db_dir in
  let donor_maps, patch_maps = (Maps.create_maps (), Maps.create_maps ()) in
  Maps.reset_maps donor_maps;
  Maps.reset_maps patch_maps;
  Maps.reset_globals ();
  Facts.make ~add_var_too:true ~maps:donor_maps z3env.donor_solver donor_dir;
  SemCons.make ~add_var_too:true donor_maps z3env.donor_solver donor_dir;
  Facts.make ~maps:patch_maps z3env.patch_solver patch_dir;
  Maps.dump "donor" donor_maps z3env.donor_solver out_dir;
  Maps.dump "patch" patch_maps z3env.patch_solver out_dir;
  Logger.info "Make facts done";
  abstract_bug_pattern out_dir
