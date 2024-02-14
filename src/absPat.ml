open Core
module Hashtbl = Stdlib.Hashtbl
module L = Logger

let rec fixedpoint rels terms deps =
  let deps', terms' =
    Chc.fold
      (fun c (deps, terms) ->
        let is_nec, terms' = Chc.road_to_node terms c in
        ((if is_nec then Chc.add c deps else deps), terms'))
      rels (deps, terms)
  in
  if Chc.subset deps' deps && Chc.subset terms' terms then (deps', terms')
  else fixedpoint rels terms' deps'

let abstract_by_comps chc dug patch_comps snk alarm_comps =
  L.info "patch_comps: %s" (String.concat ~sep:", " patch_comps);
  L.info "alarm_comps: %s"
    (alarm_comps |> Chc.to_list |> Chc.Elt.terms2strs |> String.concat ~sep:", ");
  let du_rels = Chc.filter Chc.Elt.is_duedge chc in
  let ast_rels = Chc.diff chc du_rels in
  let terms =
    List.map ~f:(fun s -> Chc.Elt.FDNumeral s) patch_comps
    |> Chc.of_list |> Chc.union alarm_comps
  in
  let abs_ast_rels, terms' = fixedpoint ast_rels terms Chc.empty in
  let nodes = Chc.to_list terms' |> Chc.Elt.terms2strs |> Chc.filter_by_node in
  L.info "nodes: %s" (String.concat ~sep:", " nodes);
  let dug = Dug.copy dug in
  let paths =
    List.fold_left
      ~f:(fun paths src -> Dug.shortest_path dug src snk :: paths)
      ~init:[] nodes
  in
  let abs_du_rels = Dug.paths2rels paths in
  Chc.union abs_ast_rels abs_du_rels

let rec go_up parent_tups ast_node_lst (parent, child) acc =
  let candidates =
    List.fold_left ~init:[]
      ~f:(fun cand (parent', child') ->
        if String.equal parent parent' && not (String.equal child child') then
          (parent', child') :: cand
        else cand)
      parent_tups
  in
  if List.length candidates = 0 then
    let upper_tups_opt =
      List.find ~f:(fun (_, c') -> String.equal parent c') parent_tups
    in
    let upper_tups =
      if Option.is_none upper_tups_opt then
        failwith "compute_ast_pattern: common ancestor not found"
      else Option.value_exn upper_tups_opt
    in
    go_up parent_tups ast_node_lst upper_tups (upper_tups :: acc)
  else if
    List.exists
      ~f:(fun (_, c') ->
        List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
      candidates
  then
    List.find_exn
      ~f:(fun (_, c') ->
        List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
      candidates
    :: acc
  else
    let down = fold_down parent_tups ast_node_lst candidates [] in
    if List.length down = 0 then
      let upper_tups_opt =
        List.find ~f:(fun (_, c') -> String.equal parent c') acc
      in
      let upper_tups =
        if Option.is_none upper_tups_opt then
          failwith "common ancestor not found!"
        else Option.value_exn upper_tups_opt
      in
      go_up parent_tups ast_node_lst upper_tups (upper_tups :: acc)
    else acc @ down

and go_down parent_tups ast_node_lst (p, c) acc =
  let candidates =
    List.fold_left ~init:[]
      ~f:(fun acc' (p', c') ->
        if String.equal c p' then (p', c') :: acc' else acc')
      parent_tups
  in
  if List.length candidates = 0 then []
  else
    let is_found =
      List.exists
        ~f:(fun (_, c') ->
          List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
        candidates
    in
    if is_found then
      List.find_exn
        ~f:(fun (_, c') ->
          List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
        candidates
      :: acc
    else fold_down parent_tups ast_node_lst candidates ((p, c) :: acc)

and fold_down parent_tups ast_node_lst candidates acc =
  List.fold_left ~init:[]
    ~f:(fun acc' edge ->
      go_down parent_tups ast_node_lst edge (edge :: acc) @ acc')
    candidates

let mk_parent_tups_str func stmts ast_map =
  Parser.mk_parent_tuples func stmts
  |> List.fold_left ~init:[] ~f:(fun acc (p, c) ->
         if Hashtbl.mem ast_map p && Hashtbl.mem ast_map c then
           ( Hashtbl.find ast_map p |> string_of_int,
             Hashtbl.find ast_map c |> string_of_int )
           :: acc
         else acc)

let greedy_search_common_ancestor func stmts ast_map ast_node_lst
    parent_of_patch =
  let parent_tups = mk_parent_tups_str [ func ] stmts ast_map in
  let init =
    List.find_exn ~f:(fun (p, _) -> String.equal p parent_of_patch) parent_tups
  in
  go_up parent_tups ast_node_lst init []

let search_eq_ast_rel ast_facts fa = Chc.find fa ast_facts

let mk_ast_bug_pattern ast_facts node_map solution =
  List.fold_left ~init:[]
    ~f:(fun acc (p, c) ->
      let p = Chc.Elt.FDNumeral ("AstNode-" ^ p) in
      let c = Chc.Elt.FDNumeral ("AstNode-" ^ c) in
      (Chc.Elt.FuncApply ("AstParent", [ p; c ]) |> search_eq_ast_rel ast_facts)
      :: acc)
    solution
  |> fun x ->
  List.fold_left ~init:x
    ~f:(fun acc (p, c) ->
      let p_cfg = Hashtbl.find_opt node_map p in
      let c_cfg = Hashtbl.find_opt node_map c in
      let p_ast = Chc.Elt.FDNumeral ("AstNode-" ^ p) in
      let c_ast = Chc.Elt.FDNumeral ("AstNode-" ^ c) in
      if Option.is_some p_cfg && Option.is_some c_cfg then
        (Chc.Elt.FuncApply
           ("EqNode", [ FDNumeral (Option.value_exn p_cfg); p_ast ])
        |> search_eq_ast_rel ast_facts)
        :: (Chc.Elt.FuncApply
              ("EqNode", [ FDNumeral (Option.value_exn c_cfg); c_ast ])
           |> search_eq_ast_rel ast_facts)
        :: acc
      else if Option.is_some p_cfg then
        (Chc.Elt.FuncApply
           ("EqNode", [ FDNumeral (Option.value_exn p_cfg); p_ast ])
        |> search_eq_ast_rel ast_facts)
        :: acc
      else if Option.is_some c_cfg then
        (Chc.Elt.FuncApply
           ("EqNode", [ FDNumeral (Option.value_exn c_cfg); c_ast ])
        |> search_eq_ast_rel ast_facts)
        :: acc
      else acc)
    solution

let find_eq_rel ast_facts patch_node =
  let patch_node = Chc.Elt.FDNumeral ("AstNode-" ^ patch_node) in
  let ast_fact_lst = Chc.to_list ast_facts in
  List.find
    ~f:(fun fact ->
      match fact with
      | Chc.Elt.FuncApply ("EqNode", [ _; p ]) ->
          if Chc.Elt.equal patch_node p then true else false
      | _ -> false)
    ast_fact_lst

let compute_ast_pattern ast_facts ast_node_lst parent_of_patch patch_func maps
    ast =
  let parent_in_pattern = find_eq_rel ast_facts parent_of_patch in
  if Option.is_some parent_in_pattern then
    [ Option.value_exn parent_in_pattern ]
  else (
    if String.equal patch_func "None" then
      failwith "compute_ast_pattern: no func";
    let ast_map = maps.Maps.ast_map in
    let node_map = maps.Maps.node_map |> Utils.reverse_hashtbl in
    L.info "Compute AST pattern...";
    let stmts = Utils.extract_target_func_stmt_lst ast patch_func in
    let func = Utils.extract_target_func ast patch_func in
    let solution =
      greedy_search_common_ancestor func stmts ast_map ast_node_lst
        parent_of_patch
    in
    mk_ast_bug_pattern ast_facts node_map solution)

let run du_facts ast_facts dug patch_comps src snk alarm_comps maps diff ast =
  let fst_abs_facts =
    abstract_by_comps du_facts dug patch_comps snk alarm_comps
  in
  let fact_lst = Chc.to_list fst_abs_facts in
  let ast_node_lst = Chc.extract_nodes_in_facts fact_lst maps.Maps.node_map in
  if List.length ast_node_lst = 0 then
    failwith "abstract_bug_pattern: no AST nodes corresponding CFG nodes found";
  let parents = AbsDiff.extract_parent diff maps.Maps.ast_map in
  let smallest_ast_patterns =
    List.fold ~init:[]
      ~f:(fun acc (parent, func) ->
        compute_ast_pattern ast_facts ast_node_lst parent func maps ast @ acc)
      parents
    |> Stdlib.List.sort_uniq Chc.Elt.compare
  in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  let pattern_in_numeral =
    Chc.Elt.Implies (fact_lst @ smallest_ast_patterns, errtrace)
  in
  ( pattern_in_numeral |> Chc.singleton,
    pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton )
