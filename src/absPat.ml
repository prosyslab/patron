open Core
module Set = Stdlib.Set
module Map = Stdlib.Map
module Hashtbl = Stdlib.Hashtbl
module L = Logger

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

let collect_ast_rels full_rels node leaf =
  let terms = Chc.Elt.numer node |> Chc.singleton in
  let n2l =
    Chc.fixedpoint (Chc.from_node_to_ast ~leaf) full_rels terms Chc.empty |> fst
  in
  let l2n =
    Chc.fixedpoint Chc.from_ast_to_node full_rels leaf Chc.empty |> fst
  in
  Chc.inter n2l l2n

let find_rels_by_lv full_rels dug cmd_map snk lv =
  let module NodeSet = Set.Make (String) in
  let lv_term = Chc.Elt.numer lv in
  let lv_terms = Chc.singleton lv_term in
  let def_skip_nodes, def_nodes =
    Hashtbl.find dug.Dug.def_map lv_term
    |> NodeSet.partition (Dug.is_skip_node cmd_map)
  in
  (* NOTE: hack for skip node (ENTRY, EXIT, ReturnNode, ...) *)
  if NodeSet.is_empty def_nodes then
    let node = NodeSet.choose def_skip_nodes in
    let succ =
      Hashtbl.find dug.Dug.use_map lv_term
      |> NodeSet.find_first (fun s -> Dug.mem_edge dug node s)
    in
    let ast_rels = collect_ast_rels full_rels succ lv_terms in
    Dug.shortest_path dug succ snk
    |> Dug.path2rels
    |> Chc.add (Chc.Elt.duedge node succ)
    |> Chc.union ast_rels
  else
    let collect_rels node rels_acc =
      let ast_rels = collect_ast_rels full_rels node lv_terms in
      Dug.fold_succ
        (fun succ path_rels ->
          if Hashtbl.find dug.label (node, succ) |> Chc.mem lv_term then
            Dug.shortest_path dug succ snk
            |> Dug.path2rels
            |> Chc.add (Chc.Elt.duedge node succ)
            |> Chc.union path_rels
          else path_rels)
        dug node rels_acc
      |> Chc.union ast_rels
    in
    NodeSet.fold collect_rels def_nodes Chc.empty

let abs_by_comps dug patch_comps snk alarm_comps cmd_map du_facts =
  L.info "patch_comps: %s" (String.concat ~sep:", " patch_comps);
  L.info "alarm_comps: %s"
    (alarm_comps |> Chc.to_list |> Chc.Elt.numers2strs
   |> String.concat ~sep:", ");
  let collected_by_patch_comps =
    List.fold_left
      ~f:(fun rels lv ->
        find_rels_by_lv du_facts dug cmd_map snk lv |> Chc.union rels)
      ~init:Chc.empty patch_comps
  in
  let collected_by_alarm_comps = collect_ast_rels du_facts snk alarm_comps in
  Chc.union collected_by_patch_comps collected_by_alarm_comps |> Chc.to_list

let abs_ast_rels maps du_fact_lst abs_diff ast ast_facts =
  let ast_node_lst =
    Chc.extract_nodes_in_facts du_fact_lst maps.Maps.node_map
  in
  if List.length ast_node_lst = 0 then
    failwith "abstract_bug_pattern: no AST nodes corresponding CFG nodes found";
  let parents = AbsDiff.extract_parent abs_diff maps.Maps.ast_map in
  List.fold ~init:[]
    ~f:(fun acc (parent, func) ->
      compute_ast_pattern ast_facts ast_node_lst parent func maps ast @ acc)
    parents
  |> Stdlib.List.sort_uniq Chc.Elt.compare

let run maps dug ast patch_comps alarm_comps src snk abs_diff du_facts ast_facts
    =
  let abs_du_facts =
    abs_by_comps dug patch_comps snk alarm_comps maps.Maps.cmd_map du_facts
  in
  let abs_ast_facts = abs_ast_rels maps abs_du_facts abs_diff ast ast_facts in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  let pattern_in_numeral =
    Chc.Elt.Implies (abs_du_facts @ abs_ast_facts, errtrace)
  in
  ( pattern_in_numeral |> Chc.singleton,
    pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton )
