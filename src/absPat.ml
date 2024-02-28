open Core
module Set = Stdlib.Set
module Map = Stdlib.Map
module Hashtbl = Stdlib.Hashtbl
module L = Logger

let collect_ast_rels dug node leaf =
  let node_info = Dug.info_of_v dug node in
  Chc.fixedpoint Chc.from_ast_to_node node_info.rels leaf Chc.empty |> fst

let find_rels_by_lv dug cmd_map snk lv =
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
    let ast_rels = collect_ast_rels dug succ lv_terms in
    Dug.shortest_path dug succ snk
    |> Dug.path2rels
    |> Chc.add (Chc.Elt.duedge node succ)
    |> Chc.union ast_rels
  else
    let collect_rels node rels_acc =
      let ast_rels = collect_ast_rels dug node lv_terms in
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

let abs_by_comps dug patch_comps snk alarm_exps alarm_lvs cmd_map =
  L.info "patch_comps: %s" (String.concat ~sep:", " patch_comps);
  L.info "alarm_exps: %s"
    (alarm_exps |> Chc.to_list |> Chc.Elt.numers2strs |> String.concat ~sep:", ");
  L.info "alarm_lvs: %s"
    (alarm_lvs |> Chc.to_list |> Chc.Elt.numers2strs |> String.concat ~sep:", ");
  (* TODO: use alarm_lvs and EvalLv for finding real DUPath from patch to sink *)
  let collected_by_patch_comps =
    List.fold_left
      ~f:(fun rels lv ->
        find_rels_by_lv dug cmd_map snk lv
        |> Chc.union rels
        |> Chc.add (Chc.Elt.real_lv lv))
      ~init:Chc.empty patch_comps
  in
  let collected_by_alarm_comps = collect_ast_rels dug snk alarm_exps in
  Chc.union collected_by_patch_comps collected_by_alarm_comps |> Chc.to_list

let run maps dug patch_comps alarm_exps alarm_lvs src snk =
  let abs_facts =
    abs_by_comps dug patch_comps snk alarm_exps alarm_lvs maps.Maps.cmd_map
  in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  let pattern_in_numeral = Chc.Elt.Implies (abs_facts, errtrace) in
  ( pattern_in_numeral |> Chc.singleton,
    pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton )
