open Core
module Set = Stdlib.Set
module Map = Stdlib.Map
module Hashtbl = Stdlib.Hashtbl
module L = Logger
module F = Format
module NodeSet = Set.Make (String)

let collect_ast_rels dug node leaf =
  let node_info = Dug.info_of_v dug node in
  Chc.fixedpoint Chc.from_ast_to_node node_info.Dug.rels leaf Chc.empty |> fst

let def_from_skip_nodes dug lv_term snk def_skip_nodes =
  let node = NodeSet.choose def_skip_nodes in
  let succ =
    Hashtbl.find dug.Dug.use_map lv_term
    |> NodeSet.find_first (fun s -> Dug.mem_edge dug node s)
  in
  let lv_terms = Chc.singleton lv_term in
  let ast_rels = collect_ast_rels dug succ lv_terms in
  Dug.shortest_path dug succ snk
  |> Dug.path2rels
  |> Chc.add (Chc.Elt.duedge node succ)
  |> Chc.union ast_rels

let find_rels_by_loc dug snk loc facts =
  L.info "find_rels_by_loc - loc:\n%a" Chc.Elt.pp loc;
  let cand_nodes = Chc.find_evallv_nodes loc facts in
  let n_path n np =
    let path = Dug.shortest_path dug (Chc.Elt.to_sym n) snk in
    (n, path) :: np
  in
  let compare (_, p1) (_, p2) = Int.compare (List.length p1) (List.length p2) in
  let selected_node, selected_path =
    Chc.fold n_path cand_nodes [] |> List.min_elt ~compare |> Option.value_exn
  in
  let locs = Chc.singleton loc in
  let node_sym = Chc.Elt.to_sym selected_node in
  let ast_rels = collect_ast_rels dug node_sym locs in
  L.info "find_rels_by_loc - path: %s"
    (Dug.path2lst selected_path |> String.concat ~sep:", ");
  (Dug.path2rels selected_path |> Chc.union ast_rels, node_sym)

let def_from_normal_node dug lv_term loc used_node node rels_acc =
  L.info "def_from_normal_node - lv: %s" (Chc.Elt.to_sym lv_term);
  let terms = Chc.singleton loc in
  let ast_rels = collect_ast_rels dug node terms in
  let find_path_rels succ path_rels =
    if Hashtbl.find dug.label (node, succ) |> Chc.mem lv_term then (
      let path = Dug.shortest_path dug succ used_node in
      L.info "def_from_normal_node - path: %s"
        (Dug.path2lst path |> List.cons node |> String.concat ~sep:", ");
      Dug.path2rels path
      |> Chc.add (Chc.Elt.duedge node succ)
      |> Chc.union path_rels)
    else path_rels
  in
  Dug.fold_succ find_path_rels dug node rels_acc |> Chc.union ast_rels

let def_from_normal_nodes dug lv_term loc used_node def_nodes =
  NodeSet.fold
    (def_from_normal_node dug lv_term loc used_node)
    def_nodes Chc.empty

let find_rels_by_lv dug cmd_map snk lv facts =
  let lv_term = Chc.Elt.numer lv in
  let def_skip_nodes, def_nodes =
    Hashtbl.find dug.Dug.def_map lv_term
    |> NodeSet.partition (Dug.is_skip_node cmd_map)
  in
  (* NOTE: hack for skip node (ENTRY, EXIT, ReturnNode, ...) *)
  if NodeSet.is_empty def_nodes then
    def_from_skip_nodes dug lv_term snk def_skip_nodes
  else
    let loc = Chc.find_loc lv_term facts in
    let loc_rels, used_node = find_rels_by_loc dug snk loc facts in
    def_from_normal_nodes dug lv_term loc used_node def_nodes
    |> Chc.union loc_rels

let is_lv comp = String.split ~on:'-' comp |> List.hd_exn |> String.equal "Lval"

let abs_by_comps maps dug patch_comps snk alarm_exps alarm_lvs facts =
  L.info "patch_comps: %s"
    (List.map
       ~f:(fun c ->
         if is_lv c then
           F.sprintf "%s (%s)" c
             (Hashtbl.find maps.Maps.ast_map c |> Ast.to_lval |> Ast.s_lv)
         else c)
       patch_comps
    |> String.concat ~sep:", ");
  L.info "alarm_exps: %s"
    (alarm_exps |> Chc.to_list |> Chc.Elt.numers2strs |> String.concat ~sep:", ");
  L.info "alarm_lvs: %s"
    (alarm_lvs |> Chc.to_list |> Chc.Elt.numers2strs |> String.concat ~sep:", ");
  (* TODO: use alarm_lvs and EvalLv for finding real DUPath from patch to sink *)
  let collected_by_patch_comps =
    List.fold_left
      ~f:(fun rels comp ->
        if is_lv comp then
          find_rels_by_lv dug maps.Maps.cmd_map snk comp facts |> Chc.union rels
        else rels (* TODO: use dug node as patch comps *))
      ~init:Chc.empty patch_comps
  in
  let collected_by_alarm_comps = collect_ast_rels dug snk alarm_exps in
  Chc.union collected_by_patch_comps collected_by_alarm_comps |> Chc.to_list

let run maps dug patch_comps alarm_exps alarm_lvs src snk facts =
  let abs_facts =
    abs_by_comps maps dug patch_comps snk alarm_exps alarm_lvs facts
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
