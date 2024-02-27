open Core
module Set = Stdlib.Set
module Map = Stdlib.Map
module Hashtbl = Stdlib.Hashtbl
module L = Logger

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

let abs_by_comps dug patch_comps snk alarm_comps cmd_map facts =
  L.info "patch_comps: %s" (String.concat ~sep:", " patch_comps);
  L.info "alarm_comps: %s"
    (alarm_comps |> Chc.to_list |> Chc.Elt.numers2strs
   |> String.concat ~sep:", ");
  let collected_by_patch_comps =
    List.fold_left
      ~f:(fun rels lv ->
        find_rels_by_lv facts dug cmd_map snk lv
        |> Chc.union rels
        |> Chc.add (Chc.Elt.real_lv lv))
      ~init:Chc.empty patch_comps
  in
  let collected_by_alarm_comps = collect_ast_rels facts snk alarm_comps in
  Chc.union collected_by_patch_comps collected_by_alarm_comps |> Chc.to_list

let run maps dug patch_comps alarm_comps src snk facts =
  let abs_facts =
    abs_by_comps dug patch_comps snk alarm_comps maps.Maps.cmd_map facts
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
