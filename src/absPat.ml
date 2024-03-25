open Core
module Set = Stdlib.Set
module StrSet = Set.Make (String)
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
  (* TEMP: for more simple pattern *)
  Dug.shortest_path dug succ snk
  |> Dug.path2rels
  |> Chc.add (Chc.Elt.duedge node succ)

let find_rels_by_loc dug snk loc facts =
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
  (Dug.path2rels selected_path |> Chc.union ast_rels, node_sym)

let def_from_normal_node dug lv_term loc used_node node rels_acc =
  let terms = Chc.singleton loc in
  let ast_rels = collect_ast_rels dug node terms in
  let find_path_rels succ path_rels =
    if Hashtbl.find dug.label (node, succ) |> Chc.mem lv_term then
      let path = Dug.shortest_path dug succ used_node in
      Dug.path2rels path
      |> Chc.add (Chc.Elt.duedge node succ)
      |> Chc.union path_rels
    else path_rels
  in
  Dug.fold_succ find_path_rels dug node rels_acc |> Chc.union ast_rels

let def_from_normal_nodes dug lv_term loc used_node def_nodes =
  NodeSet.fold
    (def_from_normal_node dug lv_term loc used_node)
    def_nodes Chc.empty

let find_rels_by_lv dug cmd_map snk lv facts =
  let def_skip_nodes, def_nodes =
    Hashtbl.find dug.Dug.def_map lv
    |> NodeSet.partition (Dug.is_skip_node cmd_map)
  in
  (* NOTE: hack for skip node (ENTRY, EXIT, ReturnNode, ...) *)
  if NodeSet.is_empty def_nodes then
    (def_from_skip_nodes dug lv snk def_skip_nodes, def_skip_nodes)
  else
    let loc = Chc.find_loc lv facts in
    let loc_rels, used_node = find_rels_by_loc dug snk loc facts in
    ( def_from_normal_nodes dug lv loc used_node def_nodes |> Chc.union loc_rels,
      def_nodes )

let log_lv maps lv =
  Hashtbl.find maps.Maps.ast_map lv
  |> Ast.to_lval |> Ast.s_lv |> F.sprintf "%s (%s)" lv

module FunLvMap = Map.Make (String)
module AltMap = Map.Make (Chc.Elt)

let find_alt_lv facts lv =
  let loc = Chc.find_loc lv facts in
  let fl_map = Chc.find_f_lv loc facts in
  FunLvMap.fold
    (fun func_name lvs fl ->
      let new_lvs =
        Chc.fold
          (fun lv lvs' ->
            let cps = Chc.find_copy_lvs lv facts in
            if Chc.is_empty cps then lvs'
              (* NOTE: if there is copied lv, then remove orig lv *)
            else Chc.union lvs' cps |> Chc.remove lv)
          lvs lvs
      in
      FunLvMap.add func_name new_lvs fl)
    fl_map fl_map

let funcs fl = FunLvMap.bindings fl |> List.map ~f:fst |> StrSet.of_list

let find_common_func alt_map =
  AltMap.fold
    (fun _ fl (cfs, first) ->
      let fs = funcs fl in
      if first then (fs, false) else (StrSet.inter cfs fs, first))
    alt_map (StrSet.empty, true)
  |> fst

let patch_comps2str maps patch_comps =
  Chc.fold
    (fun c s -> s ^ (Chc.Elt.to_sym c |> log_lv maps) ^ ", ")
    patch_comps ""

let terms2str terms =
  terms |> Chc.to_list |> Chc.Elt.numers2strs |> String.concat ~sep:", "

let find_alt_lvs snk_func facts patch_lvs abs_diff =
  let alt_map =
    Chc.fold
      (fun lv lfl ->
        let fl = find_alt_lv facts lv in
        AltMap.add lv fl lfl)
      patch_lvs AltMap.empty
  in
  let common_func = find_common_func alt_map in
  (* TEMP: use alt lvs only they are in same function with sink point *)
  if StrSet.mem snk_func common_func then
    (* TEMP: choose one arbitrary lv from candidates *)
    AltMap.fold
      (fun orig_lv fl (new_pc, new_ad) ->
        let new_lv = FunLvMap.find snk_func fl |> Chc.choose in
        let o_lv = Chc.Elt.to_sym orig_lv in
        let n_lv = Chc.Elt.to_sym new_lv in
        (Chc.add new_lv new_pc, AbsDiff.subst_abs_diff o_lv n_lv new_ad))
      alt_map (Chc.empty, abs_diff)
  else (Chc.empty, abs_diff)

let abs_by_comps ?(new_ad = false) maps dug patch_comps snk alarm_exps alarm_lvs
    facts abs_diff =
  patch_comps2str maps patch_comps |> L.info "patch_comps: %s";
  terms2str alarm_exps |> L.info "alarm_exps: %s";
  terms2str alarm_lvs |> L.info "alarm_lvs: %s";
  if Chc.equal patch_comps alarm_lvs then
    ( collect_ast_rels dug snk alarm_lvs,
      if new_ad then AbsDiff.change_use (StrSet.singleton snk) abs_diff
      else abs_diff )
  else
    let collected_by_patch_comps, defs =
      Chc.fold
        (fun lv (rels, defs) ->
          let path_rels, new_defs =
            find_rels_by_lv dug maps.Maps.cmd_map snk lv facts
          in
          (Chc.union path_rels rels, NodeSet.union defs new_defs))
        patch_comps (Chc.empty, NodeSet.empty)
    in
    let collected_by_alarm_comps = collect_ast_rels dug snk alarm_exps in
    let abs_diff' =
      AbsDiff.change_def defs abs_diff
      |> AbsDiff.change_use (StrSet.singleton snk)
    in
    ( Chc.union collected_by_patch_comps collected_by_alarm_comps,
      if new_ad then abs_diff' else abs_diff )

let run maps dug patch_comps alarm_exps alarm_lvs src snk facts abs_diff =
  let abs_facts, abs_diff' =
    abs_by_comps maps dug patch_comps snk alarm_exps alarm_lvs facts abs_diff
  in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  let pattern_in_numeral =
    Chc.Elt.Implies (abs_facts |> Chc.to_list, errtrace)
  in
  let snk_func = Utils.get_func_name_from_node snk in
  let alt_pc, alt_diff = find_alt_lvs snk_func facts patch_comps abs_diff in
  let alt_pat =
    if Chc.is_empty alt_pc then []
    else
      let alt_facts, alt_diff' =
        abs_by_comps ~new_ad:true maps dug alt_pc snk alarm_exps alarm_lvs facts
          alt_diff
      in
      let alt_pattern_in_numeral =
        Chc.Elt.Implies (alt_facts |> Chc.to_list, errtrace)
      in
      [
        ( alt_pattern_in_numeral |> Chc.singleton,
          alt_pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
          alt_diff' );
      ]
  in
  ( pattern_in_numeral |> Chc.singleton,
    pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
    abs_diff' )
  :: alt_pat
