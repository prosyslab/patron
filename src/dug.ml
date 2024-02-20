open Core
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module L = Logger
module F = Format
module V = String
module I = Graph.Imperative.Digraph.ConcreteBidirectional (String)

module W = struct
  type edge = I.E.t
  type t = int

  let weight _ = 1
  let compare = Stdlib.compare
  let add = ( + )
  let zero = 0
end

module Dijkstra = Graph.Path.Dijkstra (I) (W)
module Check = Graph.Path.Check (I)
module LvalMap = Map.Make (String)

type node_info = { rels : Chc.t; defs : Chc.t; uses : Chc.t }

type t = {
  graph : I.t;
  node_info : (string, node_info) Hashtbl.t; (* Node -> (Rels, Defs, Uses) *)
  label : (string * string, Chc.t) Hashtbl.t; (* Edge -> (FDNumeral Lval) Set *)
  lvmap_per_func : (string, string LvalMap.t) Hashtbl.t;
}

type path_checker = Check.path_checker

let create ~size () =
  {
    graph = I.create ~size ();
    node_info = Hashtbl.create size;
    label = Hashtbl.create (size * size);
    lvmap_per_func = Hashtbl.create size;
  }

let copy g =
  {
    graph = I.copy g.graph;
    node_info = Hashtbl.copy g.node_info;
    label = Hashtbl.copy g.label;
    lvmap_per_func = Hashtbl.copy g.lvmap_per_func;
  }

let clear g =
  I.clear g.graph;
  Hashtbl.clear g.node_info;
  Hashtbl.clear g.label;
  Hashtbl.clear g.lvmap_per_func

let mem_vertex g n = I.mem_vertex g.graph n
let fold_vertex f g a = I.fold_vertex f g.graph a
let info_of_v g v = Hashtbl.find g.node_info v

let add_vertex (v, rels, defs, uses) g =
  Hashtbl.replace g.node_info v { rels; defs; uses };
  I.add_vertex g.graph v;
  g

let add_edge_e (s, lval_set, d) g =
  Hashtbl.replace g.label (s, d) lval_set;
  I.add_edge g.graph s d;
  g

let add_edge s d = add_edge_e (s, Chc.empty, d)

let delete_last_edge dst edges =
  match List.rev edges with
  | [] -> []
  | h :: t ->
      let dst' = I.E.dst h in
      if String.equal dst dst' then List.rev t else failwith "delete_last_edge"

let delete_first_edge src edges =
  match edges with
  | [] -> []
  | h :: t ->
      let src' = I.E.src h in
      if String.equal src src' then t else failwith "delete_first_edge"

let shortest_path g src dst = Dijkstra.shortest_path g.graph src dst |> fst

let edges2lst edge_lst =
  List.fold_left
    ~f:(fun l edge ->
      let src, dst = (I.E.src edge, I.E.dst edge) in
      match l with [] -> [ dst; src ] | _ -> dst :: l)
    ~init:[] edge_lst
  |> List.rev

let create_path_checker = Check.create
let check_path pc src dst = Check.check_path pc src dst

let paths2rels =
  List.fold_left
    ~f:(fun rels path ->
      List.fold_left
        ~f:(fun rels edge ->
          Chc.add (Chc.Elt.duedge (I.E.src edge) (I.E.dst edge)) rels)
        ~init:rels path)
    ~init:Chc.empty

let mapping_func_lvmap lval_map v lvs g =
  let lvm =
    List.fold_left
      ~f:(fun lvm lv -> LvalMap.add (Hashtbl.find lval_map lv) lv lvm)
      ~init:LvalMap.empty lvs
  in
  let func_name = String.split ~on:'-' v |> List.hd_exn in
  if Hashtbl.mem g.lvmap_per_func func_name then
    let orig_lvmap = Hashtbl.find g.lvmap_per_func func_name in
    LvalMap.union
      (fun _ a_sym b_sym ->
        if String.equal a_sym b_sym |> not then
          L.warn "There are two symbols of same lv in one func";
        Some a_sym)
      orig_lvmap lvm
    |> Hashtbl.replace g.lvmap_per_func func_name
  else Hashtbl.replace g.lvmap_per_func func_name lvm;
  g

let process_vertex lval_map v r g =
  if mem_vertex g v then (info_of_v g v, g)
  else
    let terms = Chc.Elt.numer v |> Chc.singleton in
    let reach = Chc.fixedpoint Chc.from_node_to_ast r terms Chc.empty |> fst in
    let defs = Chc.find_defs reach in
    let uses = Chc.find_uses reach in
    let g' = add_vertex (v, reach, defs, uses) g in
    let lvs = Chc.union defs uses |> Chc.to_list |> Chc.Elt.numers2strs in
    let g'' = mapping_func_lvmap lval_map v lvs g' in
    (info_of_v g'' v, g'')

let of_facts lval_map rels =
  let module NodeSet = Set.Make (String) in
  let du_rels, ast_rels = Chc.partition Chc.Elt.is_duedge rels in
  let nodes =
    Chc.fold
      (fun rel ns ->
        let src, dst = Chc.Elt.extract_src_dst rel in
        ns |> NodeSet.add src |> NodeSet.add dst)
      du_rels NodeSet.empty
  in
  let dug = create ~size:(NodeSet.cardinal nodes) () in
  Chc.fold
    (fun rel g ->
      let src, dst = Chc.Elt.extract_src_dst rel in
      let src_info, g' = process_vertex lval_map src ast_rels g in
      let dst_info, g'' = process_vertex lval_map dst ast_rels g' in
      let lvs =
        if Chc.is_empty src_info.defs then dst_info.uses
        else if Chc.is_empty dst_info.uses then src_info.defs
        else Chc.inter src_info.defs dst_info.uses
      in
      add_edge_e (src, lvs, dst) g'')
    du_rels dug
