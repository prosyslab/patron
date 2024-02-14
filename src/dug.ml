open Core
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
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

type node_info = { rels : Chc.t; defs : Chc.t; uses : Chc.t }

type t = {
  graph : I.t;
  node_info : (string, node_info) Hashtbl.t; (* Node -> (Rels, Defs, Uses) *)
  label : (string * string, Chc.t) Hashtbl.t; (* Edge -> (FDNumeral Lval) Set *)
}

type path_checker = Check.path_checker

let create ~size () =
  {
    graph = I.create ~size ();
    node_info = Hashtbl.create size;
    label = Hashtbl.create (size * size);
  }

let copy g =
  {
    graph = I.copy g.graph;
    node_info = Hashtbl.copy g.node_info;
    label = Hashtbl.copy g.label;
  }

let clear g =
  I.clear g.graph;
  Hashtbl.clear g.node_info;
  Hashtbl.clear g.label

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

let process_vertex g v r =
  if mem_vertex g v then (info_of_v g v, g)
  else
    let terms = Chc.Elt.numer v |> Chc.singleton in
    let reach =
      Chc.fixedpoint (Chc.prop_deps ~ignore_duedge:true) r terms Chc.empty
      |> fst
    in
    let defs = Chc.find_defs reach in
    let uses = Chc.find_uses reach in
    let g' = add_vertex (v, reach, defs, uses) g in
    (info_of_v g' v, g')

let of_facts rels =
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
      let src_info, g' = process_vertex g src ast_rels in
      let dst_info, g'' = process_vertex g' dst ast_rels in
      let lvs =
        if Chc.is_empty src_info.defs then dst_info.uses
        else if Chc.is_empty dst_info.uses then src_info.defs
        else Chc.inter src_info.defs dst_info.uses
      in
      add_edge_e (src, lvs, dst) g'')
    du_rels dug
