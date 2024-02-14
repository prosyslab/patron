open Core
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
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

type t = {
  graph : I.t;
  rels_of_node : (string, Chc.t) Hashtbl.t; (* Node -> Rels *)
  label : (string * string, Chc.t) Hashtbl.t; (* Edge -> (FDNumeral Lval) Set *)
}

type path_checker = Check.path_checker

let create ~size () =
  {
    graph = I.create ~size ();
    rels_of_node = Hashtbl.create size;
    label = Hashtbl.create (size * size);
  }

let copy g =
  {
    graph = I.copy g.graph;
    rels_of_node = Hashtbl.copy g.rels_of_node;
    label = Hashtbl.copy g.label;
  }

let clear g =
  I.clear g.graph;
  Hashtbl.clear g.rels_of_node;
  Hashtbl.clear g.label

let mem_vertex g n = I.mem_vertex g.graph n
let fold_vertex f g a = I.fold_vertex f g.graph a

let add_edge_e (s, lval_set, d) g =
  Hashtbl.replace g.label (s, d) lval_set;
  I.add_edge g.graph s d;
  g

let add_edge s d = add_edge_e (s, Chc.empty, d)

let rec delete_last_edge dst edges =
  match List.rev edges with
  | [] -> []
  | h :: t ->
      let dst' = I.E.dst h in
      if String.equal dst dst' then List.rev t else failwith "delete_last_edge"

let rec delete_first_edge src edges =
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

let mk_duedge edge =
  Chc.Elt.FuncApply
    ( "DUEdge",
      [ Chc.Elt.FDNumeral (I.E.src edge); Chc.Elt.FDNumeral (I.E.dst edge) ] )

let paths2rels =
  List.fold_left
    ~f:(fun rels path ->
      List.fold_left
        ~f:(fun rels edge -> Chc.add (mk_duedge edge) rels)
        ~init:rels path)
    ~init:Chc.empty

let of_fact rels =
  let module NodeSet = Set.Make (String) in
  let du_rels = Chc.filter Chc.Elt.is_duedge rels in
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
      add_edge src dst g)
    du_rels dug
