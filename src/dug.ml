open Core
module L = Logger
module F = Format
module V = String
module G = Graph.Imperative.Digraph.ConcreteBidirectional (String)

module W = struct
  type edge = G.E.t
  type t = int

  let weight _ = 1
  let compare = Stdlib.compare
  let add = ( + )
  let zero = 0
end

module Dijkstra = Graph.Path.Dijkstra (G) (W)
module Check = Graph.Path.Check (G)

type t = G.t
type path_checker = Check.path_checker

let create ~size () = G.create ~size ()
let copy = G.copy
let clear = G.clear
let mem_vertex = G.mem_vertex
let fold_vertex = G.fold_vertex

let add_edge s d g =
  G.add_edge g s d;
  g

let rec delete_last_edge dst edges =
  match List.rev edges with
  | [] -> []
  | h :: t ->
      let dst' = G.E.dst h in
      if String.equal dst dst' then List.rev t else failwith "delete_last_edge"

let rec delete_first_edge src edges =
  match edges with
  | [] -> []
  | h :: t ->
      let src' = G.E.src h in
      if String.equal src src' then t else failwith "delete_first_edge"

let shortest_path g src dst = Dijkstra.shortest_path g src dst |> fst

let edges2lst edge_lst =
  List.fold_left
    ~f:(fun l edge ->
      let src, dst = (G.E.src edge, G.E.dst edge) in
      match l with [] -> [ dst; src ] | _ -> dst :: l)
    ~init:[] edge_lst
  |> List.rev

let create_path_checker = Check.create
let check_path pc src dst = Check.check_path pc src dst
