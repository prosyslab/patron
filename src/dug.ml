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

let add_edge s d g =
  G.add_edge g s d;
  g

let shortest_path g src dst = Dijkstra.shortest_path g src dst |> fst
(* |> List.fold_left
     ~f:(fun l edge ->
       let src, dst = (G.E.src edge, G.E.dst edge) in
       match l with [] -> [ dst; src ] | _ -> dst :: l)
     ~init:[] *)

let create_path_checker = Check.create
let check_path pc src dst = Check.check_path pc src dst
