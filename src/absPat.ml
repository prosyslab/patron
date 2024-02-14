open Core
module L = Logger

let rec fixedpoint rels terms deps =
  let deps', terms' =
    Chc.fold
      (fun c (deps, terms) ->
        let is_nec, terms' = Chc.road_to_node terms c in
        ((if is_nec then Chc.add c deps else deps), terms'))
      rels (deps, terms)
  in
  if Chc.subset deps' deps && Chc.subset terms' terms then (deps', terms')
  else fixedpoint rels terms' deps'

let abstract_by_comps chc dug patch_comps snk alarm_comps =
  L.info "patch_comps: %s" (String.concat ~sep:", " patch_comps);
  L.info "alarm_comps: %s"
    (alarm_comps |> Chc.to_list |> Chc.Elt.terms2strs |> String.concat ~sep:", ");
  let du_rels = Chc.filter Chc.Elt.is_duedge chc in
  let ast_rels = Chc.diff chc du_rels in
  let terms =
    List.map ~f:(fun s -> Chc.Elt.FDNumeral s) patch_comps
    |> Chc.of_list |> Chc.union alarm_comps
  in
  let abs_ast_rels, terms' = fixedpoint ast_rels terms Chc.empty in
  let nodes = Chc.to_list terms' |> Chc.Elt.terms2strs |> Chc.filter_by_node in
  L.info "nodes: %s" (String.concat ~sep:", " nodes);
  let dug = Dug.copy dug in
  let paths =
    List.fold_left
      ~f:(fun paths src -> Dug.shortest_path dug src snk :: paths)
      ~init:[] nodes
  in
  let abs_du_rels = Dug.paths2rels paths in
  Chc.union abs_ast_rels abs_du_rels
