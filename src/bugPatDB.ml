open Core
open Z3env
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module Sys = Stdlib.Sys

let rec fixedpoint rels terms deps =
  let deps', terms' =
    Chc.fold
      (fun c (deps, terms) ->
        let is_nec, terms' = Chc.prop_deps terms c in
        ((if is_nec then Chc.add c deps else deps), terms'))
      rels (deps, terms)
  in
  if Chc.subset deps' deps && Chc.subset terms' terms then (deps', terms')
  else fixedpoint rels terms' deps'

let remove_before_src_after_snk src snk rels =
  let src_node, snk_node = (Chc.Elt.FDNumeral src, Chc.Elt.FDNumeral snk) in
  let before_src = Chc.collect_node ~before:true src_node rels in
  let after_snk = Chc.collect_node ~before:false snk_node rels in
  let before_deps = fixedpoint rels before_src Chc.empty |> fst in
  let after_deps = fixedpoint rels after_snk Chc.empty |> fst in
  rels |> (Fun.flip Chc.diff) before_deps |> (Fun.flip Chc.diff) after_deps

let collect_deps src snk aexps chc =
  let func_apps =
    Chc.extract_func_apps chc |> remove_before_src_after_snk src snk
  in
  let snk_term = Chc.Elt.FDNumeral snk in
  let terms = Chc.add snk_term aexps in
  fixedpoint func_apps terms Chc.empty
  |> fst
  |> Chc.filter (fun dep ->
         (Chc.Elt.is_duedge dep || Chc.Elt.is_assume dep) |> not)
  |> Chc.inter chc

let sort_rule_optimize ref deps =
  let get_args = function
    | Chc.Elt.FuncApply (s, args) -> (s, args)
    | _ -> failwith "not implemented"
  in
  let hv_common_elt rel1 rel2 =
    let name1, args1 = get_args rel1 in
    let _, args2 = get_args rel2 in
    let eq_elt arg1 arg2 =
      Chc.Elt.equal arg1 arg2
      && (not (String.equal name1 "BinOP"))
      && not (String.equal name1 "UnOP")
    in
    List.exists
      ~f:(fun arg1 -> List.exists ~f:(fun arg2 -> eq_elt arg1 arg2) args2)
      args1
  in
  let init =
    List.filter ~f:(fun dep -> hv_common_elt ref dep) deps |> List.hd_exn
  in
  let deps = List.filter ~f:(fun dep -> not (Chc.Elt.equal init dep)) deps in
  let rec mk_lcs_list record1 lst record2 acc cand out =
    match lst with
    | [] ->
        if List.length record2 = 0 then out
        else
          let prev = List.hd_exn cand in
          let cand' = List.tl_exn cand in
          let prev_rec = List.hd_exn record2 in
          let record = List.tl_exn record2 in
          let snapshot = List.tl_exn record1 in
          mk_lcs_list snapshot prev_rec record prev cand' (acc :: out)
    | hd :: tl ->
        let last = List.hd_exn acc in
        if hv_common_elt hd last then
          let new_deps = List.hd_exn record1 in
          let new_lst =
            List.filter ~f:(fun dep -> not (Chc.Elt.equal dep hd)) new_deps
          in
          let record1 =
            if List.hd_exn record1 |> List.length = List.length new_lst then
              record1
            else new_lst :: record1
          in
          mk_lcs_list record1 new_lst (tl :: record2) (hd :: acc) (acc :: cand)
            out
        else mk_lcs_list record1 tl record2 acc cand out
  in
  let _, lcs =
    mk_lcs_list [ deps ] deps [] [ init ] [] []
    |> List.fold_left ~init:(0, []) ~f:(fun (len, acc) lst ->
           if List.length lst > len then (List.length lst, lst) else (len, acc))
  in
  let unsorted =
    List.filter
      ~f:(fun dep ->
        not (List.mem lcs ~equal:(fun x y -> Chc.Elt.equal x y) dep))
      deps
  in
  (lcs |> List.rev) @ (unsorted |> List.rev)

let collect_nodes deps node_map =
  List.fold_left ~init:[]
    ~f:(fun acc dep ->
      match dep with
      (* TODO: case where nodes are used but not by Set *)
      | Chc.Elt.FuncApply ("Set", args) -> List.hd_exn args :: acc
      | _ -> acc)
    deps
  |> List.fold_left ~init:[] ~f:(fun acc node ->
         match node with
         | Chc.Elt.FDNumeral n -> (
             try Hashtbl.find node_map n :: acc with _ -> acc)
         | _ -> acc)

let extract_parent diff ast_map =
  let patch_node = diff.SymDiff.SDiff.patch_node.node in
  let func_name = diff.SymDiff.SDiff.func_name in
  match patch_node with
  | SymDiff.SElement.SGlob _ -> ("", func_name)
  | SymDiff.SElement.SStmt (_, s) ->
      (Hashtbl.find ast_map s |> string_of_int, func_name)
  | _ -> failwith "parent not found"

let compute_ast_pattern ast_node_lst patch_node patch_func ast_map ast =
  let stmts = Utils.extract_target_func_stmt_lst ast patch_func in
  let parent_tups =
    List.fold_left ~init:[]
      ~f:(fun acc s ->
        match s.Cil.skind with
        | Cil.Block b | Cil.Loop (b, _, _, _) ->
            Parser.mk_parent_tuples s b.bstmts @ acc
        | Cil.If (_, tb, eb, _) ->
            Parser.mk_parent_tuples s tb.bstmts
            @ Parser.mk_parent_tuples s eb.bstmts
            @ acc
        | _ -> acc)
      stmts
    |> List.fold_left ~init:[] ~f:(fun acc (p, c) ->
           ( Hashtbl.find ast_map p |> string_of_int,
             Hashtbl.find ast_map c |> string_of_int )
           :: acc)
  in
  let start =
    List.find_exn ~f:(fun (_, c) -> String.equal c patch_node) parent_tups
  in
  let rec go_up (p, c) acc =
    let rec go_down candidates acc =
      let rec aux (p, c) acc =
        let candidates =
          List.fold_left ~init:[]
            ~f:(fun acc' (p', c') ->
              if String.equal c p' then (p', c') :: acc' else acc')
            parent_tups
        in
        if List.length candidates = 0 then []
        else
          let is_found =
            List.exists
              ~f:(fun (_, c') ->
                List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
              candidates
          in
          if is_found then
            List.find_exn
              ~f:(fun (_, c') ->
                List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
              candidates
            :: acc
          else go_down candidates ((p, c) :: acc)
      in
      List.fold_left ~init:[]
        ~f:(fun acc' edge -> aux edge (edge :: acc) @ acc')
        candidates
    in
    let candidates =
      List.fold_left ~init:[]
        ~f:(fun acc' (p', c') ->
          if String.equal p p' then (p', c') :: acc' else acc')
        parent_tups
    in
    let up_opt = List.find ~f:(fun (_, c') -> String.equal p c') acc in
    let up =
      if Option.is_none up_opt then failwith "common ancestor not found"
      else Option.value_exn up_opt
    in
    if List.length candidates = 0 then go_up up (up :: acc)
    else
      let is_found =
        List.exists
          ~f:(fun (_, c') ->
            List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
          candidates
      in
      if is_found then
        List.find_exn
          ~f:(fun (_, c') ->
            List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
          candidates
        :: acc
      else
        let down = go_down candidates [] in
        if List.length down = 0 then go_up up (up :: acc) else acc @ down
  in
  let solution = go_up start [ start ] in
  List.fold_left ~init:Chc.empty
    ~f:(fun acc (p, c) ->
      let p = Chc.Elt.Var ("AstNode-" ^ p) in
      let c = Chc.Elt.Var ("AstNode-" ^ c) in
      Chc.add (Chc.Elt.FuncApply ("AstParent", [ p; c ])) acc)
    solution

let abstract_bug_pattern buggy src snk aexps maps diffs ast =
  let node_map = maps.Maps.node_map in
  let ast_map = maps.Maps.ast_map in
  let ctx =
    List.fold_left ~init:[]
      ~f:(fun acc diff -> SymDiff.SDiff.extract_context diff :: acc)
      diffs
    |> List.hd_exn
  in
  let deps = collect_deps src snk aexps buggy |> Chc.to_list in
  (* let ast_node_lst = collect_nodes deps node_map in
     let patch_node, patch_func = extract_parent ctx ast_map in
     let smallest_ast_pattern =
       if String.equal patch_node "" then
         failwith "not implemented for direct patch below the function"
       else compute_ast_pattern ast_node_lst patch_node patch_func ast_map ast
     in *)
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.src := src;
  Z3env.snk := snk;
  (* let deps = sort_rule_optimize errtrace deps in *)
  let errtrace_rule = Chc.Elt.Implies (deps, errtrace) |> Chc.Elt.numer2var in
  (* let error_cons = Chc.Elt.numer2var alarm in
     let err_rel = Chc.Elt.get_head error_cons in *)
  let bug_rule =
    Chc.Elt.Implies ([ errtrace (*; err_rel*) ], Chc.Elt.FuncApply ("Bug", []))
  in
  Chc.of_list [ errtrace_rule; (*error_cons;*) bug_rule ]
(* |> Chc.union smallest_ast_pattern *)

let parse_ast dir i_opt =
  Parser.parse_ast dir |> fun f ->
  if List.length i_opt <> 0 then Inline.perform i_opt f else f

let match_bug_for_one_prj pattern buggy_dir target_alarm ast cfg out_dir =
  let maps = Maps.create_maps () in
  Maps.reset_maps maps;
  try
    let facts, _ =
      Parser.make_facts buggy_dir target_alarm ast cfg out_dir maps
    in
    reset_env ();
    L.info "Try matching with %s..." target_alarm;
    Chc.match_and_log out_dir target_alarm maps facts pattern;
    Maps.dump target_alarm maps out_dir;
    L.info "match_bug_for_one_prj: %s is done" target_alarm
  with Parser.Not_impl_aexp -> L.info "PASS"

let run (i_opt, w_opt) target_alarm buggy_dir patch_dir out_dir =
  let buggy_maps = Maps.create_maps () in
  Maps.reset_maps buggy_maps;
  let buggy_ast = parse_ast buggy_dir i_opt in
  let patch_ast = parse_ast patch_dir i_opt in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff buggy_ast patch_ast in
  let buggy_cfg =
    Utils.parse_node_json (Filename.concat buggy_dir "sparrow-out")
  in
  L.info "Make Facts in buggy done";
  let buggy_facts, (src, snk, aexps) =
    Parser.make_facts buggy_dir target_alarm buggy_ast buggy_cfg out_dir
      buggy_maps
  in
  L.info "Mapping CFG Elements to AST nodes...";
  let sym_diff = SymDiff.define_sym_diff buggy_maps buggy_ast ast_diff in
  if w_opt then (
    L.info "Writing out the edit script...";
    SymDiff.to_json sym_diff ast_diff out_dir);
  let pattern =
    abstract_bug_pattern buggy_facts src snk aexps buggy_maps sym_diff buggy_ast
  in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern") pattern;
  reset_env ();
  L.info "Try matching with buggy...";
  Chc.match_and_log out_dir "buggy" buggy_maps buggy_facts pattern;
  Maps.dump "buggy" buggy_maps out_dir;
  Sys.readdir (Filename.concat buggy_dir "sparrow-out/taint/datalog")
  |> Array.iter ~f:(fun ta ->
         if
           (not (String.equal target_alarm ta))
           && Sys.is_directory
                (Filename.concat buggy_dir ("sparrow-out/taint/datalog/" ^ ta))
         then
           match_bug_for_one_prj pattern buggy_dir ta buggy_ast buggy_cfg
             out_dir);
  L.info "Done."
