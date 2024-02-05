open Core
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module Sys = Stdlib.Sys

let get_func str = String.split_on_chars ~on:[ '-' ] str |> List.hd_exn
let get_id str = String.split_on_chars ~on:[ '-' ] str |> List.last_exn

let extract_id elt =
  List.fold_left ~init:[]
    ~f:(fun acc e ->
      match e with
      | Chc.Elt.FDNumeral s | Chc.Elt.Var s -> get_id s :: acc
      | _ -> acc)
    elt

let extract_func elt =
  List.fold_left ~init:[]
    ~f:(fun acc e ->
      match e with
      | Chc.Elt.FDNumeral s | Chc.Elt.Var s -> get_func s :: acc
      | _ -> acc)
    elt

let extract_funcs_from_facts facts =
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply (_, elt) -> extract_func elt @ acc
      | _ -> acc)
    facts []
  |> List.dedup_and_sort ~compare:String.compare

let reduce_ast_facts maps ast facts =
  let func_lst = extract_funcs_from_facts facts in
  let interesting_stmts =
    List.fold ~init:[]
      ~f:(fun acc f ->
        (Utils.extract_target_func_stmt_lst ast f
        |> List.map ~f:(fun s -> Ast.stmt2ast (Some s)))
        @ acc)
      func_lst
    |> List.fold ~init:[] ~f:(fun acc s ->
           try (Hashtbl.find maps.Maps.ast_map s |> string_of_int) :: acc
           with _ -> acc)
  in
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply ("AstParent", elt) ->
          let nodes = [ List.hd_exn elt; List.last_exn elt ] |> extract_id in
          List.fold_left ~init:Chc.empty
            ~f:(fun acc' node ->
              if List.exists ~f:(fun n -> String.equal n node) interesting_stmts
              then Chc.add c acc'
              else acc')
            nodes
          |> Chc.union acc
      | Chc.Elt.FuncApply ("EqNode", elt) ->
          let (func : string) =
            [ List.hd_exn elt ] |> extract_func |> List.hd_exn
          in
          if List.exists ~f:(fun y -> String.equal func y) func_lst then
            Chc.add c acc
          else acc
      | _ -> acc)
    facts Chc.empty

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

let collect_deps maps ast src snk aexps cf_chc ast_chc =
  let func_apps =
    Chc.extract_func_apps cf_chc |> remove_before_src_after_snk src snk
  in
  let snk_term = Chc.Elt.FDNumeral snk in
  let terms = Chc.add snk_term aexps in
  let reduced_cf_facts =
    fixedpoint func_apps terms Chc.empty
    |> fst
    |> Chc.filter (fun dep ->
           (Chc.Elt.is_duedge dep || Chc.Elt.is_assume dep) |> not)
    |> Chc.inter cf_chc
  in
  let reduced_ast_facts = reduce_ast_facts maps ast ast_chc in
  (reduced_cf_facts, reduced_ast_facts)

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
      | Chc.Elt.FuncApply ("DetailedDUEdge", args) ->
          (List.rev args |> List.tl_exn) @ acc
      | Chc.Elt.FuncApply ("EvalLv", args) -> List.hd_exn args :: acc
      | _ -> acc)
    deps
  |> List.fold_left ~init:[] ~f:(fun acc node ->
         match node with
         | Chc.Elt.FDNumeral n -> (
             try Hashtbl.find node_map n :: acc with _ -> acc)
         | _ -> acc)

let extract_parent sym_diff (ast_map : (Ast.t, int) Hashtbl.t) =
  let parent_of_patch =
    List.fold_left ~init:[]
      ~f:(fun acc diff -> SymDiff.extract_context diff :: acc)
      sym_diff
    (* Consider that patch occured in a single location for now *)
    |> List.fold_left ~init:[] ~f:(fun acc c ->
           (c.SymDiff.parent_of_patch.node, c.SymDiff.func_name) :: acc)
  in
  List.fold_left ~init:[]
    ~f:(fun acc (p, f) ->
      match p with
      | SymDiff.SymAst.SGlob _ -> ("", f) :: acc
      | SStmt (_, s) ->
          (Ast.stmt2ast (Some s) |> Hashtbl.find ast_map |> string_of_int, f)
          :: acc
      | _ -> failwith "parent not found")
    parent_of_patch
  |> List.rev

let rec go_up parent_tups ast_node_lst (parent, _) acc =
  let candidates =
    List.fold_left ~init:[]
      ~f:(fun cand (parent', child') ->
        if String.equal parent parent' then (parent', child') :: cand else cand)
      parent_tups
  in
  if List.length candidates = 0 then
    let upper_node_opt =
      List.find ~f:(fun (_, c') -> String.equal parent c') acc
    in
    let upper_node =
      if Option.is_none upper_node_opt then
        failwith "compute_ast_pattern: common ancestor not found"
      else Option.value_exn upper_node_opt
    in
    go_up parent_tups ast_node_lst upper_node (upper_node :: acc)
  else if
    List.exists
      ~f:(fun (_, c') ->
        List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
      candidates
  then
    List.find_exn
      ~f:(fun (_, c') ->
        List.exists ~f:(fun n -> String.equal n c') ast_node_lst)
      candidates
    :: acc
  else
    let down = fold_down parent_tups ast_node_lst candidates [] in
    let upper_node_opt =
      List.find ~f:(fun (_, c') -> String.equal parent c') acc
    in
    let upper_node =
      if Option.is_none upper_node_opt then
        failwith "common ancestor not found!"
      else Option.value_exn upper_node_opt
    in
    if List.length down = 0 then
      go_up parent_tups ast_node_lst upper_node (upper_node :: acc)
    else acc @ down

and go_down parent_tups ast_node_lst (p, c) acc =
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
    else fold_down parent_tups ast_node_lst candidates ((p, c) :: acc)

and fold_down parent_tups ast_node_lst candidates acc =
  List.fold_left ~init:[]
    ~f:(fun acc' edge ->
      go_down parent_tups ast_node_lst edge (edge :: acc) @ acc')
    candidates

let mk_ast_bug_pattern node_map solution =
  List.fold_left ~init:[]
    ~f:(fun acc (p, c) ->
      let p = Chc.Elt.FDNumeral ("AstNode-" ^ p) in
      let c = Chc.Elt.FDNumeral ("AstNode-" ^ c) in
      Chc.Elt.FuncApply ("AstParent", [ p; c ]) :: acc)
    solution
  |> fun x ->
  List.fold_left ~init:x
    ~f:(fun acc (p, c) ->
      let p_cfg = Hashtbl.find_opt node_map p in
      let c_cfg = Hashtbl.find_opt node_map c in
      let p_ast = Chc.Elt.FDNumeral ("AstNode-" ^ p) in
      let c_ast = Chc.Elt.FDNumeral ("AstNode-" ^ c) in
      if Option.is_some p_cfg && Option.is_some c_cfg then
        Chc.Elt.FuncApply
          ("EqNode", [ FDNumeral (Option.value_exn p_cfg); p_ast ])
        :: Chc.Elt.FuncApply
             ("EqNode", [ FDNumeral (Option.value_exn c_cfg); c_ast ])
        :: acc
      else if Option.is_some p_cfg then
        Chc.Elt.FuncApply
          ("EqNode", [ FDNumeral (Option.value_exn p_cfg); p_ast ])
        :: acc
      else if Option.is_some c_cfg then
        Chc.Elt.FuncApply
          ("EqNode", [ FDNumeral (Option.value_exn c_cfg); c_ast ])
        :: acc
      else acc)
    solution

let mk_parent_tups_str func stmts ast_map =
  Parser.mk_parent_tuples func stmts
  |> List.fold_left ~init:[] ~f:(fun acc (p, c) ->
         if Hashtbl.mem ast_map p && Hashtbl.mem ast_map c then
           ( Hashtbl.find ast_map p |> string_of_int,
             Hashtbl.find ast_map c |> string_of_int )
           :: acc
         else acc)

let compute_ast_pattern ast_node_lst patch_node patch_func maps ast =
  if String.equal patch_func "None" then failwith "compute_ast_pattern: no func";
  let ast_map = maps.Maps.ast_map in
  let node_map = maps.Maps.node_map |> Utils.reverse_hashtbl in
  L.info "Compute AST pattern...";
  let stmts = Utils.extract_target_func_stmt_lst ast patch_func in
  let func = Utils.extract_target_func ast patch_func in
  let parent_tups = mk_parent_tups_str [ func ] stmts ast_map in
  let init =
    List.find_exn ~f:(fun (p, _) -> String.equal p patch_node) parent_tups
  in
  let solution = go_up parent_tups ast_node_lst init [ init ] in
  mk_ast_bug_pattern node_map solution

let need_ast_pattern diff =
  match List.hd_exn diff with SymDiff.SUpdateExp _ -> false | _ -> true

let abstract_bug_pattern facts src snk aexps maps diff ast =
  let fact_lst = Chc.to_list facts in
  let ast_node_lst = collect_nodes fact_lst maps.Maps.node_map in
  if List.length ast_node_lst = 0 then
    failwith "abstract_bug_pattern: no AST nodes corresponding CFG nodes found";
  (* List.iter ~f:(fun n -> L.info "facts: %a" Chc.pp_chc n) fact_lst;
     List.iter ~f:(fun n -> L.info "ast_node_lst: %s" n) ast_node_lst; *)
  let parents = extract_parent diff maps.Maps.ast_map in
  let smallest_ast_patterns =
    List.fold_left ~init:[]
      ~f:(fun acc (patch_node, patch_func) ->
        if need_ast_pattern diff |> not || String.is_empty patch_node then acc
        else
          compute_ast_pattern ast_node_lst patch_node patch_func maps ast @ acc)
      parents
  in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  ( Chc.Elt.Implies (fact_lst @ smallest_ast_patterns, errtrace)
    |> Chc.Elt.numer2var |> Chc.singleton,
    ast_node_lst )

let match_bug_for_one_prj pattern buggy_maps buggy_dir target_alarm ast cfg
    out_dir patch_ids patch_ingredients diff =
  let target_maps = Maps.create_maps () in
  Maps.reset_maps target_maps;
  try
    let cf_facts, ast_facts, (src, snk, aexps) =
      Parser.make_facts buggy_dir target_alarm ast cfg out_dir target_maps
    in
    let cf_facts', ast_facts' =
      collect_deps target_maps ast src snk aexps cf_facts ast_facts
    in
    let combined_facts = Chc.union cf_facts' ast_facts' in
    let z3env = Z3env.get_env () in
    L.info "Try matching with %s..." target_alarm;
    let status =
      Chc.match_and_log z3env buggy_dir target_alarm out_dir target_alarm
        target_maps combined_facts src snk pattern
    in
    Maps.dump target_alarm target_maps out_dir;
    if Option.is_some status then
      Modeling.match_ans buggy_maps target_maps target_alarm out_dir;
    L.info "Matching with %s is done" target_alarm;
    let ef =
      EditFunction.translate ast diff
        (Filename.concat out_dir (target_alarm ^ "_sol.map"))
        target_maps patch_ids patch_ingredients
    in
    L.info "Applying patch on the target file ...";
    let patch_file = Patch.apply diff ast ef in
    let out_file = String.concat [ out_dir; "/patch_"; target_alarm; ".c" ] in
    let out_chan = Out_channel.create out_file in
    Cil.dumpFile Cil.defaultCilPrinter out_chan "patch.c" patch_file;
    L.info "Patch for %s is done, written at %s" target_alarm out_file
  with Parser.Not_impl_aexp -> L.info "PASS"

let is_new_alarm dir ta a =
  (not (String.equal ta a))
  && Sys.is_directory (Filename.concat dir ("sparrow-out/taint/datalog/" ^ a))

let match_with_new_alarms buggy_dir true_alarm buggy_maps buggy_ast buggy_cfg
    pattern out_dir patch_ids patch_ingredients diff =
  Sys.readdir (Filename.concat buggy_dir "sparrow-out/taint/datalog")
  |> Array.iter ~f:(fun ta ->
         if is_new_alarm buggy_dir true_alarm ta then
           match_bug_for_one_prj pattern buggy_maps buggy_dir ta buggy_ast
             buggy_cfg out_dir patch_ids patch_ingredients diff)

let run (inline_funcs, write_out) true_alarm buggy_dir patch_dir out_dir =
  let buggy_maps = Maps.create_maps () in
  Maps.reset_maps buggy_maps;
  let buggy_ast = Parser.parse_ast buggy_dir inline_funcs in
  let patch_ast = Parser.parse_ast patch_dir inline_funcs in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff buggy_ast patch_ast in
  L.info "Loading CFG Elements...";
  let buggy_cfg =
    Utils.parse_node_json (Filename.concat buggy_dir "sparrow-out")
  in
  L.info "CFG Elements Loading Done!";
  let cf_facts, ast_facts, (src, snk, aexps) =
    Parser.make_facts buggy_dir true_alarm buggy_ast buggy_cfg out_dir
      buggy_maps
  in
  L.info "Make Facts in buggy done";
  L.info "Mapping CFG Elements to AST nodes...";
  let sym_diff, patch_comps =
    SymDiff.define_sym_diff buggy_maps buggy_ast ast_diff
  in
  if write_out then (
    L.info "Writing out the edit script...";
    SymDiff.to_json sym_diff out_dir);
  let cf_facts', ast_facts' =
    collect_deps buggy_maps buggy_ast src snk aexps cf_facts ast_facts
  in
  let combined_facts = Chc.union cf_facts' ast_facts' in
  let patch_node_ids =
    extract_parent sym_diff buggy_maps.Maps.ast_map |> List.map ~f:fst
  in
  Maps.dump_ast "buggy" buggy_maps out_dir;
  let pattern, patch_ingredients =
    abstract_bug_pattern cf_facts' src snk aexps buggy_maps sym_diff buggy_ast
  in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern") pattern;
  let z3env = Z3env.get_env () in
  L.info "Try matching with buggy...";
  ( Chc.match_and_log z3env buggy_dir true_alarm out_dir "buggy" buggy_maps
      combined_facts src snk pattern
  |> fun status -> assert (Option.is_some status) );
  Maps.dump "buggy" buggy_maps out_dir;
  match_with_new_alarms buggy_dir true_alarm buggy_maps patch_ast buggy_cfg
    pattern out_dir patch_node_ids patch_ingredients sym_diff;
  L.info "Done."
