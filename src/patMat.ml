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

let reduce_parent_facts maps ast facts =
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

let rec fixedpoint ?(ignore_duedge = false) rels terms deps =
  let deps', terms' =
    Chc.fold
      (fun c (deps, terms) ->
        let is_nec, terms' = Chc.prop_deps ~ignore_duedge terms c in
        ((if is_nec then Chc.add c deps else deps), terms'))
      rels (deps, terms)
  in
  if Chc.subset deps' deps && Chc.subset terms' terms then (deps', terms')
  else fixedpoint rels terms' deps'

let remove_before_src_after_snk src snk rels =
  let src_node, snk_node = (Chc.Elt.FDNumeral src, Chc.Elt.FDNumeral snk) in
  let before_src = Chc.collect_node ~before:true src_node rels in
  let after_snk = Chc.collect_node ~before:false snk_node rels in
  let before_deps =
    fixedpoint ~ignore_duedge:true rels before_src Chc.empty |> fst
  in
  let after_deps =
    fixedpoint ~ignore_duedge:true rels after_snk Chc.empty |> fst
  in
  rels |> (Fun.flip Chc.diff) before_deps |> (Fun.flip Chc.diff) after_deps

let reduce_facts maps ast src snk alarm_comps du_chc parent_chc =
  let func_apps =
    Chc.extract_func_apps du_chc |> remove_before_src_after_snk src snk
  in
  let snk_term = Chc.Elt.FDNumeral snk in
  let terms = Chc.add snk_term alarm_comps in
  let reduced_du_facts = fixedpoint func_apps terms Chc.empty |> fst in
  let reduced_parent_facts = reduce_parent_facts maps ast parent_chc in
  (* (reduced_du_facts, reduced_parent_facts) *)
  (du_chc, reduced_parent_facts)

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

let extract_parent abs_diff (ast_map : (Ast.t, int) Hashtbl.t) =
  let parent_of_patch =
    List.fold_left ~init:[]
      ~f:(fun acc diff -> AbsDiff.extract_context diff :: acc)
      abs_diff
    (* Consider that patch occured in a single location for now *)
    |> List.fold_left ~init:[] ~f:(fun acc c ->
           (c.AbsDiff.parent_of_patch.node, c.AbsDiff.func_name) :: acc)
  in
  List.fold_left ~init:[]
    ~f:(fun acc (p, f) ->
      match p with
      | AbsDiff.AbsAst.AbsGlob (_, g) ->
          (Ast.glob2ast (Some g) |> Hashtbl.find ast_map |> string_of_int, f)
          :: acc
      | AbsStmt (_, s) ->
          (Ast.stmt2ast (Some s) |> Hashtbl.find ast_map |> string_of_int, f)
          :: acc
      | _ -> failwith "parent not found")
    parent_of_patch
  |> List.rev

let rec go_up parent_tups ast_node_lst (parent, child) acc =
  let candidates =
    List.fold_left ~init:[]
      ~f:(fun cand (parent', child') ->
        if String.equal parent parent' && not (String.equal child child') then
          (parent', child') :: cand
        else cand)
      parent_tups
  in
  if List.length candidates = 0 then
    let upper_tups_opt =
      List.find ~f:(fun (_, c') -> String.equal parent c') parent_tups
    in
    let upper_tups =
      if Option.is_none upper_tups_opt then
        failwith "compute_ast_pattern: common ancestor not found"
      else Option.value_exn upper_tups_opt
    in
    go_up parent_tups ast_node_lst upper_tups (upper_tups :: acc)
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
    if List.length down = 0 then
      let upper_tups_opt =
        List.find ~f:(fun (_, c') -> String.equal parent c') acc
      in
      let upper_tups =
        if Option.is_none upper_tups_opt then
          failwith "common ancestor not found!"
        else Option.value_exn upper_tups_opt
      in
      go_up parent_tups ast_node_lst upper_tups (upper_tups :: acc)
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

let search_eq_ast_rel ast_facts fa = Chc.find fa ast_facts

let mk_ast_bug_pattern ast_facts node_map solution =
  List.fold_left ~init:[]
    ~f:(fun acc (p, c) ->
      let p = Chc.Elt.FDNumeral ("AstNode-" ^ p) in
      let c = Chc.Elt.FDNumeral ("AstNode-" ^ c) in
      (Chc.Elt.FuncApply ("AstParent", [ p; c ]) |> search_eq_ast_rel ast_facts)
      :: acc)
    solution
  |> fun x ->
  List.fold_left ~init:x
    ~f:(fun acc (p, c) ->
      let p_cfg = Hashtbl.find_opt node_map p in
      let c_cfg = Hashtbl.find_opt node_map c in
      let p_ast = Chc.Elt.FDNumeral ("AstNode-" ^ p) in
      let c_ast = Chc.Elt.FDNumeral ("AstNode-" ^ c) in
      if Option.is_some p_cfg && Option.is_some c_cfg then
        (Chc.Elt.FuncApply
           ("EqNode", [ FDNumeral (Option.value_exn p_cfg); p_ast ])
        |> search_eq_ast_rel ast_facts)
        :: (Chc.Elt.FuncApply
              ("EqNode", [ FDNumeral (Option.value_exn c_cfg); c_ast ])
           |> search_eq_ast_rel ast_facts)
        :: acc
      else if Option.is_some p_cfg then
        (Chc.Elt.FuncApply
           ("EqNode", [ FDNumeral (Option.value_exn p_cfg); p_ast ])
        |> search_eq_ast_rel ast_facts)
        :: acc
      else if Option.is_some c_cfg then
        (Chc.Elt.FuncApply
           ("EqNode", [ FDNumeral (Option.value_exn c_cfg); c_ast ])
        |> search_eq_ast_rel ast_facts)
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

let greedy_search_common_ancestor func stmts ast_map ast_node_lst
    parent_of_patch =
  let parent_tups = mk_parent_tups_str [ func ] stmts ast_map in
  let init =
    List.find_exn ~f:(fun (p, _) -> String.equal p parent_of_patch) parent_tups
  in
  go_up parent_tups ast_node_lst init []

let find_eq_rel ast_facts patch_node =
  let patch_node = Chc.Elt.FDNumeral ("AstNode-" ^ patch_node) in
  let ast_fact_lst = Chc.to_list ast_facts in
  List.find
    ~f:(fun fact ->
      match fact with
      | Chc.Elt.FuncApply ("EqNode", [ _; p ]) ->
          if Chc.Elt.equal patch_node p then true else false
      | _ -> false)
    ast_fact_lst

let compute_ast_pattern ast_facts ast_node_lst parent_of_patch patch_func maps
    ast =
  let parent_in_pattern = find_eq_rel ast_facts parent_of_patch in
  if Option.is_some parent_in_pattern then
    [ Option.value_exn parent_in_pattern ]
  else (
    if String.equal patch_func "None" then
      failwith "compute_ast_pattern: no func";
    let ast_map = maps.Maps.ast_map in
    let node_map = maps.Maps.node_map |> Utils.reverse_hashtbl in
    L.info "Compute AST pattern...";
    let stmts = Utils.extract_target_func_stmt_lst ast patch_func in
    let func = Utils.extract_target_func ast patch_func in
    let solution =
      greedy_search_common_ancestor func stmts ast_map ast_node_lst
        parent_of_patch
    in
    mk_ast_bug_pattern ast_facts node_map solution)

let is_patch_under_func parent ast_map =
  Stdlib.Hashtbl.fold
    (fun k v acc -> if int_of_string parent = v then k :: acc else acc)
    ast_map []
  |> List.hd_exn
  |> fun node -> Ast.is_glob node || Ast.is_fun node

let abstract_bug_pattern du_facts ast_facts dug patch_comps src snk alarm_comps
    maps diff ast =
  let fst_abs_facts =
    Chc.abstract_by_comps du_facts dug patch_comps snk alarm_comps
  in
  let fact_lst = Chc.to_list fst_abs_facts in
  let ast_node_lst = Chc.extract_nodes_in_facts fact_lst maps.Maps.node_map in
  if List.length ast_node_lst = 0 then
    failwith "abstract_bug_pattern: no AST nodes corresponding CFG nodes found";
  let parents = extract_parent diff maps.Maps.ast_map in
  let smallest_ast_patterns =
    List.fold ~init:[]
      ~f:(fun acc (parent, func) ->
        compute_ast_pattern ast_facts ast_node_lst parent func maps ast @ acc)
      parents
    |> Stdlib.List.sort_uniq Chc.Elt.compare
  in
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  let pattern_in_numeral =
    Chc.Elt.Implies (fact_lst @ smallest_ast_patterns, errtrace)
  in
  ( pattern_in_numeral |> Chc.singleton,
    pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton )

let mk_file_diff orig_path patch_path target_alarm out_dir =
  Sys.command
    (String.concat
       [
         "diff -u ";
         orig_path;
         " ";
         patch_path;
         " > ";
         Filename.concat out_dir ("result_" ^ target_alarm ^ "_diff.patch");
       ])
  |> ignore

let match_bug_for_one_prj pattern buggy_maps donee_dir target_alarm ast cfg
    out_dir diff =
  let target_maps = Maps.create_maps () in
  Maps.reset_maps target_maps;
  try
    let du_facts, parent_facts, (src, snk, alarm_comps) =
      Parser.make_facts donee_dir target_alarm ast cfg out_dir target_maps
    in
    let du_facts', parent_facts' =
      reduce_facts target_maps ast src snk alarm_comps du_facts parent_facts
    in
    let combined_facts = Chc.union du_facts' parent_facts' in
    let z3env = Z3env.get_env () in
    L.info "Try matching with %s..." target_alarm;
    let status =
      Chc.match_and_log z3env out_dir target_alarm target_maps combined_facts
        src snk pattern
    in
    Maps.dump target_alarm target_maps out_dir;
    if Option.is_some status then
      Modeling.match_ans buggy_maps target_maps target_alarm out_dir;
    L.info "Matching with %s is done" target_alarm;
    let patch_parent_lst =
      extract_parent diff buggy_maps.Maps.ast_map |> List.map ~f:fst
    in
    let ef =
      EditFunction.translate ast diff
        (Filename.concat out_dir (target_alarm ^ "_sol.map"))
        target_maps patch_parent_lst parent_facts
    in
    L.info "Applying patch on the target file ...";
    let out_file_orig =
      String.concat [ out_dir; "/orig_"; target_alarm; ".c" ]
    in
    Patch.write_out out_file_orig ast;
    let patch_file = Patch.apply diff ast ef in
    let out_file_patch =
      String.concat [ out_dir; "/patch_"; target_alarm; ".c" ]
    in
    Patch.write_out out_file_patch patch_file;
    L.info "Patch for %s is done, written at %s" target_alarm out_file_patch;
    mk_file_diff out_file_orig out_file_patch target_alarm out_dir
  with Parser.Not_impl_alarm_comps -> L.info "PASS"

let is_new_alarm buggy_dir true_alarm donee_dir target_alarm =
  (not
     (String.equal buggy_dir donee_dir && String.equal true_alarm target_alarm))
  && Sys.is_directory
       (Filename.concat donee_dir ("sparrow-out/taint/datalog/" ^ target_alarm))

let match_with_new_alarms buggy_dir true_alarm donee_dir buggy_maps buggy_ast
    buggy_cfg pattern out_dir diff =
  Sys.readdir (Filename.concat donee_dir "sparrow-out/taint/datalog")
  |> Array.iter ~f:(fun ta ->
         if is_new_alarm buggy_dir true_alarm donee_dir ta then
           match_bug_for_one_prj pattern buggy_maps donee_dir ta buggy_ast
             buggy_cfg out_dir diff)

let run (inline_funcs, write_out) true_alarm buggy_dir patch_dir donee_dir
    out_dir =
  let buggy_maps = Maps.create_maps () in
  Maps.reset_maps buggy_maps;
  let buggy_ast = Parser.parse_ast buggy_dir inline_funcs in
  let patch_ast = Parser.parse_ast patch_dir inline_funcs in
  let donee_ast =
    if String.equal (buggy_dir ^ "/bug") donee_dir then patch_ast
    else Parser.parse_ast donee_dir inline_funcs
  in
  L.info "Constructing AST diff...";
  let ast_diff = Diff.define_diff buggy_ast patch_ast in
  L.info "Loading CFG Elements...";
  let buggy_cfg =
    Utils.parse_node_json (Filename.concat buggy_dir "sparrow-out")
  in
  L.info "CFG Elements Loading Done!";
  let du_facts, parent_facts, (src, snk, alarm_comps) =
    Parser.make_facts buggy_dir true_alarm buggy_ast buggy_cfg out_dir
      buggy_maps
  in
  L.info "Make Facts in buggy done";
  let du_facts', parent_facts' =
    reduce_facts buggy_maps buggy_ast src snk alarm_comps du_facts parent_facts
  in
  let combined_facts = Chc.union du_facts' parent_facts' in
  L.info "Mapping CFG Elements to AST nodes...";
  let du_rels = Chc.filter Chc.Elt.is_duedge du_facts' in
  let dug = Chc.to_dug du_rels in
  let abs_diff, patch_comps =
    AbsDiff.define_abs_diff buggy_maps buggy_ast ast_diff du_facts'
      (Dug.copy dug) (src, snk)
  in
  if write_out then (
    L.info "Writing out the edit script...";
    AbsDiff.to_json abs_diff out_dir);
  Maps.dump_ast "buggy" buggy_maps out_dir;
  let pattern_in_numeral, pattern =
    abstract_bug_pattern du_facts' parent_facts' dug patch_comps src snk
      alarm_comps buggy_maps abs_diff buggy_ast
  in
  L.info "Make Bug Pattern done";
  Chc.pretty_dump (Filename.concat out_dir "pattern") pattern;
  Chc.sexp_dump (Filename.concat out_dir "pattern") pattern;
  let z3env = Z3env.get_env () in
  L.info "Try matching with buggy...";
  ( Chc.match_and_log z3env out_dir "buggy" buggy_maps combined_facts src snk
      pattern
  |> fun status -> assert (Option.is_some status) );
  Maps.dump "buggy" buggy_maps out_dir;
  L.info "Try matching with buggy numeral...";
  ( Chc.match_and_log z3env out_dir "buggy_numer" buggy_maps combined_facts src
      snk pattern_in_numeral
  |> fun status -> assert (Option.is_some status) );
  Maps.dump "buggy_numer" buggy_maps out_dir;
  match_with_new_alarms buggy_dir true_alarm donee_dir buggy_maps donee_ast
    buggy_cfg pattern out_dir abs_diff;
  L.info "Done."
