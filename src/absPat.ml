open Core
module Set = Stdlib.Set
module StrSet = Set.Make (String)
module Map = Stdlib.Map
module Hashtbl = Stdlib.Hashtbl
module L = Logger
module F = Format
module NodeSet = Set.Make (String)

let arbitrary_node_cnt = ref 1
let arbitrary_exp_cnt = ref 1

let mk_arbitrary_node () =
  let node = "Node-" ^ String.make !arbitrary_node_cnt '0' in
  incr arbitrary_node_cnt;
  node

let mk_arbitrary_exp () =
  let exp = "Exp-" ^ String.make (!arbitrary_exp_cnt + 1) '0' in
  incr arbitrary_exp_cnt;
  exp

let is_arbitrary_exp e =
  String.is_prefix ~prefix:"Exp-" e
  && String.is_suffix ~suffix:(String.make (String.length e - 4) '0') e

let get_previous_arbitrary_exp () =
  let exp = "Exp-" ^ String.make !arbitrary_exp_cnt '0' in
  exp

let comps_of_facts facts =
  Chc.fold
    (fun rel acc ->
      match rel with
      | Chc.Elt.FuncApply ("Assume", [ _; e ]) -> Chc.add e acc
      | FuncApply ("BinOpExp", [ _; e1; e2 ]) -> Chc.add e1 acc |> Chc.add e2
      | FuncApply ("Set", [ _; lv; e ]) -> Chc.add e acc |> Chc.add lv
      | FuncApply ("LvalExp", [ e; lv ]) -> Chc.add e acc |> Chc.add lv
      | FuncApply ("EvalLv", [ _; lv; _ ]) -> Chc.add lv acc
      | FuncApply ("CallExp", [ e; _; _ ]) -> Chc.add e acc
      | FuncApply ("LibCallExp", [ e; _; _ ]) -> Chc.add e acc
      | FuncApply ("ReadCallExp", [ e; _; _ ]) -> Chc.add e acc
      | FuncApply ("AllocExp", [ e; _ ]) -> Chc.add e acc
      | FuncApply ("SAllocExp", [ e; _ ]) -> Chc.add e acc
      | FuncApply ("Var", [ e ]) -> Chc.add e acc
      | FuncApply ("Index", [ _; _; e ]) -> Chc.add e acc
      | FuncApply ("Mem", [ _; e ]) -> Chc.add e acc
      | FuncApply ("AddrOf", [ e; _ ]) -> Chc.add e acc
      | _ -> acc)
    facts Chc.empty

let collect_ast_rels dug node leaf =
  let node_info = Dug.info_of_v dug node in
  Chc.fixedpoint Chc.from_ast_to_node node_info.Dug.rels leaf Chc.empty |> fst

let def_from_skip_nodes dug snk def_skip_nodes =
  let node = NodeSet.choose def_skip_nodes in
  (* TEMP: for more simple pattern *)
  Dug.shortest_path dug node snk |> Dug.path2rels

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

let def_from_normal_node dug cmd_map lv_term loc used_node node rels_acc =
  let terms = Chc.singleton loc in
  let ast_rels = collect_ast_rels dug node terms in
  let find_path_rels succ path_rels =
    if
      (not (Dug.is_skip_node cmd_map succ))
      && Hashtbl.find dug.label (node, succ) |> Chc.mem lv_term
    then
      let path = Dug.shortest_path_opt dug succ used_node in
      if Option.is_none path then path_rels
      else
        Option.value_exn path |> Dug.path2rels
        |> Chc.add (Chc.Elt.duedge node succ)
        |> Chc.union path_rels
    else path_rels
  in
  Dug.fold_succ find_path_rels dug node rels_acc |> Chc.union ast_rels

let def_from_normal_nodes dug cmd_map lv_term loc used_node def_nodes =
  NodeSet.fold
    (def_from_normal_node dug cmd_map lv_term loc used_node)
    def_nodes Chc.empty

let find_rels_using_defs cmd_map dug snk facts lv (def_skip_nodes, def_nodes) =
  (* NOTE: hack for skip node (ENTRY, EXIT, ReturnNode, ...) *)
  if NodeSet.is_empty def_nodes then
    (def_from_skip_nodes dug snk def_skip_nodes, def_skip_nodes)
  else
    let loc = Chc.find_loc lv facts in
    let loc_rels, used_node = find_rels_by_loc dug snk loc facts in
    ( def_from_normal_nodes dug cmd_map lv loc used_node def_nodes
      |> Chc.union loc_rels,
      def_nodes )

let find_rels_by_lv dug cmd_map snk lv facts =
  let open Option in
  Hashtbl.find_opt dug.Dug.def_map lv
  >>| NodeSet.partition (Dug.is_skip_node cmd_map)
  >>| find_rels_using_defs cmd_map dug snk facts lv

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

let rm_dangling_duedge rels facts =
  let ast_rels = Chc.filter (fun c -> not (Chc.Elt.is_duedge c)) rels in
  let nodes, exps =
    Chc.fold
      (fun c (nodes, exps) ->
        match c with
        | Chc.Elt.FuncApply ("Set", [ n; _; e ]) ->
            (Chc.add n nodes, Chc.add e exps)
        | Chc.Elt.FuncApply ("Assume", [ n; _ ])
        | Chc.Elt.FuncApply ("Return", [ n; _ ])
        | Chc.Elt.FuncApply ("EvalLv", [ n; _; _ ]) ->
            (Chc.add n nodes, exps)
        | _ -> (nodes, exps))
      ast_rels (Chc.empty, Chc.empty)
  in
  let duedges =
    Chc.filter Chc.Elt.is_duedge rels
    |> Chc.filter (fun c ->
           match c with
           | Chc.Elt.FuncApply ("DUEdge", [ n1; n2 ]) ->
               Chc.mem n1 nodes || Chc.mem n2 nodes
           | _ -> false)
  in
  let ast_rels' =
    Chc.fold
      (fun c acc ->
        match c with
        | Chc.Elt.FuncApply ("CallExp", [ e; _; _ ])
        | Chc.Elt.FuncApply ("ReadCallExp", [ e; _; _ ])
        | Chc.Elt.FuncApply ("LibCallExp", [ e; _; _ ])
        | Chc.Elt.FuncApply ("AllocExp", [ e; _; _ ]) ->
            if Chc.mem e exps then Chc.add c acc else acc
        | _ -> acc)
      facts Chc.empty
    |> Chc.union ast_rels
  in
  Chc.union duedges ast_rels'

let abs_by_comps ?(new_ad = false) maps dug patch_comps snk alarm_exps alarm_lvs
    facts abs_diff cmd =
  patch_comps2str maps patch_comps |> L.info "patch_comps: %s";
  terms2str alarm_exps |> L.info "alarm_exps: %s";
  terms2str alarm_lvs |> L.info "alarm_lvs: %s";
  if Chc.subset patch_comps alarm_lvs && Options.is_dtd cmd then
    ( collect_ast_rels dug snk patch_comps,
      if new_ad then AbsDiff.change_use (StrSet.singleton snk) abs_diff
      else abs_diff )
  else
    let collected_by_patch_comps, defs =
      Chc.fold
        (fun lv (rels, defs) ->
          let r_opt = find_rels_by_lv dug maps.Maps.cmd_map snk lv facts in
          if Option.is_none r_opt then (rels, defs)
          else
            let path_rels, new_defs = Option.value_exn r_opt in
            (Chc.union path_rels rels, NodeSet.union defs new_defs))
        patch_comps (Chc.empty, NodeSet.empty)
    in
    let filetered_patch_comps =
      rm_dangling_duedge collected_by_patch_comps facts
    in
    let collected_by_alarm_comps = collect_ast_rels dug snk alarm_exps in
    let abs_diff' =
      AbsDiff.change_def defs abs_diff
      |> AbsDiff.change_use (StrSet.singleton snk)
    in
    ( Chc.union filetered_patch_comps collected_by_alarm_comps
      |> Chc.remove_detached_edges,
      if new_ad then abs_diff' else abs_diff )

let get_ast_rels_by_node dug node =
  let node_info = Dug.info_of_v dug node in
  node_info.Dug.rels

let get_src_rels dug src edges =
  let src_asts = get_ast_rels_by_node dug src in
  let src_duedge = List.hd_exn edges |> Dug.edge2rel in
  ( Chc.filter
      (fun c ->
        match c with
        | Chc.Elt.FuncApply ("Set", _)
        | Chc.Elt.FuncApply ("CallExp", _)
        | Chc.Elt.FuncApply ("ReadCallExp", _)
        | Chc.Elt.FuncApply ("LibCallExp", _)
        | Chc.Elt.FuncApply ("AllocExp", _) ->
            true
        | _ -> false)
      src_asts
    |> Chc.add src_duedge,
    List.tl_exn edges )

let filter_interesting_rels duedge rels =
  if
    Chc.exists
      (fun c ->
        match c with
        | Chc.Elt.FuncApply ("BinOpExp", _)
        | Chc.Elt.FuncApply ("ReadCallExp", _)
        | Chc.Elt.FuncApply ("AllocExp", _) ->
            true
        | _ -> false)
      rels
  then Chc.add duedge rels
  else Chc.empty

let get_nodes facts =
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply ("DUEdge", [ n1; n2 ]) ->
          (n1 |> Chc.Elt.to_sym) :: (n2 |> Chc.Elt.to_sym) :: acc
      | Chc.Elt.FuncApply ("Set", [ n; _; _ ]) -> (n |> Chc.Elt.to_sym) :: acc
      | _ -> acc)
    facts []

let mk_patterns maps dug patch_comps src snk alarm_exps alarm_lvs facts abs_diff
    cmd =
  let abs_facts, abs_diff' =
    abs_by_comps maps dug patch_comps snk alarm_exps alarm_lvs facts abs_diff
      cmd
  in
  let abs_nodes = get_nodes abs_facts in
  let snk_func = Utils.get_func_name_from_node snk in
  let alt_pc, alt_diff = find_alt_lvs snk_func facts patch_comps abs_diff in
  let alt_facts, alt_diff' =
    if Chc.is_empty alt_pc then (Chc.empty, [])
    else
      abs_by_comps ~new_ad:true maps dug alt_pc snk alarm_exps alarm_lvs facts
        alt_diff cmd
  in
  let alt_nodes = get_nodes alt_facts in
  let edges = Dug.shortest_path dug src snk in
  let src_rels, edges' = get_src_rels dug src edges in
  let full_facts =
    List.fold ~init:(src_rels, false)
      ~f:(fun (acc, is_finished) edge ->
        if is_finished then (acc, is_finished)
        else
          let src_node = Dug.I.E.src edge in
          if
            List.mem alt_nodes src_node ~equal:String.equal
            || List.mem abs_nodes src_node ~equal:String.equal
          then (acc, true)
          else
            let duedge = Dug.edge2rel edge in
            let filtered_rels =
              get_ast_rels_by_node dug src_node
              |> filter_interesting_rels duedge
            in
            (Chc.union filtered_rels acc, is_finished))
      edges'
    |> fst
  in
  let full_facts' = Chc.union full_facts abs_facts in
  let full_alt_facts = Chc.union full_facts' alt_facts in
  (full_facts', abs_facts, abs_diff', full_alt_facts, alt_facts, alt_diff')

let num_of_rels rels =
  F.asprintf "#Rels: %d, #DUEdges: %d" (Chc.cardinal rels)
    (Chc.filter Chc.Elt.is_duedge rels |> Chc.cardinal)

let is_patch_comp abs_node comp =
  AbsDiff.StrSet.exists (fun s -> String.equal comp s) abs_node

let get_eq_exp abs_node patch_exps =
  Chc.fold
    (fun exp acc ->
      let exp_str = Chc.Elt.to_sym exp in
      if is_patch_comp abs_node.AbsDiff.ids exp_str then exp_str :: acc else acc)
    patch_exps []
  |> List.hd

let absbinop2chcop = function
  | AbsDiff.SPlusA -> "PlusA"
  | SPlusPI -> "PlusPI"
  | SIndexPI -> "IndexPI"
  | SMinusA -> "MinusA"
  | SMinusPI -> "MinusPI"
  | SMinusPP -> "MinusPP"
  | SMod -> "Mod"
  | SShiftlt -> "bvshl"
  | SShiftrt -> "bvshr"
  | SAnd -> "bvand"
  | SXor -> "bvxor"
  | SOr -> "bvor"
  | SMult -> "Mult"
  | SDiv -> "Div"
  | SEq -> "Eq"
  | SNe -> "Ne"
  | SLt -> "Lt"
  | SLe -> "Le"
  | SGt -> "Gt"
  | SGe -> "Ge"
  | SLAnd -> "and"
  | SLOr -> "or"

let absunop2chcop = function AbsDiff.SNot -> "BNot" | SNeg -> "Neg"

let lv2exp facts lv =
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply ("LvalExp", [ e; lv' ]) ->
          if Chc.Elt.to_sym lv' |> String.equal lv then e :: acc else acc
      | _ -> acc)
    facts []
  |> List.hd
  |> fun e ->
  if Option.is_none e then (mk_arbitrary_exp (), false)
  else (Option.value_exn e |> Chc.Elt.to_sym, true)

let abs_lv2chc facts patch_exps abs_ast =
  match abs_ast with
  | AbsDiff.AbsExp (exp, _) -> (
      match exp with
      | AbsDiff.SELval lv_node ->
          let parent_exp = mk_arbitrary_exp () in
          let lval_opt = get_eq_exp lv_node patch_exps in
          if Option.is_none lval_opt then (parent_exp, false)
          else lv2exp facts (Option.value_exn lval_opt)
      | _ -> (mk_arbitrary_exp (), false))
  | _ -> L.error "non-Exp node in abs_lv2chc"

let rec abs_exp2chc facts patch_exps abs_node acc =
  match abs_node.AbsDiff.ast with
  | AbsDiff.AbsExp _ when AbsDiff.is_selv abs_node.AbsDiff.ast ->
      let exp, is_arb = abs_lv2chc facts patch_exps abs_node.AbsDiff.ast in
      (exp, acc, is_arb)
  | AbsDiff.AbsExp (abs_exp, _) ->
      let exp_opt = get_eq_exp abs_node patch_exps in
      let exp, is_arb =
        if Option.is_none exp_opt then (mk_arbitrary_exp (), false)
        else (Option.value_exn exp_opt, true)
      in
      let acc', is_arb' = fold_patch facts patch_exps abs_exp exp acc in
      (exp, acc', is_arb || is_arb')
  | _ -> L.error "non-Exp node in abs_exp2chc"

and fold_patch facts patch_exps abs_exp parent acc =
  match abs_exp with
  | AbsDiff.SBinOp (op, e1, e2, _) ->
      let (e1', is_arb1), acc1 =
        if AbsDiff.is_selv e1.ast then (abs_lv2chc facts patch_exps e1.ast, acc)
        else
          let e1'', acc', is_arb = abs_exp2chc facts patch_exps e1 acc in
          ((e1'', is_arb), acc')
      in
      let (e2', is_arb2), acc2 =
        if AbsDiff.is_selv e2.ast then (abs_lv2chc facts patch_exps e2.ast, acc1)
        else
          let e2'', acc', is_arb = abs_exp2chc facts patch_exps e2 acc1 in
          ((e2'', is_arb), acc')
      in
      let chc_op = absbinop2chcop op in
      (Chc.add (Chc.Elt.binop parent chc_op e1' e2') acc2, is_arb1 || is_arb2)
  | SUnOp (op, e, _) ->
      let (e', is_arb), acc' =
        if AbsDiff.is_selv e.ast then (abs_lv2chc facts patch_exps e.ast, acc)
        else
          let e'', acc', is_arb' = abs_exp2chc facts patch_exps e acc in
          ((e'', is_arb'), acc')
      in
      if is_arbitrary_exp e' then (acc, false)
      else
        let chc_op = absunop2chcop op in
        (Chc.add (Chc.Elt.unop parent chc_op e') acc', is_arb)
  | SELval lv_node ->
      let _, acc', is_arb = abs_exp2chc facts patch_exps lv_node acc in
      (acc', is_arb)
  | SConst _ | SSizeOf _ | SSizeOfE _ | SSizeOfStr _ | SQuestion _ | SCastE _
  | SAddrOf _ | SAddrOfLabel _ | SStartOf _ | SENULL ->
      (acc, false)

let patch2chc facts abs_diff patch_exps n snk =
  let guard_cond_opt = AbsDiff.get_guard_cond_opt abs_diff in
  if Option.is_none guard_cond_opt then
    Chc.singleton (Chc.Elt.duedge n snk)
    |> Chc.add (mk_arbitrary_exp () |> Chc.Elt.assume n)
  else
    let guard_cond = Option.value_exn guard_cond_opt in
    let cond_exp, patch_chc, is_contain_sym =
      abs_exp2chc facts patch_exps guard_cond Chc.empty
    in
    let out_chc =
      Chc.singleton (Chc.Elt.assume n cond_exp) |> Chc.union patch_chc
    in
    if is_contain_sym then out_chc
    else Chc.singleton (Chc.Elt.duedge n snk) |> Chc.union out_chc

let gen_patpat abs_diff snk facts =
  let n = mk_arbitrary_node () in
  if List.exists ~f:AbsDiff.is_guard_patch abs_diff then
    let patch_exps = comps_of_facts facts in
    patch2chc facts abs_diff patch_exps n snk |> Chc.union facts
  else
    let e = mk_arbitrary_exp () in
    Chc.add (Chc.Elt.duedge n snk) facts |> Chc.add (Chc.Elt.assume n e)

let mk_weak_pattern maps dug patch_comps alarm_exps alarm_lvs src snk facts
    abs_diff cmd =
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  let abs_facts, abs_diff' =
    abs_by_comps maps dug patch_comps snk alarm_exps alarm_lvs facts abs_diff
      cmd
  in
  L.info "Original Pattern - %s" (num_of_rels abs_facts);
  let pattern_in_numeral =
    Chc.Elt.Implies (abs_facts |> Chc.to_list, errtrace)
  in
  let patpat =
    Chc.Elt.Implies (gen_patpat abs_diff snk abs_facts |> Chc.to_list, errtrace)
    |> Chc.Elt.numer2var |> Chc.singleton
  in
  let snk_func = Utils.get_func_name_from_node snk in
  let alt_pc, alt_diff = find_alt_lvs snk_func facts patch_comps abs_diff in
  let alt_pat =
    if Chc.is_empty alt_pc then []
    else
      let alt_facts, alt_diff' =
        abs_by_comps ~new_ad:true maps dug alt_pc snk alarm_exps alarm_lvs facts
          alt_diff cmd
      in
      L.info "Alternative Pattern - %s" (num_of_rels alt_facts);
      let alt_pattern_in_numeral =
        Chc.Elt.Implies (alt_facts |> Chc.to_list, errtrace)
      in
      let alt_patpat =
        Chc.Elt.Implies
          (gen_patpat abs_diff snk alt_facts |> Chc.to_list, errtrace)
        |> Chc.Elt.numer2var |> Chc.singleton
      in
      [
        ( alt_pattern_in_numeral |> Chc.singleton,
          alt_pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
          alt_patpat,
          alt_diff' );
      ]
  in
  ( ( pattern_in_numeral |> Chc.singleton,
      pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
      patpat,
      abs_diff' )
    :: alt_pat,
    true )

let mk_strong_pattern maps dug patch_comps alarm_exps alarm_lvs src snk facts
    abs_diff cmd =
  let errtrace =
    Chc.Elt.FuncApply
      ("ErrTrace", [ Chc.Elt.FDNumeral src; Chc.Elt.FDNumeral snk ])
  in
  Z3env.buggy_src := src;
  Z3env.buggy_snk := snk;
  (* split or make it somehow return differently depending on the cmd *)
  let full_facts, abs_facts, abs_diff', full_alt_facts, alt_facts, alt_diff' =
    mk_patterns maps dug patch_comps src snk alarm_exps alarm_lvs facts abs_diff
      cmd
  in
  L.info "Full Pattern - %s" (num_of_rels full_facts);
  let full_pattern_in_numeral =
    Chc.Elt.Implies (full_facts |> Chc.to_list, errtrace)
  in
  let full_patpat =
    Chc.Elt.Implies (gen_patpat abs_diff snk full_facts |> Chc.to_list, errtrace)
    |> Chc.Elt.numer2var |> Chc.singleton
  in
  L.info "Full Alternative Pattern - %s" (num_of_rels full_alt_facts);
  let full_alt_pattern_in_numeral =
    Chc.Elt.Implies (full_alt_facts |> Chc.to_list, errtrace)
  in
  let full_alt_patpat =
    Chc.Elt.Implies
      (gen_patpat abs_diff snk full_alt_facts |> Chc.to_list, errtrace)
    |> Chc.Elt.numer2var |> Chc.singleton
  in
  L.info "Abstract Pattern - %s" (num_of_rels abs_facts);
  let pattern_in_numeral =
    Chc.Elt.Implies (abs_facts |> Chc.to_list, errtrace)
  in
  let patpat =
    Chc.Elt.Implies (gen_patpat abs_diff snk abs_facts |> Chc.to_list, errtrace)
    |> Chc.Elt.numer2var |> Chc.singleton
  in
  let alt_pat =
    if Chc.is_empty alt_facts then []
    else (
      L.info "Alternative Pattern - %s" (num_of_rels alt_facts);
      let alt_pattern_in_numeral =
        Chc.Elt.Implies (alt_facts |> Chc.to_list, errtrace)
      in
      let alt_patpat =
        Chc.Elt.Implies
          (gen_patpat abs_diff snk alt_facts |> Chc.to_list, errtrace)
        |> Chc.Elt.numer2var |> Chc.singleton
      in
      [
        ( alt_pattern_in_numeral |> Chc.singleton,
          alt_pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
          alt_patpat,
          alt_diff' );
      ])
  in
  let full_pat =
    ( full_pattern_in_numeral |> Chc.singleton,
      full_pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
      full_patpat,
      abs_diff' )
  in
  let full_alt_pat =
    ( full_alt_pattern_in_numeral |> Chc.singleton,
      full_alt_pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
      full_alt_patpat,
      alt_diff' )
  in
  let abs_pat =
    ( pattern_in_numeral |> Chc.singleton,
      pattern_in_numeral |> Chc.Elt.numer2var |> Chc.singleton,
      patpat,
      abs_diff' )
  in
  let abs, _, _, _ = abs_pat in
  let patterns_in_use =
    if Chc.cardinal abs_facts <= 15 || List.is_empty alt_pat then
      [ full_pat; full_alt_pat ]
    else abs_pat :: alt_pat
  in
  let is_altpat_eq_abspat =
    if List.is_empty alt_pat then false
    else
      let alt, _, _, _ = alt_pat |> List.hd_exn in
      Chc.fold
        (fun elt acc -> acc && Chc.exists (fun e -> Chc.Elt.equal e elt) abs)
        alt true
  in
  (patterns_in_use, not is_altpat_eq_abspat)

let run maps dug patch_comps alarm_exps alarm_lvs src snk facts abs_diff cmd
    is_strong_pat =
  if is_strong_pat then
    mk_strong_pattern maps dug patch_comps alarm_exps alarm_lvs src snk facts
      abs_diff cmd
  else
    mk_weak_pattern maps dug patch_comps alarm_exps alarm_lvs src snk facts
      abs_diff cmd
