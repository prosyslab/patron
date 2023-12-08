open Core
open Z3env
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module L = Logger
module Sys = Stdlib.Sys

module ASTMap = struct
  module Key = struct
    type t = Cil.stmt

    let compare x y =
      String.compare (Utils.string_of_stmt x) (Utils.string_of_stmt y)
  end

  module M = Map.Make (Key)

  type t = string M.t

  let make_map stmts =
    let _, map =
      List.fold_left ~init:(1, M.empty)
        ~f:(fun (id, map) stmt ->
          let next_id = id + 1 in
          (next_id, M.add stmt (id |> string_of_int) map))
        stmts
    in
    map
end

let parse_ast target_dir =
  let file = Utils.get_target_file target_dir in
  if !Cilutil.printStages then ignore ();
  let cil = Frontc.parse file () in
  if not (Feature.enabled "epicenter") then Rmtmps.removeUnusedTemps cil;
  cil

let numer_cnt = ref 25

let update_numer name =
  match name with
  | "Exp" | "CallExp" | "LibCallExp" | "SallocExp" | "AllocExp" ->
      expr_numer_cnt := !numer_cnt
  | "Lval" -> lval_numer_cnt := !numer_cnt
  | "Val" -> value_numer_cnt := !numer_cnt
  | "ArgList" -> arg_list_numer_cnt := !numer_cnt
  | "Loc" -> loc_numer_cnt := !numer_cnt
  | "Pos" -> pos_numer_cnt := !numer_cnt
  | _ -> node_numer_cnt := !numer_cnt

let mk_term s =
  if Z3utils.is_binop s || Z3utils.is_unop s then Chc.Elt.FDNumeral s
  else
    try Chc.Elt.Const (Z.of_string s)
    with _ ->
      let splitted = String.split ~on:'-' s in
      if List.length splitted = 1 then Chc.Elt.Var s
      else (
        incr numer_cnt;
        let name = List.hd_exn splitted in
        update_numer name;
        Chc.Elt.FDNumeral s)

(* TODO: Add Assume.facts *)
let file2func = function
  | "AllocExp.facts" -> "Alloc"
  | "Arg.facts" -> "Arg"
  | "Set.facts" -> "Set"
  | "BinOpExp.facts" -> "BinOp"
  | "UnOpExp.facts" -> "UnOp"
  | "CallExp.facts" -> "Call"
  | "CFPath.facts" -> "CFPath"
  (* | "DetailedDUEdge.facts" -> "DUEdge" *)
  | "DUEdge.facts" -> "DUEdge"
  | "DUPath.facts" -> "DUPath"
  | "GlobalVar.facts" | "LocalVar.facts" -> "Var"
  | "LibCallExp.facts" -> "LibCall"
  | "LvalExp.facts" -> "LvalExp"
  | "Return.facts" -> "Return"
  | "SAllocExp.facts" -> "SAlloc"
  | "Skip.facts" -> "Skip"
  | "EvalLv.facts" -> "EvalLv"
  | "Assume.facts" -> "Assume"
  | f -> L.error "file2func - wrong filename: %s" f

let parse_cf_facts datalog_dir fact_file =
  let func_name = file2func fact_file in
  let fact_file_path = Filename.concat datalog_dir fact_file in
  let elt_lst, facts =
    In_channel.read_lines fact_file_path
    |> List.fold_left ~init:([], Utils.StrMap.empty) ~f:(fun (lst, map) line ->
           let arg_lst = String.split ~on:'\t' line in
           let args = List.map ~f:mk_term arg_lst in
           let elt = Chc.Elt.FuncApply (func_name, args) in
           let map =
             Utils.StrMap.add (List.hd_exn arg_lst) (List.tl_exn arg_lst) map
           in
           (elt :: lst, map))
  in
  (List.rev elt_lst |> Chc.of_list, (func_name, facts))

(* TODO: combine symdiff making process and make_cf_facts wrt the file IO *)
let make_cf_facts work_dir cfg map =
  let cf_facts, facts_map =
    List.fold_left ~init:(Chc.empty, [])
      ~f:(fun (facts, lst) file ->
        let chc, fact_map = parse_cf_facts work_dir file in
        (Chc.union facts chc, fact_map :: lst))
      Z3env.fact_files
  in
  Maps.CfgNode.parse_sparrow cfg map facts_map;
  cf_facts

let rec sexp2chc = function
  | Sexp.List [ Sexp.Atom "Lt"; e1; e2 ] ->
      Chc.Elt.CLt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Gt"; e1; e2 ] -> CGt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Le"; e1; e2 ] -> CLe (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Ge"; e1; e2 ] -> CGe (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Eq"; e1; e2 ] -> CEq (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Ne"; e1; e2 ] -> CNe (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvshl"; e1; e2 ] -> BvShl (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvshr"; e1; e2 ] -> BvShr (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvand"; e1; e2 ] -> BvAnd (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvor"; e1; e2 ] -> BvOr (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvxor"; e1; e2 ] -> BvXor (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "<"; e1; e2 ] -> Lt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom ">"; e1; e2 ] -> Gt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "<="; e1; e2 ] -> Le (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom ">="; e1; e2 ] -> Ge (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "PlusPI"; _; _ ] ]
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "IndexPI"; _; _ ] ]
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "MinusPI"; _; _ ] ]
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "MinusPP"; _; _ ] ] ->
      Eq (Var "y", Var "y")
  | Sexp.List [ Sexp.Atom "="; e1; e2 ] -> Eq (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "!="; e1; e2 ] -> Ne (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "PlusA"; e1; e2 ] -> Add (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "MinusA"; e1; e2 ] -> Sub (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Mult"; e1; e2 ] -> Mul (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Div"; e1; e2 ] -> Div (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Mod"; e1; e2 ] -> Mod (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "and"; e1; e2 ] -> And (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "or"; e1; e2 ] -> Or (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "BNot"; e ] -> CBNot (sexp2chc e)
  | Sexp.List [ Sexp.Atom "LNot"; e ] -> CLNot (sexp2chc e)
  | Sexp.List [ Sexp.Atom "Neg"; e ] -> CNeg (sexp2chc e)
  | Sexp.List [ Sexp.Atom "not"; e ] -> Not (sexp2chc e)
  | Sexp.List (Sexp.Atom f :: es) -> FuncApply (f, List.map ~f:sexp2chc es)
  | Sexp.List ((Sexp.List (Sexp.Atom _ :: _) as hd) :: tl) ->
      Implies (List.map ~f:sexp2chc tl, sexp2chc hd)
  | Sexp.Atom s -> mk_term s
  | _ -> failwith "Unsupported Sexp"

let parse_chc chc_file =
  In_channel.read_lines chc_file
  |> List.fold_left ~init:[] ~f:(fun chc_list rule ->
         try (Sexp.of_string rule |> sexp2chc) :: chc_list with _ -> chc_list)
  |> Chc.of_list

let mk_parent_tuples parent stmts =
  List.fold_left ~init:[] ~f:(fun acc s -> (parent, s) :: acc) stmts

let match_eq_nodes ast_node cfg ast_map =
  let ast_id = Hashtbl.find ast_map ast_node |> string_of_int in
  let cfg_id =
    Hashtbl.fold
      (fun cnode id acc ->
        let bool =
          match (ast_node.Cil.skind, cnode) with
          | Cil.Instr i, cn -> (
              match (List.hd_exn i, cn) with
              | Cil.Call (_, _, _, loc), Maps.CfgNode.CCall (_, _, cloc) ->
                  SymDiff.SDiff.eq_line loc cloc
              | Cil.Set (_, _, loc), Maps.CfgNode.CSet (_, _, cloc)
              | Cil.Set (_, _, loc), Maps.CfgNode.CAlloc (_, _, cloc)
              | Cil.Set (_, _, loc), Maps.CfgNode.CSalloc (_, _, cloc)
              | Cil.Set (_, _, loc), Maps.CfgNode.CFalloc (_, _, cloc) ->
                  SymDiff.SDiff.eq_line loc cloc
              | _ -> false)
          | Cil.If (_, _, _, loc), Maps.CfgNode.CIf cloc ->
              SymDiff.SDiff.eq_line loc cloc
          | Cil.Return (_, loc), Maps.CfgNode.CReturn1 (_, cloc)
          | Cil.Return (_, loc), Maps.CfgNode.CReturn2 cloc ->
              SymDiff.SDiff.eq_line loc cloc
          | _ -> false
        in
        if bool then id :: acc else acc)
      cfg []
    |> List.hd_exn
  in
  Chc.Elt.FuncApply ("EqNode", [ FDNumeral cfg_id; FDNumeral ast_id ])

let make_ast_facts (maps : Maps.t) stmts =
  let parent_tups =
    List.fold_left ~init:[]
      ~f:(fun acc s ->
        match s.Cil.skind with
        | Cil.Block b | Cil.Loop (b, _, _, _) ->
            mk_parent_tuples s b.bstmts @ acc
        | Cil.If (_, tb, eb, _) ->
            mk_parent_tuples s tb.bstmts @ mk_parent_tuples s eb.bstmts @ acc
        | _ -> acc)
      stmts
    |> List.fold_left ~init:[] ~f:(fun acc (parent, child) ->
           let parent = Hashtbl.find maps.ast_map parent |> string_of_int in
           let child = Hashtbl.find maps.ast_map child |> string_of_int in
           (parent, child) :: acc)
  in
  let parent_rel =
    List.fold_left ~init:[]
      ~f:(fun acc (parent, child) ->
        Chc.Elt.FuncApply ("AstParent", [ FDNumeral parent; FDNumeral child ])
        :: acc)
      parent_tups
    |> Chc.of_list
  in
  let eqnode_rel =
    List.fold_left ~init:[]
      ~f:(fun acc stmt -> match_eq_nodes stmt maps.cfg_map maps.ast_map :: acc)
      stmts
    |> Chc.of_list
  in
  Chc.union parent_rel eqnode_rel

let read_and_split file =
  In_channel.read_lines file |> List.map ~f:(fun l -> String.split ~on:'\t' l)

exception Not_impl_aexp

let get_aexp alarm splited filename =
  match Filename.basename filename |> Filename.chop_extension with
  | "AlarmDivExp" -> (
      match splited with
      | [ a; _; divisor ] when String.equal a alarm ->
          Chc.singleton (Chc.Elt.FDNumeral divisor)
      | _ -> Chc.empty)
  | f ->
      Logger.warn "get_aexp - not implemented: %s" f;
      raise Not_impl_aexp

let get_alarm work_dir =
  let src, snk, alarm =
    match
      Filename.concat work_dir "SparrowAlarm.facts"
      |> read_and_split |> List.hd_exn
    with
    | [ src; snk; alarm_id ] -> (src, snk, alarm_id)
    | _ -> L.error ~to_console:true "get_alarm: invalid format"
  in
  let alarm_exp_files =
    Sys.readdir work_dir
    |> Array.filter ~f:(fun f ->
           Filename.basename f
           |> String.is_substring_at ~pos:0 ~substring:"Alarm")
  in
  let aexps =
    Array.fold
      ~f:(fun aexps file ->
        match Filename.concat work_dir file |> read_and_split with
        | hd :: [] -> get_aexp alarm hd file
        | [] -> aexps
        | _ -> aexps (* TEMP *))
      ~init:Chc.empty alarm_exp_files
  in
  (src, snk, aexps)

let make_facts buggy_dir target_alarm ast cfg out_dir (maps : Maps.t) =
  let alarm_dir =
    Filename.concat buggy_dir ("sparrow-out/taint/datalog/" ^ target_alarm)
  in
  Utils.parse_map alarm_dir maps.exp_map;
  let stmts = Utils.extract_stmts ast in
  Maps.make_ast_map stmts maps.ast_map;
  let facts =
    (* Chc.union
       (make_ast_facts stmts
       maps) *)
    make_cf_facts alarm_dir cfg maps.cfg_map
  in
  Chc.pretty_dump (Filename.concat out_dir target_alarm) facts;
  Chc.sexp_dump (Filename.concat out_dir target_alarm) facts;
  (facts, get_alarm alarm_dir)
