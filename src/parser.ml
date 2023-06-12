open Core
open Z3env
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module L = Logger

let mk_term s =
  if
    String.equal s "+" || String.equal s "-" || Z3utils.is_binop s
    || Z3utils.is_unop s
  then Chc.FDNumeral s
  else
    try Const (Z.of_string s)
    with _ ->
      let splitted = String.split ~on:'-' s in
      if List.length splitted = 1 then Var s else FDNumeral s

let file2func = function
  | "AllocExp.facts" -> "Alloc"
  | "Arg.facts" -> "Arg"
  | "Set.facts" -> "Set"
  | "BinOpExp.facts" -> "BinOp"
  | "UnOpExp.facts" -> "UnOp"
  | "CallExp.facts" -> "Call"
  | "CFPath.facts" -> "CFPath"
  | "DUPath.facts" -> "DUPath"
  | "GlobalVar.facts" | "LocalVar.facts" -> "Var"
  | "LibCallExp.facts" -> "LibCall"
  | "LvalExp.facts" -> "LvalExp"
  | "Return.facts" -> "Return"
  | "SAllocExp.facts" -> "SAlloc"
  | "Skip.facts" -> "Skip"
  | _ -> L.error "file2func: wrong filename"

let parse_facts datalog_dir fact_file =
  let func_name = file2func fact_file in
  let fact_file_path = Filename.concat datalog_dir fact_file in
  In_channel.read_lines fact_file_path
  |> List.map ~f:(fun line ->
         let args = String.split ~on:'\t' line |> List.map ~f:mk_term in
         Chc.FuncApply (func_name, args))
  |> Chc.of_list

let make_facts work_dir =
  let datalog_dir = Filename.concat work_dir "sparrow-out/taint/datalog" in
  List.fold_left ~init:Chc.empty
    ~f:(fun facts file -> parse_facts datalog_dir file |> Chc.union facts)
    z3env.fact_files

let rec parse_sem_cons = function
  | Sexp.List [ Sexp.Atom "Lt"; e1; e2 ] ->
      Chc.CLt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "Gt"; e1; e2 ] ->
      CGt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "Le"; e1; e2 ] ->
      CLe (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "Ge"; e1; e2 ] ->
      CGe (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "Eq"; e1; e2 ] ->
      CEq (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "Ne"; e1; e2 ] ->
      CNe (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "%"; e1; e2 ] ->
      Mod (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "<"; e1; e2 ] ->
      Lt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom ">"; e1; e2 ] ->
      Gt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "<="; e1; e2 ] ->
      Le (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom ">="; e1; e2 ] ->
      Ge (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "="; e1; e2 ] ->
      Eq (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "!="; e1; e2 ] ->
      Ne (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "+"; e1; e2 ] ->
      Add (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "-"; e1; e2 ] ->
      Sub (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "*"; e1; e2 ] ->
      Mul (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "/"; e1; e2 ] ->
      Div (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom "BNot"; e ] -> CBNot (parse_sem_cons e)
  | Sexp.List [ Sexp.Atom "LNot"; e ] -> CLNot (parse_sem_cons e)
  | Sexp.List [ Sexp.Atom "Neg"; e ] -> CNeg (parse_sem_cons e)
  | Sexp.List [ Sexp.Atom "not"; e ] -> Not (parse_sem_cons e)
  | Sexp.List (Sexp.Atom f :: es) -> FuncApply (f, List.map ~f:parse_sem_cons es)
  | Sexp.Atom s -> mk_term s
  | _ -> failwith "Unsupported Sexp"

let rec parse_sem_rules = function
  | Sexp.List (hd :: tl) ->
      Chc.Implies (List.map ~f:parse_sem_cons tl, parse_sem_cons hd)
  | _ -> failwith "Unsupported Sexp"

module AlarmMap = Map.Make (struct
  type t = String.t * String.t

  let compare (s1, t1) (s2, t2) =
    let cmp = String.compare s1 s2 in
    if cmp = 0 then String.compare t1 t2 else cmp
end)
(* (src node id, snk node id) -> error constraint *)

let mk_alarm_map work_dir =
  let io_err_cons_file =
    Filename.concat work_dir "sparrow-out/taint/datalog/IOErrorConstraint.rules"
  in
  try
    let alarms =
      In_channel.read_lines io_err_cons_file
      |> List.map ~f:(fun alarm ->
             match String.split ~on:'\t' alarm with
             | [ src; snk; err_rule ] -> (src, snk, err_rule)
             | _ -> L.error ~to_console:true "mk_alarm_map: invalid format")
    in
    List.fold_left ~init:AlarmMap.empty
      ~f:(fun am (src, snk, err_rule) ->
        AlarmMap.add (src, snk) (Sexp.of_string err_rule |> parse_sem_rules) am)
      alarms
  with _ ->
    Logger.debug "Empty Semantic Constraint";
    AlarmMap.empty

let make_rules work_dir =
  let sem_rule_file =
    Filename.concat work_dir "sparrow-out/taint/datalog/Sem.rules"
  in
  (* let vars =
       [ "x"; "x1"; "x2"; "y" ]
       |> List.map ~f:(fun s -> Z3.Expr.mk_const_s z3env.z3ctx s z3env.bv_sort)
     in *)
  In_channel.read_lines sem_rule_file
  |> List.map ~f:(fun rule -> Sexp.of_string rule |> parse_sem_rules)
  |> Chc.of_list

let make work_dir = Chc.union (make_facts work_dir) (make_rules work_dir)
