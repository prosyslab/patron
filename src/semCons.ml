open Core
open Z3utils
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module L = Logger

type t =
  | Lt of t * t
  | Gt of t * t
  | FuncApply of string * t list
  | Add of t list
  | Mul of t list
  | Var of string
  | Const of Z.t

let rec parse_sem_cons = function
  | Sexp.List [ Sexp.Atom "<"; e1; e2 ] ->
      Lt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom ">"; e1; e2 ] ->
      Gt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List (Sexp.Atom "+" :: es) -> Add (List.map ~f:parse_sem_cons es)
  | Sexp.List (Sexp.Atom "*" :: es) -> Mul (List.map ~f:parse_sem_cons es)
  | Sexp.List (Sexp.Atom f :: es) -> FuncApply (f, List.map ~f:parse_sem_cons es)
  | Sexp.Atom s -> ( try Const (Z.of_string s) with _ -> Var s)
  | _ -> failwith "Unsupported Sexp"

type mode = Var | Numer

let rec sc2z3 mode maps = function
  | Lt (sc1, sc2) ->
      Z3.Arithmetic.mk_lt z3env.z3ctx (sc2z3 mode maps sc1)
        (sc2z3 mode maps sc2)
  | Gt (sc1, sc2) ->
      Z3.Arithmetic.mk_gt z3env.z3ctx (sc2z3 mode maps sc1)
        (sc2z3 mode maps sc2)
  | FuncApply ("SizeOf", args) ->
      Z3.FuncDecl.apply z3env.sizeof (List.map ~f:(sc2z3 mode maps) args)
  | FuncApply ("StrLen", args) ->
      Z3.FuncDecl.apply z3env.strlen (List.map ~f:(sc2z3 mode maps) args)
  | FuncApply ("IntVal", args) ->
      Z3.FuncDecl.apply z3env.intval (List.map ~f:(sc2z3 mode maps) args)
  | Add scs ->
      Z3.Arithmetic.mk_add z3env.z3ctx (List.map ~f:(sc2z3 mode maps) scs)
  | Mul scs ->
      Z3.Arithmetic.mk_mul z3env.z3ctx (List.map ~f:(sc2z3 mode maps) scs)
  | Var s -> (
      match mode with
      | Var -> Z3.Expr.mk_const_s z3env.z3ctx s z3env.value
      | Numer -> Facts.mk_numer false maps s z3env.value)
  | Const i -> Z3.Arithmetic.Integer.mk_numeral_s z3env.z3ctx (Z.to_string i)
  | _ -> failwith "Unsupported Semantic Constraint"

module AlarmMap = Map.Make (struct
  type t = String.t * String.t

  let compare (s1, t1) (s2, t2) =
    let cmp = String.compare s1 s2 in
    if cmp = 0 then String.compare t1 t2 else cmp
end)
(* (src node id, snk node id) -> error constraint *)

let mk_alarm_map work_dir =
  let io_err_cons_file =
    Filename.concat work_dir "sparrow-out/taint/datalog/IOErrorConstraint.facts"
  in
  try
    let alarms =
      In_channel.read_lines io_err_cons_file
      |> List.map ~f:(fun alarm ->
             match String.split ~on:'\t' alarm with
             | [ src; snk; err_cons ] -> (src, snk, err_cons)
             | _ -> L.error ~to_console:true "mk_alarm_map: invalid format")
    in
    List.fold_left ~init:AlarmMap.empty
      ~f:(fun am (src, snk, err_cons) ->
        AlarmMap.add (src, snk) (Sexp.of_string err_cons |> parse_sem_cons) am)
      alarms
  with _ ->
    Logger.debug "Empty Semantic Constraint";
    AlarmMap.empty

let make ?(add_var_too = false) maps solver work_dir =
  let alarm_map = mk_alarm_map work_dir in
  let (src, snk), sem_cons = AlarmMap.choose alarm_map in
  let sc_numer = sc2z3 Numer maps sem_cons in
  Z3.Fixedpoint.add_rule solver sc_numer None;
  let src_numer = Hashtbl.find maps.node_map src in
  let snk_numer = Hashtbl.find maps.node_map snk in
  add_fact solver z3env.alarm [ src_numer; snk_numer ];
  if add_var_too then (
    let sc_var = sc2z3 Var maps sem_cons in
    Z3.Fixedpoint.add_rule z3env.pattern_solver sc_var None;
    let src_var = Z3.Expr.mk_const_s z3env.z3ctx src z3env.node in
    let snk_var = Z3.Expr.mk_const_s z3env.z3ctx snk z3env.node in
    add_fact z3env.pattern_solver z3env.alarm [ src_var; snk_var ])
