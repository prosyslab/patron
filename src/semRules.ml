open Core
open Z3utils
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module L = Logger

type t =
  | Lt of t * t
  | Gt of t * t
  | Le of t * t
  | Ge of t * t
  | Eq of t * t
  | Ne of t * t
  | Not of t
  | CLt of t * t
  | CGt of t * t
  | CLe of t * t
  | CGe of t * t
  | CEq of t * t
  | CNe of t * t
  | CBNot of t
  | CLNot of t
  | CNeg of t
  | FuncApply of string * t list
  | Add of t * t
  | Mul of t * t
  | Sub of t * t
  | Div of t * t
  | Mod of t * t
  | Var of string
  | Const of Z.t
  | Implies of t list * t

let rec parse_sem_cons = function
  | Sexp.List [ Sexp.Atom "Lt"; e1; e2 ] ->
      CLt (parse_sem_cons e1, parse_sem_cons e2)
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
  | Sexp.Atom s -> ( try Const (Z.of_string s) with _ -> Var s)
  | _ -> failwith "Unsupported Sexp"

let rec parse_sem_rules = function
  | Sexp.List (hd :: tl) ->
      Implies (List.map ~f:parse_sem_cons tl, parse_sem_cons hd)
  | _ -> failwith "Unsupported Sexp"

type mode = Var | Numer

let rec sr2z3 mode maps = function
  | Lt (e1, e2) ->
      Z3.Arithmetic.mk_lt z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Gt (e1, e2) ->
      Z3.Arithmetic.mk_gt z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Le (e1, e2) ->
      Z3.Arithmetic.mk_le z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Ge (e1, e2) ->
      Z3.Arithmetic.mk_ge z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Eq (e1, e2) ->
      Z3.Boolean.mk_eq z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Ne (e1, e2) ->
      Z3.Boolean.mk_not z3env.z3ctx
        (Z3.Boolean.mk_eq z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2))
  | Not e -> Z3.Boolean.mk_not z3env.z3ctx (sr2z3 mode maps e)
  | CLt (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.Arithmetic.mk_lt z3env.z3ctx (sr2z3 mode maps e1)
           (sr2z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CGt (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.BitVector.mk_sgt z3env.z3ctx (sr2z3 mode maps e1)
           (sr2z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CLe (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.BitVector.mk_sle z3env.z3ctx (sr2z3 mode maps e1)
           (sr2z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CGe (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.BitVector.mk_sge z3env.z3ctx (sr2z3 mode maps e1)
           (sr2z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CEq (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.Boolean.mk_eq z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CNe (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.Boolean.mk_eq z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
  | CBNot e -> Z3.BitVector.mk_not z3env.z3ctx (sr2z3 mode maps e)
  | CLNot e ->
      let zero = Z3.BitVector.mk_numeral z3env.z3ctx "0" 64 in
      let one = Z3.BitVector.mk_numeral z3env.z3ctx "1" 64 in
      let is_zero = Z3.Boolean.mk_eq z3env.z3ctx (sr2z3 mode maps e) zero in
      Z3.Boolean.mk_ite z3env.z3ctx is_zero one zero
  | CNeg e -> Z3.BitVector.mk_neg z3env.z3ctx (sr2z3 mode maps e)
  | FuncApply (f, args) ->
      L.debug "Func: %s" f;
      Z3.FuncDecl.apply (Z3utils.match_func f)
        (List.map ~f:(sr2z3 mode maps) args)
  | Add (e1, e2) ->
      Z3.BitVector.mk_add z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Sub (e1, e2) ->
      Z3.BitVector.mk_sub z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Mul (e1, e2) ->
      Z3.BitVector.mk_mul z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Div (e1, e2) ->
      Z3.BitVector.mk_sdiv z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Mod (e1, e2) ->
      Z3.BitVector.mk_smod z3env.z3ctx (sr2z3 mode maps e1) (sr2z3 mode maps e2)
  | Var x -> (
      let sort = Z3utils.match_sort x in
      match mode with
      | Var -> Z3.Expr.mk_const_s z3env.z3ctx x sort
      | Numer ->
          if Z3.Sort.equal sort z3env.bv_sort then
            Z3.Expr.mk_const_s z3env.z3ctx x sort
          else Facts.mk_numer false maps x (Z3utils.match_sort x))
  | Const i ->
      Z3.BitVector.mk_numeral z3env.z3ctx (Z.to_int i |> string_of_int) 64
  | Implies (tl, hd) ->
      let cons =
        Z3.Boolean.mk_and z3env.z3ctx (List.map ~f:(sr2z3 mode maps) tl)
      in
      Z3.Boolean.mk_implies z3env.z3ctx cons (sr2z3 mode maps hd)
(* | Eq (sc1, sc2) ->
       Z3.Boolean.mk_eq z3env.z3ctx (sc2z3 mode maps sc1) (sc2z3 mode maps sc2)
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
   | FuncApply ("Val", args) ->
       Z3.FuncDecl.apply z3env.intval (List.map ~f:(sc2z3 mode maps) args)
   | Add scs ->
       Z3.Arithmetic.mk_add z3env.z3ctx (List.map ~f:(sc2z3 mode maps) scs)
   | Mul scs ->
       Z3.Arithmetic.mk_mul z3env.z3ctx (List.map ~f:(sc2z3 mode maps) scs)
   | Var s -> (
       match mode with
       | Var -> Z3.Expr.mk_const_s z3env.z3ctx s z3env.value
       | Numer -> Facts.mk_numer false maps s z3env.value)
   | Const i -> Z3.Arithmetic.Integer.mk_numeral_s z3env.z3ctx (Z.to_string i) *)

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

let make maps solver work_dir =
  let sem_rule_file =
    Filename.concat work_dir "sparrow-out/taint/datalog/Sem.rules"
  in
  let vars =
    [ "x"; "x1"; "x2"; "y" ]
    |> List.map ~f:(fun s -> Z3.Expr.mk_const_s z3env.z3ctx s z3env.bv_sort)
  in
  In_channel.read_lines sem_rule_file
  |> List.iter ~f:(fun rule ->
         Sexp.of_string rule |> parse_sem_rules |> sr2z3 Numer maps
         |> mk_rule z3env.z3ctx vars
         |> (Fun.flip (Z3.Fixedpoint.add_rule solver)) None)