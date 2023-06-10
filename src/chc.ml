open Core
open Z3env
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module Set = Stdlib.Set
module L = Logger
module F = Format

type chc =
  | Lt of chc * chc
  | Gt of chc * chc
  | Le of chc * chc
  | Ge of chc * chc
  | Eq of chc * chc
  | Ne of chc * chc
  | Not of chc
  | CLt of chc * chc
  | CGt of chc * chc
  | CLe of chc * chc
  | CGe of chc * chc
  | CEq of chc * chc
  | CNe of chc * chc
  | CBNot of chc
  | CLNot of chc
  | CNeg of chc
  | FuncApply of string * chc list
  | Add of chc * chc
  | Mul of chc * chc
  | Sub of chc * chc
  | Div of chc * chc
  | Mod of chc * chc
  | Var of string
  | FDNumeral of string
  | Const of Z.t
  | Implies of chc list * chc

include Set.Make (struct
  type t = chc

  let compare = Stdlib.compare
end)

let rec collect_vars = function
  | Lt (t1, t2)
  | Gt (t1, t2)
  | Le (t1, t2)
  | Ge (t1, t2)
  | Eq (t1, t2)
  | Ne (t1, t2)
  | CLt (t1, t2)
  | CGt (t1, t2)
  | CLe (t1, t2)
  | CGe (t1, t2)
  | CEq (t1, t2)
  | CNe (t1, t2)
  | Add (t1, t2)
  | Mul (t1, t2)
  | Sub (t1, t2)
  | Div (t1, t2)
  | Mod (t1, t2) ->
      union (collect_vars t1) (collect_vars t2)
  | Not t | CBNot t | CLNot t | CNeg t -> collect_vars t
  | FuncApply (_, args) ->
      List.fold_left ~init:empty
        ~f:(fun vars arg -> collect_vars arg |> union vars)
        args
  | Var _ as v -> singleton v
  | FDNumeral _ | Const _ -> empty
  | Implies (cons, hd) ->
      List.fold_left ~init:empty
        ~f:(fun vars c -> collect_vars c |> union vars)
        cons
      |> union (collect_vars hd)

let rec pp_chc fmt = function
  | Lt (t1, t2) -> F.fprintf fmt "(%a < %a)" pp_chc t1 pp_chc t2
  | Gt (t1, t2) -> F.fprintf fmt "(%a > %a)" pp_chc t1 pp_chc t2
  | Le (t1, t2) -> F.fprintf fmt "(%a <= %a)" pp_chc t1 pp_chc t2
  | Ge (t1, t2) -> F.fprintf fmt "(%a >= %a)" pp_chc t1 pp_chc t2
  | Eq (t1, t2) -> F.fprintf fmt "(%a = %a)" pp_chc t1 pp_chc t2
  | Ne (t1, t2) -> F.fprintf fmt "(%a != %a)" pp_chc t1 pp_chc t2
  | Not t -> F.fprintf fmt "(not %a)" pp_chc t
  | CLt (t1, t2) -> F.fprintf fmt "(Lt %a %a)" pp_chc t1 pp_chc t2
  | CGt (t1, t2) -> F.fprintf fmt "(Gt %a %a)" pp_chc t1 pp_chc t2
  | CLe (t1, t2) -> F.fprintf fmt "(Le %a %a)" pp_chc t1 pp_chc t2
  | CGe (t1, t2) -> F.fprintf fmt "(Ge %a %a)" pp_chc t1 pp_chc t2
  | CEq (t1, t2) -> F.fprintf fmt "(Eq %a %a)" pp_chc t1 pp_chc t2
  | CNe (t1, t2) -> F.fprintf fmt "(Ne %a %a)" pp_chc t1 pp_chc t2
  | CBNot t -> F.fprintf fmt "(BNot %a)" pp_chc t
  | CLNot t -> F.fprintf fmt "(LNot %a)" pp_chc t
  | CNeg t -> F.fprintf fmt "(Neg %a)" pp_chc t
  | FuncApply (fn, args) ->
      List.map ~f:(fun arg -> F.asprintf "%a" pp_chc arg) args
      |> String.concat ~sep:" " |> F.fprintf fmt "(%s %s)" fn
  | Add (t1, t2) -> F.fprintf fmt "(%a + %a)" pp_chc t1 pp_chc t2
  | Mul (t1, t2) -> F.fprintf fmt "(%a * %a)" pp_chc t1 pp_chc t2
  | Sub (t1, t2) -> F.fprintf fmt "(%a - %a)" pp_chc t1 pp_chc t2
  | Div (t1, t2) -> F.fprintf fmt "(%a / %a)" pp_chc t1 pp_chc t2
  | Mod (t1, t2) -> F.fprintf fmt "(%a mod %a)" pp_chc t1 pp_chc t2
  | Var s | FDNumeral s -> F.fprintf fmt "%s" s
  | Const i -> F.fprintf fmt "%Ld" (Z.to_int64 i)
  | Implies (cons, hd) as impl ->
      let vars = collect_vars impl in
      let vars_str =
        fold (fun var s -> F.asprintf "%s %a" s pp_chc var) vars ""
      in
      List.map ~f:(fun c -> F.asprintf "%a" pp_chc c) cons
      |> String.concat ~sep:", "
      |> F.fprintf fmt "(\\forall %s.\n  %a <- %s)" vars_str pp_chc hd

let pp fmt chcs = iter (fun chc -> F.fprintf fmt "%a\n" pp_chc chc) chcs

let get_cons = function
  | Implies (cons, _) -> cons
  | _ -> L.error "get_cons: wrong chc"

let rec filter_func_app = function
  | FuncApply _ as c -> singleton c
  | Implies _ as c ->
      get_cons c
      |> List.fold_left ~init:empty ~f:(fun fa c ->
             filter_func_app c |> union fa)
  | _ -> empty

let extract_func_apps chc =
  fold (fun c fa -> filter_func_app c |> union fa) chc empty

let get_args = function
  | FuncApply ("Arg", args)
  | FuncApply ("BinOpExp", args)
  | FuncApply ("UnOpExp", args) ->
      List.hd_exn args :: (List.tl_exn args |> List.tl_exn)
  | FuncApply (_, args) -> args
  | _ -> L.error "get_args: wrong chc"

let add_args_to_terms terms args =
  List.fold_left ~init:terms ~f:(fun terms arg -> add arg terms) args

let all_args_has_dep terms args =
  List.for_all ~f:(fun arg -> mem arg terms) args

let exists_dep_arg terms args = List.exists ~f:(fun arg -> mem arg terms) args

let prop_deps terms = function
  | FuncApply ("CFPath", args) | FuncApply ("DUPath", args) ->
      if all_args_has_dep terms args then (true, terms) else (false, terms)
  | FuncApply ("Eval", args)
  | FuncApply ("EvalLv", args)
  | FuncApply ("Memory", args) ->
      if args |> List.tl_exn |> List.tl_exn |> all_args_has_dep terms then
        (true, add_args_to_terms terms args)
      else (false, terms)
  | FuncApply ("BinOpExp", _) as f ->
      let args = get_args f in
      if List.tl_exn args |> all_args_has_dep terms then
        (true, add_args_to_terms terms args)
      else (false, terms)
  | f ->
      let args = get_args f in
      if List.tl_exn args |> exists_dep_arg terms then
        (true, add (List.hd_exn args) terms)
      else (false, terms)

type mode = Var | Numer

let rec to_z3 mode maps = function
  | Lt (e1, e2) ->
      Z3.Arithmetic.mk_lt z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Gt (e1, e2) ->
      Z3.Arithmetic.mk_gt z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Le (e1, e2) ->
      Z3.Arithmetic.mk_le z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Ge (e1, e2) ->
      Z3.Arithmetic.mk_ge z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Eq (e1, e2) ->
      Z3.Boolean.mk_eq z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Ne (e1, e2) ->
      Z3.Boolean.mk_not z3env.z3ctx
        (Z3.Boolean.mk_eq z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2))
  | Not e -> Z3.Boolean.mk_not z3env.z3ctx (to_z3 mode maps e)
  | CLt (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.Arithmetic.mk_lt z3env.z3ctx (to_z3 mode maps e1)
           (to_z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CGt (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.BitVector.mk_sgt z3env.z3ctx (to_z3 mode maps e1)
           (to_z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CLe (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.BitVector.mk_sle z3env.z3ctx (to_z3 mode maps e1)
           (to_z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CGe (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.BitVector.mk_sge z3env.z3ctx (to_z3 mode maps e1)
           (to_z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CEq (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.Boolean.mk_eq z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
  | CNe (e1, e2) ->
      Z3.Boolean.mk_ite z3env.z3ctx
        (Z3.Boolean.mk_eq z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2))
        (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
        (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
  | CBNot e -> Z3.BitVector.mk_not z3env.z3ctx (to_z3 mode maps e)
  | CLNot e ->
      let zero = Z3.BitVector.mk_numeral z3env.z3ctx "0" 64 in
      let one = Z3.BitVector.mk_numeral z3env.z3ctx "1" 64 in
      let is_zero = Z3.Boolean.mk_eq z3env.z3ctx (to_z3 mode maps e) zero in
      Z3.Boolean.mk_ite z3env.z3ctx is_zero one zero
  | CNeg e -> Z3.BitVector.mk_neg z3env.z3ctx (to_z3 mode maps e)
  | FuncApply (f, args) ->
      L.debug "Func: %s" f;
      Z3.FuncDecl.apply (Z3utils.match_func f)
        (List.map ~f:(to_z3 mode maps) args)
  | Add (e1, e2) ->
      Z3.BitVector.mk_add z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Sub (e1, e2) ->
      Z3.BitVector.mk_sub z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Mul (e1, e2) ->
      Z3.BitVector.mk_mul z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Div (e1, e2) ->
      Z3.BitVector.mk_sdiv z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Mod (e1, e2) ->
      Z3.BitVector.mk_smod z3env.z3ctx (to_z3 mode maps e1) (to_z3 mode maps e2)
  | Var x ->
      let sort = Z3utils.match_sort x in
      Z3.Expr.mk_const_s z3env.z3ctx x sort
  | FDNumeral s ->
      let sort = Z3utils.match_sort s in
      Z3utils.mk_numer maps s sort
  | Const i ->
      Z3.BitVector.mk_numeral z3env.z3ctx (Z.to_int i |> string_of_int) 64
  | Implies (tl, hd) ->
      let cons =
        Z3.Boolean.mk_and z3env.z3ctx (List.map ~f:(to_z3 mode maps) tl)
      in
      Z3.Boolean.mk_implies z3env.z3ctx cons (to_z3 mode maps hd)

let rec numer2var = function
  | Lt (t1, t2) -> Lt (numer2var t1, numer2var t2)
  | Gt (t1, t2) -> Gt (numer2var t1, numer2var t2)
  | Le (t1, t2) -> Le (numer2var t1, numer2var t2)
  | Ge (t1, t2) -> Ge (numer2var t1, numer2var t2)
  | Eq (t1, t2) -> Eq (numer2var t1, numer2var t2)
  | Ne (t1, t2) -> Ne (numer2var t1, numer2var t2)
  | CLt (t1, t2) -> CLt (numer2var t1, numer2var t2)
  | CGt (t1, t2) -> CGt (numer2var t1, numer2var t2)
  | CLe (t1, t2) -> CLe (numer2var t1, numer2var t2)
  | CGe (t1, t2) -> CGe (numer2var t1, numer2var t2)
  | CEq (t1, t2) -> CEq (numer2var t1, numer2var t2)
  | CNe (t1, t2) -> CNe (numer2var t1, numer2var t2)
  | Add (t1, t2) -> Add (numer2var t1, numer2var t2)
  | Mul (t1, t2) -> Mul (numer2var t1, numer2var t2)
  | Sub (t1, t2) -> Sub (numer2var t1, numer2var t2)
  | Div (t1, t2) -> Div (numer2var t1, numer2var t2)
  | Mod (t1, t2) -> Mod (numer2var t1, numer2var t2)
  | Not t -> Not (numer2var t)
  | CBNot t -> CBNot (numer2var t)
  | CLNot t -> CLNot (numer2var t)
  | CNeg t -> CNeg (numer2var t)
  | FuncApply (fn, args) ->
      FuncApply (fn, List.map ~f:(fun arg -> numer2var arg) args)
  | Var _ as v -> v
  | FDNumeral s -> Var s
  | Const _ as c -> c
  | Implies (cons, hd) ->
      Implies (List.map ~f:(fun c -> numer2var c) cons, numer2var hd)
