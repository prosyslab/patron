open Core
open Z3env
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module Set = Stdlib.Set
module L = Logger
module F = Format

module Elt = struct
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
    | BvShl of t * t
    | BvShr of t * t
    | BvAnd of t * t
    | BvOr of t * t
    | BvXor of t * t
    | Var of string
    | FDNumeral of string
    | Const of Z.t
    | Implies of t list * t

  let compare a b =
    match (a, b) with
    | FDNumeral x, FDNumeral y | Var x, Var y -> String.compare x y
    | Const x, Const y -> Z.compare x y
    | _, _ -> Stdlib.compare a b

  let equal a b =
    match (a, b) with
    | FDNumeral x, FDNumeral y | Var x, Var y -> String.equal x y
    | Const x, Const y -> Z.equal x y
    | _, _ -> compare a b = 0

  let rec chc2sexp = function
    | Lt (t1, t2) -> Sexp.List [ Sexp.Atom "<"; chc2sexp t1; chc2sexp t2 ]
    | Gt (t1, t2) -> Sexp.List [ Sexp.Atom ">"; chc2sexp t1; chc2sexp t2 ]
    | Le (t1, t2) -> Sexp.List [ Sexp.Atom "<="; chc2sexp t1; chc2sexp t2 ]
    | Ge (t1, t2) -> Sexp.List [ Sexp.Atom ">="; chc2sexp t1; chc2sexp t2 ]
    | Eq (t1, t2) -> Sexp.List [ Sexp.Atom "="; chc2sexp t1; chc2sexp t2 ]
    | Ne (t1, t2) -> Sexp.List [ Sexp.Atom "!="; chc2sexp t1; chc2sexp t2 ]
    | Not t -> Sexp.List [ Sexp.Atom "not"; chc2sexp t ]
    | CLt (t1, t2) -> Sexp.List [ Sexp.Atom "Lt"; chc2sexp t1; chc2sexp t2 ]
    | CGt (t1, t2) -> Sexp.List [ Sexp.Atom "Gt"; chc2sexp t1; chc2sexp t2 ]
    | CLe (t1, t2) -> Sexp.List [ Sexp.Atom "Le"; chc2sexp t1; chc2sexp t2 ]
    | CGe (t1, t2) -> Sexp.List [ Sexp.Atom "Ge"; chc2sexp t1; chc2sexp t2 ]
    | CEq (t1, t2) -> Sexp.List [ Sexp.Atom "Eq"; chc2sexp t1; chc2sexp t2 ]
    | CNe (t1, t2) -> Sexp.List [ Sexp.Atom "Ne"; chc2sexp t1; chc2sexp t2 ]
    | CBNot t -> Sexp.List [ Sexp.Atom "BNot"; chc2sexp t ]
    | CLNot t -> Sexp.List [ Sexp.Atom "LNot"; chc2sexp t ]
    | CNeg t -> Sexp.List [ Sexp.Atom "Neg"; chc2sexp t ]
    | Add (t1, t2) -> Sexp.List [ Sexp.Atom "PlusA"; chc2sexp t1; chc2sexp t2 ]
    | Mul (t1, t2) -> Sexp.List [ Sexp.Atom "Mult"; chc2sexp t1; chc2sexp t2 ]
    | Sub (t1, t2) -> Sexp.List [ Sexp.Atom "MinusA"; chc2sexp t1; chc2sexp t2 ]
    | Div (t1, t2) -> Sexp.List [ Sexp.Atom "Div"; chc2sexp t1; chc2sexp t2 ]
    | Mod (t1, t2) -> Sexp.List [ Sexp.Atom "Mod"; chc2sexp t1; chc2sexp t2 ]
    | BvShl (t1, t2) ->
        Sexp.List [ Sexp.Atom "bvshl"; chc2sexp t1; chc2sexp t2 ]
    | BvShr (t1, t2) ->
        Sexp.List [ Sexp.Atom "bvshr"; chc2sexp t1; chc2sexp t2 ]
    | BvAnd (t1, t2) ->
        Sexp.List [ Sexp.Atom "bvand"; chc2sexp t1; chc2sexp t2 ]
    | BvOr (t1, t2) -> Sexp.List [ Sexp.Atom "bvor"; chc2sexp t1; chc2sexp t2 ]
    | BvXor (t1, t2) ->
        Sexp.List [ Sexp.Atom "bvxor"; chc2sexp t1; chc2sexp t2 ]
    | Var s | FDNumeral s -> Sexp.Atom s
    | Const i -> Sexp.Atom (Z.to_string i)
    | FuncApply (fn, args) ->
        Sexp.List (Sexp.Atom fn :: List.map ~f:chc2sexp args)
    | Implies (cons, hd) -> Sexp.List (chc2sexp hd :: List.map ~f:chc2sexp cons)

  let is_rel = function FuncApply _ -> true | _ -> false
  let is_rule = function Implies _ -> true | _ -> false
  let is_duedge = function FuncApply ("DUEdge", _) -> true | _ -> false
  let is_dupath = function FuncApply ("DUPath", _) -> true | _ -> false

  let get_body = function
    | Implies (body, _) -> body
    | _ -> L.error "get_body: wrong chc"

  let get_head = function
    | Implies (_, head) -> head
    | _ -> L.error "get_head: wrong chc"

  let get_func_name = function
    | FuncApply (fn, _) -> fn
    | _ -> L.error "get_func_name: wrong chc"

  let get_args = function
    | FuncApply ("Arg", args)
    | FuncApply ("BinOpExp", args)
    | FuncApply ("UnOpExp", args) ->
        List.hd_exn args :: (List.tl_exn args |> List.tl_exn)
    | FuncApply (_, args) -> args
    | _ -> L.error "get_args: wrong chc"

  let before node = function
    | FuncApply ("DUPath", [ src; dst ]) when equal dst node -> Some src
    | _ -> None

  let after node = function
    | FuncApply ("DUPath", [ src; dst ]) when equal src node -> Some dst
    | _ -> None

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
    | BvShl (t1, t2) -> BvShl (numer2var t1, numer2var t2)
    | BvShr (t1, t2) -> BvShr (numer2var t1, numer2var t2)
    | BvAnd (t1, t2) -> BvAnd (numer2var t1, numer2var t2)
    | BvOr (t1, t2) -> BvOr (numer2var t1, numer2var t2)
    | BvXor (t1, t2) -> BvXor (numer2var t1, numer2var t2)
    | Not t -> Not (numer2var t)
    | CBNot t -> CBNot (numer2var t)
    | CLNot t -> CLNot (numer2var t)
    | CNeg t -> CNeg (numer2var t)
    | FuncApply (fn, args) ->
        FuncApply (fn, List.map ~f:(fun arg -> numer2var arg) args)
    | Var _ as v -> v
    | FDNumeral s ->
        if Z3utils.is_binop s || Z3utils.is_unop s then FDNumeral s else Var s
    | Const _ as c -> c
    | Implies (cons, hd) ->
        Implies (List.map ~f:(fun c -> numer2var c) cons, numer2var hd)

  let rec to_z3 maps = function
    | Lt (e1, e2) ->
        Z3.BitVector.mk_slt z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Gt (e1, e2) ->
        Z3.BitVector.mk_sgt z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Le (e1, e2) ->
        Z3.BitVector.mk_sle z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Ge (e1, e2) ->
        Z3.BitVector.mk_sge z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Eq (e1, e2) ->
        Z3.Boolean.mk_eq z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Ne (e1, e2) ->
        Z3.Boolean.mk_not z3env.z3ctx
          (Z3.Boolean.mk_eq z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2))
    | Not e -> Z3.Boolean.mk_not z3env.z3ctx (to_z3 maps e)
    | CLt (e1, e2) ->
        Z3.Boolean.mk_ite z3env.z3ctx
          (Z3.Arithmetic.mk_lt z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2))
          (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
          (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
    | CGt (e1, e2) ->
        Z3.Boolean.mk_ite z3env.z3ctx
          (Z3.BitVector.mk_sgt z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2))
          (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
          (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
    | CLe (e1, e2) ->
        Z3.Boolean.mk_ite z3env.z3ctx
          (Z3.BitVector.mk_sle z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2))
          (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
          (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
    | CGe (e1, e2) ->
        Z3.Boolean.mk_ite z3env.z3ctx
          (Z3.BitVector.mk_sge z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2))
          (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
          (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
    | CEq (e1, e2) ->
        Z3.Boolean.mk_ite z3env.z3ctx
          (Z3.Boolean.mk_eq z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2))
          (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
          (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
    | CNe (e1, e2) ->
        Z3.Boolean.mk_ite z3env.z3ctx
          (Z3.Boolean.mk_eq z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2))
          (Z3.BitVector.mk_numeral z3env.z3ctx "0" 64)
          (Z3.BitVector.mk_numeral z3env.z3ctx "1" 64)
    | CBNot e -> Z3.BitVector.mk_not z3env.z3ctx (to_z3 maps e)
    | CLNot e ->
        let zero = Z3.BitVector.mk_numeral z3env.z3ctx "0" 64 in
        let one = Z3.BitVector.mk_numeral z3env.z3ctx "1" 64 in
        let is_zero = Z3.Boolean.mk_eq z3env.z3ctx (to_z3 maps e) zero in
        Z3.Boolean.mk_ite z3env.z3ctx is_zero one zero
    | CNeg e -> Z3.BitVector.mk_neg z3env.z3ctx (to_z3 maps e)
    | FuncApply (f, args) ->
        Z3.FuncDecl.apply (Z3utils.match_func f) (List.map ~f:(to_z3 maps) args)
    | Add (e1, e2) ->
        Z3.BitVector.mk_add z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Sub (e1, e2) ->
        Z3.BitVector.mk_sub z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Mul (e1, e2) ->
        Z3.BitVector.mk_mul z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Div (e1, e2) ->
        Z3.BitVector.mk_sdiv z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | Mod (e1, e2) ->
        Z3.BitVector.mk_smod z3env.z3ctx (to_z3 maps e1) (to_z3 maps e2)
    | BvShl (t1, t2) ->
        Z3.BitVector.mk_shl z3env.z3ctx (to_z3 maps t1) (to_z3 maps t2)
    | BvShr (t1, t2) ->
        Z3.BitVector.mk_lshr z3env.z3ctx (to_z3 maps t1) (to_z3 maps t2)
    | BvAnd (t1, t2) ->
        Z3.BitVector.mk_and z3env.z3ctx (to_z3 maps t1) (to_z3 maps t2)
    | BvOr (t1, t2) ->
        Z3.BitVector.mk_or z3env.z3ctx (to_z3 maps t1) (to_z3 maps t2)
    | BvXor (t1, t2) ->
        Z3.BitVector.mk_xor z3env.z3ctx (to_z3 maps t1) (to_z3 maps t2)
    | Var x ->
        let sort = Z3utils.match_sort x in
        Z3.Expr.mk_const_s z3env.z3ctx x sort
    | FDNumeral s ->
        let sort = Z3utils.match_sort s in
        Z3utils.mk_numer maps s sort
    | Const i -> Z3.BitVector.mk_numeral z3env.z3ctx (Z.to_string i) 64
    | Implies (tl, hd) ->
        let cons =
          if List.is_empty tl then Z3.Boolean.mk_true z3env.z3ctx
          else Z3.Boolean.mk_and z3env.z3ctx (List.map ~f:(to_z3 maps) tl)
        in
        Z3.Boolean.mk_implies z3env.z3ctx cons (to_z3 maps hd)
end

include Set.Make (struct
  type t = Elt.t

  let compare = Stdlib.compare
end)

let to_list s = fold (fun c l -> c :: l) s []

let rec collect_vars = function
  | Elt.Lt (t1, t2)
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
  | Mod (t1, t2)
  | BvShl (t1, t2)
  | BvShr (t1, t2)
  | BvAnd (t1, t2)
  | BvOr (t1, t2)
  | BvXor (t1, t2) ->
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
  | Elt.Lt (t1, t2) -> F.fprintf fmt "(%a < %a)" pp_chc t1 pp_chc t2
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
  | BvShl (t1, t2) -> F.fprintf fmt "(%a bvshl %a)" pp_chc t1 pp_chc t2
  | BvShr (t1, t2) -> F.fprintf fmt "(%a bvshr %a)" pp_chc t1 pp_chc t2
  | BvAnd (t1, t2) -> F.fprintf fmt "(%a bvand %a)" pp_chc t1 pp_chc t2
  | BvOr (t1, t2) -> F.fprintf fmt "(%a bvor %a)" pp_chc t1 pp_chc t2
  | BvXor (t1, t2) -> F.fprintf fmt "(%a bvxor %a)" pp_chc t1 pp_chc t2
  | Var s | FDNumeral s -> F.fprintf fmt "%s" s
  | Const i -> F.fprintf fmt "%Ld" (Z.to_int64 i)
  | Implies (cons, hd) as impl ->
      let vars = collect_vars impl in
      let vars_str =
        fold (fun var s -> F.asprintf "%s %a" s pp_chc var) vars ""
      in
      List.map ~f:(fun c -> F.asprintf "%a" pp_chc c) cons
      |> String.concat ~sep:",\n    "
      |> F.fprintf fmt "(\\forall %s.\n  %a <-\n    %s)" vars_str pp_chc hd

let pp fmt = iter (fun chc -> F.fprintf fmt "%a\n" pp_chc chc)

let pp_smt fmt =
  iter (fun chc ->
      Elt.chc2sexp chc |> Sexp.pp fmt;
      F.fprintf fmt "\n")

let pretty_dump file chcs =
  let oc_file = Out_channel.create (file ^ "_hum.chc") in
  let fmt = F.formatter_of_out_channel oc_file in
  F.fprintf fmt "%a" pp chcs;
  F.pp_print_flush fmt ();
  Out_channel.close oc_file

let sexp_dump file chcs =
  let oc_file = Out_channel.create (file ^ "_mach.chc") in
  let fmt = F.formatter_of_out_channel oc_file in
  F.fprintf fmt "%a" pp_smt chcs;
  F.pp_print_flush fmt ();
  Out_channel.close oc_file

let rec filter_func_app = function
  | Elt.FuncApply _ as chc -> singleton chc
  | Implies _ as chc ->
      Elt.get_body chc
      |> List.fold_left ~init:empty ~f:(fun fa c ->
             filter_func_app c |> union fa)
  | _ -> empty

let extract_func_apps chcs =
  fold (fun chc fa -> filter_func_app chc |> union fa) chcs empty

let extract_syntactic_rels =
  filter (function Elt.FuncApply _ -> true | _ -> false)

let add_args_to_terms terms rel =
  Elt.get_args rel
  |> List.fold_left ~init:terms ~f:(fun terms arg -> add arg terms)

let all_args_has_dep terms args =
  List.for_all ~f:(fun arg -> mem arg terms) args

let exists_dep_arg terms args = List.exists ~f:(fun arg -> mem arg terms) args

let prop_deps terms = function
  | Elt.FuncApply ("DUEdge", [ src; dst; loc ]) ->
      if mem dst terms && mem loc terms then (true, add src terms)
      else (false, terms)
  | FuncApply ("CFPath", args) | FuncApply ("DUPath", args) ->
      if all_args_has_dep terms args then (true, terms) else (false, terms)
  | FuncApply ("EvalLv", [ _; lval; loc ]) ->
      if mem lval terms then (true, add loc terms) else (false, terms)
  | FuncApply ("Set", [ node; _; exp ]) ->
      if mem node terms then (true, add exp terms) else (false, terms)
  | FuncApply ("Return", [ node; exp ]) ->
      if mem node terms then (true, add exp terms) else (false, terms)
  | FuncApply ("Arg", [ arg_list; _; exp ]) ->
      if mem arg_list terms then (true, add exp terms) else (false, terms)
  | FuncApply ("BinOp", [ e; _; e1; e2 ]) ->
      if mem e terms then (true, terms |> add e1 |> add e2) else (false, terms)
  | FuncApply ("UnOp", [ e; _; e1 ]) ->
      if mem e terms then (true, add e1 terms) else (false, terms)
  | FuncApply ("LvalExp", [ exp; lval ]) ->
      if mem exp terms then (true, add lval terms) else (false, terms)
  | FuncApply ("Call", [ e; _; arg_list ])
  | FuncApply ("LibCall", [ e; _; arg_list ]) ->
      (* Maybe not used *)
      if mem e terms then (true, add arg_list terms) else (false, terms)
  | FuncApply ("Alloc", [ e; size_e ]) ->
      if mem e terms then (true, add size_e terms) else (false, terms)
  | FuncApply ("SAlloc", [ e; _ ]) ->
      if mem e terms then (true, terms) else (false, terms)
  | _ -> (false, terms)

let is_child var = function
  | Elt.FuncApply ("Set", hd :: _)
  | FuncApply ("Return", hd :: _)
  | FuncApply ("Arg", _ :: hd :: _)
  | FuncApply ("BinOp", hd :: _)
  | FuncApply ("UnOp", hd :: _)
  | FuncApply ("LvalExp", hd :: _)
  | FuncApply ("Call", hd :: _)
  | FuncApply ("LibCall", hd :: _)
  | FuncApply ("Alloc", hd :: _)
  | FuncApply ("SAlloc", hd :: _) ->
      Elt.equal var hd
  | _ -> false

let collect_children var rels = filter (is_child var) rels

let is_removable rels = function
  | Elt.FuncApply ("CFPath", args) | FuncApply ("DUPath", args) ->
      List.exists ~f:(fun arg -> collect_children arg rels |> cardinal = 0) args
  | FuncApply ("Set", _ :: _ :: args)
  | FuncApply ("Return", _ :: args)
  | FuncApply ("Arg", _ :: _ :: args)
  | FuncApply ("BinOp", _ :: _ :: args)
  | FuncApply ("UnOp", _ :: _ :: args)
  | FuncApply ("LvalExp", _ :: args)
  | FuncApply ("Call", _ :: _ :: args)
  | FuncApply ("LibCall", _ :: _ :: args)
  | FuncApply ("Alloc", _ :: args)
  | FuncApply ("SAlloc", _ :: args) ->
      List.for_all
        ~f:(fun arg -> collect_children arg rels |> cardinal = 0)
        args
  | _ -> false

let collect_removable chcs = filter (is_removable chcs) chcs

let collect_node ~before node chcs =
  let befores =
    fold
      (fun chc b ->
        Option.(Elt.before node chc >>| singleton)
        |> Option.value ~default:empty
        |> union b)
      chcs empty
  in
  let afters =
    fold
      (fun chc b ->
        Option.(Elt.after node chc >>| singleton)
        |> Option.value ~default:empty
        |> union b)
      chcs empty
  in
  if before then diff befores afters else diff afters befores

let find_rule head_name =
  find_first (function
    | Elt.Implies (_, FuncApply (f, _)) when String.equal f head_name -> true
    | _ -> false)

let update_rule head_name new_body chcs =
  let target = find_rule head_name chcs in
  let head = Elt.get_head target in
  let new_rule = Elt.Implies (new_body, head) in
  remove target chcs |> add new_rule

let add_fact maps solver f =
  if Elt.is_duedge f |> not then
    let fact = Elt.to_z3 maps f in
    Z3.Fixedpoint.add_rule solver fact None

let add_rule maps solver r =
  if Elt.is_duedge r |> not then
    let vars = collect_vars r |> to_list |> List.map ~f:(Elt.to_z3 maps) in
    let impl = Elt.to_z3 maps r in
    if List.is_empty vars then add_fact maps solver r
    else
      let rule =
        Z3.Quantifier.mk_forall_const z3env.z3ctx vars impl None [] [] None None
        |> Z3.Quantifier.expr_of_quantifier
      in
      Z3.Fixedpoint.add_rule solver rule None

let add_all maps solver =
  iter (fun chc ->
      if Elt.is_rel chc then add_fact maps solver chc
      else add_rule maps solver chc)

let pattern_match out_dir maps chc pattern query =
  let solver = mk_fixedpoint z3env.z3ctx in
  reg_rel_to_solver z3env solver;
  add_all maps solver (union chc pattern);
  let status = Z3.Fixedpoint.query_r solver query in
  Z3utils.dump_solver_to_smt "test" solver out_dir;
  match status with
  | Z3.Solver.UNSATISFIABLE -> None
  | Z3.Solver.SATISFIABLE -> Z3.Fixedpoint.get_answer solver
  | Z3.Solver.UNKNOWN -> None

let match_and_log out_dir ver_name maps chc pattern query =
  let status = pattern_match out_dir maps chc pattern query in
  Option.iter
    ~f:(fun ans ->
      L.info "Matched";
      Z3utils.dump_expr_to_smt (ver_name ^ "_ans") ans out_dir)
    status
