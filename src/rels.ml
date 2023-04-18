open Core
module F = Format
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module StrMap = Map.Make (String)

type t =
  | Set of node * lval * expr
  | Call of node * lval * expr * arg_list
  | Arg of arg_list * int * expr
  | Alloc of node * lval * expr
  | Salloc of node * lval * string
  | Falloc of node * lval * fundec
  | Return of node * expr
  | Skip of node
  | Const of expr * const
  | LvalExp of expr * lval
  | SizeOfExp of expr * expr
  | SizeOfType of expr * typ
  | UnOp of expr * unop * expr
  | BinOp of expr * expr * binop * expr
  | Cast of expr * typ * expr
  | StartOf of expr * lval
  | SubExp of expr * expr
  (* NOTE: is it necessary? *)
  (* TODO: relations for lval *)
  | DUPath of node * node
  | EvalLv of node * lval * loc
  | Eval of node * expr * value
  | Memory of node * loc * value
  | Array of value * offset * size * stride

and sem_cons =
  | SemEq of sem_cons * sem_cons
  | SemNe of sem_cons * sem_cons
  | SemLe of sem_cons * sem_cons
  | SemLt of sem_cons * sem_cons
  | SizeOf of value
  | StrLen of arg_list

and fundec = FunDec of string
and node = Node of string
and expr = Expr of string
and typ = Typ of string
and lval = Lval of string

and const =
  | Int of int
  | String of string
  | Chr of char
  | Real of float
  | Enum of string * string

and unop = Neg | BNot | LNot

and binop =
  | PlusA
  | PlusPI
  | IndexPI
  | MinusA
  | MinusPI
  | Mult
  | Div
  | Mod
  | Shiflt
  | Shiftrt
  | Lt
  | Gt
  | Le
  | Ge
  | Eq
  | Ne
  | BAnd
  | BXor
  | BOr
  | LAnd
  | LOr

and arg_list = ArgList of string
and loc = Loc of string
and value = Val of string
and offset = Offset of string
and size = Size of string
and stride = Stride of string

type maps = {
  sym_map : (string, Z3.Expr.expr) Hashtbl.t;
  node_map : (string, Z3.Expr.expr) Hashtbl.t;
  numeral_map : (Z3.Expr.expr, string) Hashtbl.t;
  exp_map : (string, string) Hashtbl.t;
  exp_map_inv : (string, string) Hashtbl.t;
  fixed_exps : string Bag.t;
}

let create_maps () =
  {
    sym_map = Hashtbl.create 1000;
    node_map = Hashtbl.create 1000;
    numeral_map = Hashtbl.create 1000;
    exp_map = Hashtbl.create 1000;
    exp_map_inv = Hashtbl.create 1000;
    fixed_exps = Bag.create ();
  }

let const_map = Hashtbl.create 1000
let numer = ref 0

let new_numer () =
  incr numer;
  !numer


let mk_facts maps work_dir =
  let datalog_dir = Filename.concat work_dir "sparrow-out/interval/datalog" in
  let exp_map_ic = Filename.concat datalog_dir "Exp.map" |> In_channel.create in
  let rec loop () =
    let line = In_channel.input_line exp_map_ic in
    if Option.is_some line then (
      let pair = Option.value_exn line |> String.split ~on:'\t' in
      Hashtbl.add maps.exp_map (List.nth_exn pair 0) (List.nth_exn pair 1);
      Hashtbl.add maps.exp_map_inv (List.nth_exn pair 1) (List.nth_exn pair 0);
      loop ())
  in
  loop ();
  In_channel.close exp_map_ic;
  let app_fact fact_file =
    let fact_file_path = Filename.concat datalog_dir fact_file in
    let ic = In_channel.create fact_file_path in
    let rec loop () =
      let line = In_channel.input_line ic in
      if Option.is_some line then (
        let line = Option.value_exn line in
        let numeral_args, var_args =
          List.fold2_exn ~init:([], [])
            ~f:(z3_add_symbol ~fix_exp:(String.equal fact_file "LibCall.facts"))
            (String.split ~on:'\t' line)
            arg_sorts
        in
        let numeral_args = List.rev numeral_args in
        let var_args = List.rev var_args in
        add_fact solver func numeral_args;
        if add_var_too then add_fact z3env.pattern_solver func var_args;
        loop ())
    match fact_file with
    | "Alloc.facts" 
