open Core
module F = Format
module L = Logger
module Hashtbl = Stdlib.Hashtbl

let match_func z3env f =
  match f with
  | "Assume" -> z3env.Z3env.assume
  | "Src" -> z3env.src
  | "Snk" -> z3env.snk
  | "Skip" -> z3env.skip
  | "Set" -> z3env.set
  | "Copy" -> z3env.copy
  | "AllocExp" -> z3env.alloc
  | "SAllocExp" -> z3env.salloc
  | "LvalExp" -> z3env.lval_exp
  | "Var" -> z3env.var
  | "Index" -> z3env.index
  | "Mem" -> z3env.deref
  | "Field" -> z3env.field
  | "AddrOf" -> z3env.addrof
  | "CallExp" -> z3env.call
  | "LibCallExp" -> z3env.libcall
  | "ReadCallExp" -> z3env.readcall
  | "Arg" -> z3env.arg
  | "ConstExp" -> z3env.constexp
  | "Return" -> z3env.ret
  | "BinOpExp" -> z3env.binop
  | "UnOpExp" -> z3env.unop
  | "CFPath" -> z3env.cfpath
  | "DetailedDUEdge" -> z3env.deduedge
  | "DUEdge" -> z3env.duedge
  | "DUPath" -> z3env.dupath
  | "EvalLv" -> z3env.evallv
  | "Eval" -> z3env.eval
  | "Memory" -> z3env.memory
  | "ArrVal" -> z3env.arrval
  | "ConstStr" -> z3env.conststr
  | "SizeOf" -> z3env.sizeof
  | "StrLen" -> z3env.strlen
  | "Val" -> z3env.val_rel
  | "StrVal" -> z3env.strval
  | "Alarm" -> z3env.alarm
  | "Reach" -> z3env.reach
  | "IOError" -> z3env.ioerror
  | "DZError" -> z3env.dzerror
  | "ErrTrace" -> z3env.errtrace
  | "Bug" -> z3env.bug
  | s -> F.sprintf "match_func: invalid function - %s" s |> failwith

let is_binop = function
  | "PlusA" | "PlusPI" | "IndexPI" | "MinusA" | "MinusPI" | "MinusPP" | "Mult"
  | "Div" | "Mod" | "bvshl" | "bvshr" | "Lt" | "Gt" | "Le" | "Ge" | "Eq" | "Ne"
  | "bvand" | "bvxor" | "bvor" | "and" | "or" ->
      true
  | _ -> false

let int_of_binop = function
  | "PlusA" -> 0
  | "PlusPI" -> 1
  | "IndexPI" -> 2
  | "MinusA" -> 3
  | "MinusPI" -> 4
  | "MinusPP" -> 5
  | "Mult" -> 6
  | "Div" -> 7
  | "Mod" -> 8
  | "bvshl" -> 9
  | "bvshr" -> 10
  | "Lt" -> 11
  | "Gt" -> 12
  | "Le" -> 13
  | "Ge" -> 14
  | "Eq" -> 15
  | "Ne" -> 16
  | "bvand" -> 17
  | "bvxor" -> 18
  | "bvor" -> 19
  | "and" -> 20
  | "or" -> 21
  | _ -> failwith "int_of_binop: invalid symbol"

let binop_of_int = function
  | 0 -> "PlusA"
  | 1 -> "PlusPI"
  | 2 -> "IndexPI"
  | 3 -> "MinusA"
  | 4 -> "MinusPI"
  | 5 -> "MinusPP"
  | 6 -> "Mult"
  | 7 -> "Div"
  | 8 -> "Mod"
  | 9 -> "bvshl"
  | 10 -> "bvshr"
  | 11 -> "Lt"
  | 12 -> "Gt"
  | 13 -> "Le"
  | 14 -> "Ge"
  | 15 -> "Eq"
  | 16 -> "Ne"
  | 17 -> "bvand"
  | 18 -> "bvxor"
  | 19 -> "bvor"
  | 20 -> "and"
  | 21 -> "or"
  | _ -> failwith "binop_of_int: invalid int"

let is_unop = function "BNot" | "LNot" | "Neg" -> true | _ -> false

let int_of_unop = function
  | "BNot" -> 22
  | "LNot" -> 23
  | "Neg" -> 24
  | _ -> failwith "int_of_unop: invalid symbol"

let unop_of_int = function
  | 22 -> "BNot"
  | 23 -> "LNot"
  | 24 -> "Neg"
  | _ -> failwith "unop_of_int: invalid symbol"

let match_sort z3env s =
  let sort_id = String.split ~on:'-' s in
  let name = List.hd_exn sort_id in
  if List.length sort_id = 1 then
    if is_binop name then z3env.Z3env.binop_sort
    else if is_unop name then z3env.unop_sort
    else if String.equal "l" s then z3env.loc
    else if String.is_prefix ~prefix:"v" s then z3env.value
    else if String.is_prefix ~prefix:"s" s then z3env.str_literal
    else z3env.bv_sort
  else
    match name with
    | "Exp" | "CallExp" | "LibCallExp" | "SallocExp" | "AllocExp"
    | "ReadCallExp" ->
        z3env.expr
    | "ArgList" -> z3env.arg_list
    | "Lval" -> z3env.lval
    | "Loc" -> z3env.loc
    | "Val" -> z3env.value
    | "Pos" -> z3env.int_sort
    | "BinOp" -> z3env.binop_sort
    | _ -> z3env.node

let numer_cnt = ref 24 (* for binop, unop *)

let new_numer () =
  incr numer_cnt;
  !numer_cnt

let mk_numer z3env maps sym sort =
  if Z3.Sort.equal sort z3env.Z3env.binop_sort then
    Z3.Expr.mk_numeral_int z3env.z3ctx (int_of_binop sym) sort
  else if Z3.Sort.equal sort z3env.unop_sort then
    Z3.Expr.mk_numeral_int z3env.z3ctx (int_of_unop sym) sort
  else if Hashtbl.mem maps.Maps.sym_map sym then
    Hashtbl.find maps.Maps.sym_map sym
  else
    let i = new_numer () in
    let numer_i = Z3.Expr.mk_numeral_int z3env.z3ctx i sort in
    Hashtbl.add maps.Maps.sym_map sym numer_i;
    Hashtbl.add maps.Maps.numeral_map i sym;
    numer_i

let dump_solver_to_smt ver_name solver out_dir =
  let solver_file = ver_name ^ ".smt2" |> Filename.concat out_dir in
  let solver_oc = Out_channel.create solver_file in
  Z3.Fixedpoint.to_string solver |> Out_channel.output_string solver_oc;
  Out_channel.close solver_oc

let dump_expr_to_smt ver_name expr out_dir =
  let expr_file = ver_name ^ ".smt2" |> Filename.concat out_dir in
  let expr_oc = Out_channel.create expr_file in
  Z3.Expr.to_string expr |> Out_channel.output_string expr_oc;
  Out_channel.close expr_oc

let dump_formula ver_name solver query out_dir =
  let file = ver_name ^ "_formula.smt2" |> Filename.concat out_dir in
  let oc = Out_channel.create file in
  Printf.fprintf oc
    "(define-sort arg_list () Int)\n\
     (define-sort node () Int)\n\
     (define-sort expr () Int)\n\
     (define-sort unop () Int)\n\
     (define-sort binop () Int)\n\
     (define-sort lval () Int)\n\
     (define-sort int () Int)\n";
  Z3.Fixedpoint.to_string solver |> Printf.fprintf oc "%s\n";
  Z3.Expr.to_string query |> Printf.fprintf oc "%s\n";
  Out_channel.close oc
