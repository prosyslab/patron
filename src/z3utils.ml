open Core
module L = Logger
include Z3env

let match_func = function
  | "Src" -> z3env.src
  | "Snk" -> z3env.snk
  | "Skip" -> z3env.skip
  | "Set" -> z3env.set
  | "Alloc" -> z3env.alloc
  | "SAlloc" -> z3env.salloc
  | "LvalExp" -> z3env.lval_exp
  | "Var" -> z3env.var
  | "Call" -> z3env.call
  | "LibCall" -> z3env.libcall
  | "Arg" -> z3env.arg
  | "ConstExp" -> z3env.constexp
  | "Return" -> z3env.ret
  | "BinOp" -> z3env.binop
  | "UnOp" -> z3env.unop
  | "CFPath" -> z3env.cfpath
  | "DUPath" -> z3env.dupath
  | "EvalLv" -> z3env.evallv
  | "Eval" -> z3env.eval
  | "Memory" -> z3env.memory
  | "ArrVal" -> z3env.arrval
  | "ConstStr" -> z3env.conststr
  | "SizeOf" -> z3env.sizeof
  | "StrLen" -> z3env.strlen
  | "Val" -> z3env.val_rel
  | "Alarm" -> z3env.alarm
  | "Reach" -> z3env.reach
  | "IOError" -> z3env.ioerror
  | "ErrNode" -> z3env.errnode
  | "Bug" -> z3env.bug
  | _ -> L.error "match_func: invalid function"

let is_binop = function
  | "+" | "PlusPI" | "IndexPI" | "-" | "MinusPI" | "MinusPP" | "*" | "/" | "%"
  | "bvshl" | "bvshr" | "Lt" | "Gt" | "Le" | "Ge" | "Eq" | "Ne" | "bvand"
  | "bvxor" | "bvor" | "and" | "or" ->
      true
  | _ -> false

let match_binop = function
  | "+" -> 0
  | "PlusPI" -> 1
  | "IndexPI" -> 2
  | "-" -> 3
  | "MinusPI" -> 4
  | "MinusPP" -> 5
  | "*" -> 6
  | "/" -> 7
  | "%" -> 8
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
  | _ -> L.error "match_binop: invalid symbol"

let is_unop = function "BNot" | "LNot" | "Neg" -> true | _ -> false

let match_unop = function
  | "BNot" -> 22
  | "LNot" -> 23
  | "Neg" -> 24
  | _ -> L.error "match_unop: invalid symbol"

let match_sort s =
  let sort_id = String.split ~on:'-' s in
  let name = List.hd_exn sort_id in
  if List.length sort_id = 1 then
    if is_binop name then z3env.binop_sort
    else if is_unop name then z3env.unop_sort
    else z3env.bv_sort
  else
    let id = List.nth_exn sort_id 1 in
    if String.is_empty name then
      if String.is_empty id then z3env.binop_sort else z3env.bv_sort
    else
      match name with
      | "Exp" | "CallExp" | "LibCallExp" | "SallocExp" | "AllocExp" ->
          z3env.expr
      | "ArgList" -> z3env.arg_list
      | "Lval" -> z3env.lval
      | "Loc" | "Val" -> z3env.value
      | _ -> z3env.node

let numer_cnt = ref 24 (* for binop, unop *)

let new_numer () =
  incr numer_cnt;
  !numer_cnt

let mk_numer maps sym sort =
  if Z3.Sort.equal sort z3env.binop_sort then
    Z3.Expr.mk_numeral_int z3env.z3ctx (match_binop sym) sort
  else if Z3.Sort.equal sort z3env.unop_sort then
    Z3.Expr.mk_numeral_int z3env.z3ctx (match_unop sym) sort
  else if Hashtbl.mem maps.Maps.sym_map sym then
    Hashtbl.find maps.Maps.sym_map sym
  else
    let n = Z3.Expr.mk_numeral_int z3env.z3ctx (new_numer ()) sort in
    Hashtbl.add maps.Maps.sym_map sym n;
    n

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
