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

let match_sort s =
  let sort_id = String.split ~on:'-' s in
  if List.length sort_id = 1 then z3env.bv_sort
  else
    let sort = List.hd_exn sort_id in
    match sort with
    | "Exp" | "CallExp" | "LibCallExp" | "SallocExp" | "AllocExp" -> z3env.expr
    | "ArgList" -> z3env.arg_list
    | "Lval" -> z3env.lval
    | "Loc" | "Val" -> z3env.value
    | "BinOp" -> z3env.binop_sort
    | "UnOp" -> z3env.unop_sort
    | _ -> z3env.node

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
  else Z3.Expr.mk_numeral_int z3env.z3ctx (new_numer ()) sort

let add_fact solver func args =
  Z3.Fixedpoint.add_rule solver (Z3.FuncDecl.apply func args) None

let mk_rule z3ctx vars cons =
  Z3.Quantifier.mk_forall_const z3ctx vars cons None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

(* let match_rule facts pattern =
   let solver = mk_fixedpoint z3env.z3ctx in
   reg_rel_to_solver z3env solver;
   let bug = Z3.FuncDecl.apply z3env.bug [] in
   let cond = Z3.Boolean.mk_and z3env.z3ctx (set2list pattern) in
   let vars_for_all = Bag.to_list Maps.var_bag in
   let bug_pattern_rule =
     mk_rule z3env.z3ctx vars_for_all
       (Z3.Boolean.mk_implies z3env.z3ctx cond bug)
   in
   List.iter ~f:(fun fact -> Z3.Fixedpoint.add_rule solver fact None) facts;
   Z3.Fixedpoint.add_rule solver bug_pattern_rule None;
   let status = Z3.Fixedpoint.query solver (Z3.FuncDecl.apply z3env.bug []) in
   match status with
   | Z3.Solver.UNSATISFIABLE -> None
   | Z3.Solver.SATISFIABLE -> Z3.Fixedpoint.get_answer solver
   | Z3.Solver.UNKNOWN -> None *)
