open Core
include Z3env

module ExprSet = struct
  include Set.Make (struct
    type t = Z3.Expr.expr

    let compare = Z3.Expr.compare
  end)

  let pp fmt es =
    fold (fun e s -> s ^ Z3.Expr.to_string e ^ "\n") es "" |> F.fprintf fmt "%s"
end

let set2list set = ExprSet.fold (fun elt lst -> elt :: lst) set []

let is_what subs rel =
  if Z3.Expr.to_string rel |> String.is_substring ~substring:subs then true
  else false

let is_cfpath = is_what "(CFPath"
let is_dupath = is_what "(DUPath"
let is_alloc = is_what "(Alloc"
let is_salloc = is_what "(SAlloc"
let is_set = is_what "(Set"
let is_call = is_what "(Call"
let is_libcall = is_what "(LibCall"
let is_var = is_what "(Var"
let is_skip = is_what "(Skip"
let is_ret = is_what "(Return"
let is_eval = is_what "(Eval"
let is_evallv = is_what "(EvalLv"
let is_memory = is_what "(Memory"
let is_sizeof = is_what "(SizeOf"
let is_strlen = is_what "(StrLen"
let is_intval = is_what "(IntVal"
let is_alarm = is_what "(Alarm"
let is_let = is_what "(let"
let is_binop = is_what "(BinOp"
let is_unop = is_what "(UnOp"
let is_cast = is_what "(Cast"
let is_arg = is_what "(Arg"
let ( ||| ) f1 f2 x = f1 x || f2 x
let is_sem_cons = is_sizeof ||| is_strlen ||| is_intval
let is_sem_rels = is_eval ||| is_evallv ||| is_memory

let is_node_rels =
  is_sem_rels ||| is_alloc ||| is_alloc ||| is_salloc ||| is_set ||| is_call
  ||| is_libcall ||| is_ret

let neg f x = not (f x)

let match_rule facts pattern =
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
  | Z3.Solver.UNKNOWN -> None
