open Core
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module F = Format

type t = {
  z3ctx : Z3.context;
  boolean_sort : Z3.Sort.sort;
  int_sort : Z3.Sort.sort;
  bv_sort : Z3.Sort.sort;
  str_sort : Z3.Sort.sort;
  zero : Z3.Expr.expr;
  one : Z3.Expr.expr;
  two : Z3.Expr.expr;
  three : Z3.Expr.expr;
  node : Z3.Sort.sort;
  lval : Z3.Sort.sort;
  expr : Z3.Sort.sort;
  binop_sort : Z3.Sort.sort;
  unop_sort : Z3.Sort.sort;
  identifier : Z3.Sort.sort;
  arg_list : Z3.Sort.sort;
  str_literal : Z3.Sort.sort;
  loc : Z3.Sort.sort;
  value : Z3.Sort.sort;
  const : Z3.Sort.sort;
  src : Z3.FuncDecl.func_decl;
  snk : Z3.FuncDecl.func_decl;
  skip : Z3.FuncDecl.func_decl;
  set : Z3.FuncDecl.func_decl;
  copy : Z3.FuncDecl.func_decl;
  alloc : Z3.FuncDecl.func_decl;
  salloc : Z3.FuncDecl.func_decl;
  assume : Z3.FuncDecl.func_decl;
  lval_exp : Z3.FuncDecl.func_decl;
  var : Z3.FuncDecl.func_decl;
  index : Z3.FuncDecl.func_decl;
  deref : Z3.FuncDecl.func_decl;
  field : Z3.FuncDecl.func_decl;
  addrof : Z3.FuncDecl.func_decl;
  call : Z3.FuncDecl.func_decl;
  libcall : Z3.FuncDecl.func_decl;
  arg : Z3.FuncDecl.func_decl;
  constexp : Z3.FuncDecl.func_decl;
  ret : Z3.FuncDecl.func_decl;
  cast : Z3.FuncDecl.func_decl;
  binop : Z3.FuncDecl.func_decl;
  unop : Z3.FuncDecl.func_decl;
  cfpath : Z3.FuncDecl.func_decl;
  deduedge : Z3.FuncDecl.func_decl;
  duedge : Z3.FuncDecl.func_decl;
  dupath : Z3.FuncDecl.func_decl;
  (* Functions for Semantic Constraint *)
  evallv : Z3.FuncDecl.func_decl;
  eval : Z3.FuncDecl.func_decl;
  memory : Z3.FuncDecl.func_decl;
  arrval : Z3.FuncDecl.func_decl;
  strval : Z3.FuncDecl.func_decl;
  conststr : Z3.FuncDecl.func_decl;
  sizeof : Z3.FuncDecl.func_decl;
  strlen : Z3.FuncDecl.func_decl;
  val_rel : Z3.FuncDecl.func_decl;
  alarm : Z3.FuncDecl.func_decl;
  reach : Z3.FuncDecl.func_decl;
  ioerror : Z3.FuncDecl.func_decl;
  dzerror : Z3.FuncDecl.func_decl;
  errtrace : Z3.FuncDecl.func_decl;
  bug : Z3.FuncDecl.func_decl;
}

let buggy_src = ref ""
let buggy_snk = ref ""

let mk_fixedpoint z3ctx =
  let mk_string_symbol s = Z3.Symbol.mk_string z3ctx s in
  let s = Z3.Fixedpoint.mk_fixedpoint z3ctx in
  let param = Z3.Params.mk_params z3ctx in
  Z3.Params.add_symbol param
    (mk_string_symbol "engine")
    (mk_string_symbol "datalog");
  Z3.Params.add_bool param
    (mk_string_symbol "datalog.generate_explanations")
    true;
  Z3.Params.add_bool param (mk_string_symbol "spacer.elim_aux") false;
  Z3.Params.add_bool param (mk_string_symbol "xform.slice") false;
  Z3.Params.add_bool param (mk_string_symbol "xform.inline_linear") false;
  Z3.Params.add_bool param (mk_string_symbol "xform.inline_eager") false;
  Z3.Fixedpoint.set_parameters s param;
  s

let reg_rel_to_solver env solver =
  Z3.Fixedpoint.register_relation solver env.src;
  Z3.Fixedpoint.register_relation solver env.snk;
  Z3.Fixedpoint.register_relation solver env.skip;
  Z3.Fixedpoint.register_relation solver env.set;
  Z3.Fixedpoint.register_relation solver env.copy;
  Z3.Fixedpoint.register_relation solver env.alloc;
  Z3.Fixedpoint.register_relation solver env.salloc;
  Z3.Fixedpoint.register_relation solver env.assume;
  Z3.Fixedpoint.register_relation solver env.lval_exp;
  Z3.Fixedpoint.register_relation solver env.var;
  Z3.Fixedpoint.register_relation solver env.index;
  Z3.Fixedpoint.register_relation solver env.deref;
  Z3.Fixedpoint.register_relation solver env.field;
  Z3.Fixedpoint.register_relation solver env.addrof;
  Z3.Fixedpoint.register_relation solver env.call;
  Z3.Fixedpoint.register_relation solver env.libcall;
  Z3.Fixedpoint.register_relation solver env.arg;
  Z3.Fixedpoint.register_relation solver env.constexp;
  Z3.Fixedpoint.register_relation solver env.ret;
  Z3.Fixedpoint.register_relation solver env.cast;
  Z3.Fixedpoint.register_relation solver env.binop;
  Z3.Fixedpoint.register_relation solver env.unop;
  Z3.Fixedpoint.register_relation solver env.cfpath;
  Z3.Fixedpoint.register_relation solver env.deduedge;
  Z3.Fixedpoint.register_relation solver env.duedge;
  Z3.Fixedpoint.register_relation solver env.dupath;
  Z3.Fixedpoint.register_relation solver env.evallv;
  Z3.Fixedpoint.register_relation solver env.eval;
  Z3.Fixedpoint.register_relation solver env.memory;
  Z3.Fixedpoint.register_relation solver env.arrval;
  Z3.Fixedpoint.register_relation solver env.strval;
  Z3.Fixedpoint.register_relation solver env.conststr;
  Z3.Fixedpoint.register_relation solver env.strlen;
  Z3.Fixedpoint.register_relation solver env.sizeof;
  Z3.Fixedpoint.register_relation solver env.val_rel;
  Z3.Fixedpoint.register_relation solver env.alarm;
  Z3.Fixedpoint.register_relation solver env.reach;
  Z3.Fixedpoint.register_relation solver env.ioerror;
  Z3.Fixedpoint.register_relation solver env.dzerror;
  Z3.Fixedpoint.register_relation solver env.errtrace;
  Z3.Fixedpoint.register_relation solver env.bug

let fact_files =
  [
    "AllocExp.facts";
    "Arg.facts";
    "BinOpExp.facts";
    "CallExp.facts";
    "DUEdge.facts";
    "DUPath.facts";
    "LibCallExp.facts";
    "LvalExp.facts";
    "Index.facts";
    "Mem.facts";
    "Field.facts";
    "AddrOf.facts";
    "Return.facts";
    "Set.facts";
    "Copy.facts";
    "Skip.facts";
    "UnOpExp.facts";
    "Assume.facts";
    "EvalLv.facts";
  ]

let sort_size = 1500000 (* NOTE: hard coded *)

let z3ctx =
  Z3.mk_context [ ("model", "true"); ("proof", "true"); ("unsat_core", "true") ]

let boolean_sort = Z3.Boolean.mk_sort z3ctx
let int_sort = Z3.FiniteDomain.mk_sort_s z3ctx "int" (Int64.of_int sort_size)
let bv_sort = Z3.BitVector.mk_sort z3ctx 64 (* NOTE: hard coded *)
let str_sort = Z3.Seq.mk_string_sort z3ctx
let zero = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 0
let one = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 1
let two = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 2
let three = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 3
let node = Z3.FiniteDomain.mk_sort_s z3ctx "node" (Int64.of_int sort_size)
let lval = Z3.FiniteDomain.mk_sort_s z3ctx "lval" (Int64.of_int sort_size)
let expr = Z3.FiniteDomain.mk_sort_s z3ctx "expr" (Int64.of_int sort_size)
let binop_sort = Z3.FiniteDomain.mk_sort_s z3ctx "binop" (Int64.of_int 25)
let unop_sort = Z3.FiniteDomain.mk_sort_s z3ctx "unop" (Int64.of_int 25)
let identifier = Z3.FiniteDomain.mk_sort_s z3ctx "identifier" (Int64.of_int 1)

let arg_list =
  Z3.FiniteDomain.mk_sort_s z3ctx "arg_list" (Int64.of_int sort_size)

let str_literal =
  Z3.FiniteDomain.mk_sort_s z3ctx "str_literal" (Int64.of_int sort_size)

let loc = Z3.FiniteDomain.mk_sort_s z3ctx "loc" (Int64.of_int sort_size)
let value = Z3.FiniteDomain.mk_sort_s z3ctx "value" (Int64.of_int sort_size)
let const = Z3.FiniteDomain.mk_sort_s z3ctx "const" (Int64.of_int sort_size)
let src = Z3.FuncDecl.mk_func_decl_s z3ctx "Src" [ node ] boolean_sort
let snk = Z3.FuncDecl.mk_func_decl_s z3ctx "Snk" [ node ] boolean_sort
let skip = Z3.FuncDecl.mk_func_decl_s z3ctx "Skip" [ node ] boolean_sort

let set =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Set" [ node; lval; expr ] boolean_sort

let copy =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Copy" [ node; lval; lval ] boolean_sort

let alloc =
  Z3.FuncDecl.mk_func_decl_s z3ctx "AllocExp" [ expr; expr ] boolean_sort

let salloc =
  Z3.FuncDecl.mk_func_decl_s z3ctx "SAllocExp" [ expr; str_literal ]
    boolean_sort

let assume =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Assume" [ node; expr ] boolean_sort

let lval_exp =
  Z3.FuncDecl.mk_func_decl_s z3ctx "LvalExp" [ expr; lval ] boolean_sort

let var =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Var" [ lval; identifier ] boolean_sort

let index =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Index" [ lval; lval; expr ] boolean_sort

let deref = Z3.FuncDecl.mk_func_decl_s z3ctx "Mem" [ lval; expr ] boolean_sort
let field = Z3.FuncDecl.mk_func_decl_s z3ctx "Field" [ lval; lval ] boolean_sort

let addrof =
  Z3.FuncDecl.mk_func_decl_s z3ctx "AddrOf" [ expr; lval ] boolean_sort

let call =
  Z3.FuncDecl.mk_func_decl_s z3ctx "CallExp" [ expr; expr; arg_list ]
    boolean_sort

let libcall =
  Z3.FuncDecl.mk_func_decl_s z3ctx "LibCallExp" [ expr; expr; arg_list ]
    boolean_sort

let arg =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Arg"
    [ arg_list; int_sort; expr ]
    boolean_sort

let constexp = Z3.FuncDecl.mk_func_decl_s z3ctx "ConstExp" [ expr ] boolean_sort
let ret = Z3.FuncDecl.mk_func_decl_s z3ctx "Return" [ node; expr ] boolean_sort
let cast = Z3.FuncDecl.mk_func_decl_s z3ctx "Cast" [ expr; expr ] boolean_sort

let binop =
  Z3.FuncDecl.mk_func_decl_s z3ctx "BinOpExp"
    [ expr; binop_sort; expr; expr ]
    boolean_sort

let unop =
  Z3.FuncDecl.mk_func_decl_s z3ctx "UnOpExp" [ expr; unop_sort; expr ]
    boolean_sort

(* TODO: add extra relations for expr *)
let cfpath =
  Z3.FuncDecl.mk_func_decl_s z3ctx "CFPath" [ node; node ] boolean_sort

let deduedge =
  Z3.FuncDecl.mk_func_decl_s z3ctx "DetailedDUEdge" [ node; node; loc ]
    boolean_sort

let duedge =
  Z3.FuncDecl.mk_func_decl_s z3ctx "DUEdge" [ node; node ] boolean_sort

let dupath =
  Z3.FuncDecl.mk_func_decl_s z3ctx "DUPath" [ node; node ] boolean_sort

let evallv =
  Z3.FuncDecl.mk_func_decl_s z3ctx "EvalLv" [ node; lval; loc ] boolean_sort

let eval =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Eval" [ node; expr; value ] boolean_sort

let memory =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Memory" [ node; loc; value ] boolean_sort

let arrval =
  Z3.FuncDecl.mk_func_decl_s z3ctx "ArrVal" [ value; bv_sort ] boolean_sort

let strval =
  Z3.FuncDecl.mk_func_decl_s z3ctx "StrVal" [ value; bv_sort ] boolean_sort

let conststr =
  Z3.FuncDecl.mk_func_decl_s z3ctx "ConstStr" [ value; const ] boolean_sort

let sizeof =
  Z3.FuncDecl.mk_func_decl_s z3ctx "SizeOf" [ value; bv_sort ] boolean_sort

let strlen =
  Z3.FuncDecl.mk_func_decl_s z3ctx "StrLen" [ value; bv_sort ] boolean_sort

let val_rel =
  Z3.FuncDecl.mk_func_decl_s z3ctx "Val" [ value; bv_sort ] boolean_sort

let alarm = Z3.FuncDecl.mk_func_decl_s z3ctx "Alarm" [ node; node ] boolean_sort
let reach = Z3.FuncDecl.mk_func_decl_s z3ctx "Reach" [ node ] boolean_sort

let ioerror =
  Z3.FuncDecl.mk_func_decl_s z3ctx "IOError" [ node; bv_sort ] boolean_sort

let dzerror =
  Z3.FuncDecl.mk_func_decl_s z3ctx "DZError" [ node; bv_sort ] boolean_sort

let errtrace =
  Z3.FuncDecl.mk_func_decl_s z3ctx "ErrTrace" [ node; node ] boolean_sort

let bug = Z3.FuncDecl.mk_func_decl_s z3ctx "Bug" [] boolean_sort

let z3env =
  {
    z3ctx;
    boolean_sort;
    int_sort;
    bv_sort;
    str_sort;
    zero;
    one;
    two;
    three;
    node;
    lval;
    expr;
    binop_sort;
    unop_sort;
    identifier;
    arg_list;
    str_literal;
    loc;
    value;
    const;
    src;
    snk;
    skip;
    set;
    copy;
    alloc;
    salloc;
    assume;
    lval_exp;
    var;
    index;
    deref;
    field;
    addrof;
    call;
    libcall;
    arg;
    constexp;
    ret;
    cast;
    binop;
    unop;
    cfpath;
    deduedge;
    duedge;
    dupath;
    evallv;
    eval;
    memory;
    arrval;
    strval;
    conststr;
    sizeof;
    strlen;
    val_rel;
    alarm;
    reach;
    ioerror;
    dzerror;
    errtrace;
    bug;
  }
