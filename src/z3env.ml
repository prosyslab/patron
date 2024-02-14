open Core
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module F = Format

let _ = Z3.set_global_param "memory_high_watermark" "4294967295"

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
  ast_node : Z3.Sort.sort;
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
  ast_parent : Z3.FuncDecl.func_decl;
  eq_node : Z3.FuncDecl.func_decl;
  src : Z3.FuncDecl.func_decl;
  snk : Z3.FuncDecl.func_decl;
  skip : Z3.FuncDecl.func_decl;
  set : Z3.FuncDecl.func_decl;
  alloc : Z3.FuncDecl.func_decl;
  salloc : Z3.FuncDecl.func_decl;
  assume : Z3.FuncDecl.func_decl;
  lval_exp : Z3.FuncDecl.func_decl;
  var : Z3.FuncDecl.func_decl;
  index : Z3.FuncDecl.func_decl;
  deref : Z3.FuncDecl.func_decl;
  addrof : Z3.FuncDecl.func_decl;
  call : Z3.FuncDecl.func_decl;
  libcall : Z3.FuncDecl.func_decl;
  arg : Z3.FuncDecl.func_decl;
  constexp : Z3.FuncDecl.func_decl;
  ret : Z3.FuncDecl.func_decl;
  (* TODO: add extra relations for expr *)
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
  Z3.Fixedpoint.register_relation solver env.eq_node;
  Z3.Fixedpoint.register_relation solver env.ast_parent;
  Z3.Fixedpoint.register_relation solver env.src;
  Z3.Fixedpoint.register_relation solver env.snk;
  Z3.Fixedpoint.register_relation solver env.skip;
  Z3.Fixedpoint.register_relation solver env.set;
  Z3.Fixedpoint.register_relation solver env.alloc;
  Z3.Fixedpoint.register_relation solver env.salloc;
  Z3.Fixedpoint.register_relation solver env.assume;
  Z3.Fixedpoint.register_relation solver env.lval_exp;
  Z3.Fixedpoint.register_relation solver env.var;
  Z3.Fixedpoint.register_relation solver env.index;
  Z3.Fixedpoint.register_relation solver env.deref;
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
    "AddrOf.facts";
    "Return.facts";
    "Set.facts";
    "Skip.facts";
    "UnOpExp.facts";
    "Assume.facts";
    "EvalLv.facts";
  ]

let sort_size = ref 25

let mk_env () =
  let z3ctx =
    Z3.mk_context
      [ ("model", "true"); ("proof", "true"); ("unsat_core", "true") ]
  in
  let boolean_sort = Z3.Boolean.mk_sort z3ctx in
  let int_sort =
    Z3.FiniteDomain.mk_sort_s z3ctx "int" (Int64.of_int !sort_size)
  in
  let bv_sort = Z3.BitVector.mk_sort z3ctx 64 (* NOTE: hard coded *) in
  let str_sort = Z3.Seq.mk_string_sort z3ctx in
  let zero = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 0 in
  let one = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 1 in
  let two = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 2 in
  let three = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 3 in
  let node = Z3.FiniteDomain.mk_sort_s z3ctx "node" (Int64.of_int !sort_size) in
  let ast_node =
    Z3.FiniteDomain.mk_sort_s z3ctx "ast_node" (Int64.of_int !sort_size)
  in
  let lval = Z3.FiniteDomain.mk_sort_s z3ctx "lval" (Int64.of_int !sort_size) in
  let expr = Z3.FiniteDomain.mk_sort_s z3ctx "expr" (Int64.of_int !sort_size) in
  let binop_sort = Z3.FiniteDomain.mk_sort_s z3ctx "binop" (Int64.of_int 25) in
  let unop_sort = Z3.FiniteDomain.mk_sort_s z3ctx "unop" (Int64.of_int 25) in
  let identifier =
    Z3.FiniteDomain.mk_sort_s z3ctx "identifier" (Int64.of_int 1)
  in
  let arg_list =
    Z3.FiniteDomain.mk_sort_s z3ctx "arg_list" (Int64.of_int !sort_size)
  in
  let str_literal =
    Z3.FiniteDomain.mk_sort_s z3ctx "str_literal" (Int64.of_int !sort_size)
  in
  let loc = Z3.FiniteDomain.mk_sort_s z3ctx "loc" (Int64.of_int !sort_size) in
  let value =
    Z3.FiniteDomain.mk_sort_s z3ctx "value" (Int64.of_int !sort_size)
  in
  let const =
    Z3.FiniteDomain.mk_sort_s z3ctx "const" (Int64.of_int !sort_size)
  in
  let ast_parent =
    Z3.FuncDecl.mk_func_decl_s z3ctx "AstParent" [ ast_node; ast_node ]
      boolean_sort
  in
  let eq_node =
    Z3.FuncDecl.mk_func_decl_s z3ctx "EqNode" [ node; ast_node ] boolean_sort
  in
  let src = Z3.FuncDecl.mk_func_decl_s z3ctx "Src" [ node ] boolean_sort in
  let snk = Z3.FuncDecl.mk_func_decl_s z3ctx "Snk" [ node ] boolean_sort in
  let skip = Z3.FuncDecl.mk_func_decl_s z3ctx "Skip" [ node ] boolean_sort in
  let set =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Set" [ node; lval; expr ] boolean_sort
  in
  let alloc =
    Z3.FuncDecl.mk_func_decl_s z3ctx "AllocExp" [ expr; expr ] boolean_sort
  in
  let salloc =
    Z3.FuncDecl.mk_func_decl_s z3ctx "SAllocExp" [ expr; str_literal ]
      boolean_sort
  in
  let assume =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Assume" [ node; expr ] boolean_sort
  in
  let lval_exp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "LvalExp" [ expr; lval ] boolean_sort
  in
  let var =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Var" [ lval; identifier ] boolean_sort
  in
  let index =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Index" [ lval; lval; expr ] boolean_sort
  in
  let deref =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Mem" [ lval; expr ] boolean_sort
  in
  let addrof =
    Z3.FuncDecl.mk_func_decl_s z3ctx "AddrOf" [ expr; lval ] boolean_sort
  in
  let call =
    Z3.FuncDecl.mk_func_decl_s z3ctx "CallExp" [ expr; expr; arg_list ]
      boolean_sort
  in
  let libcall =
    Z3.FuncDecl.mk_func_decl_s z3ctx "LibCallExp" [ expr; expr; arg_list ]
      boolean_sort
  in
  let arg =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Arg"
      [ arg_list; int_sort; expr ]
      boolean_sort
  in
  let constexp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ConstExp" [ expr ] boolean_sort
  in
  let ret =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Return" [ node; expr ] boolean_sort
  in
  let cast =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Cast" [ expr; expr ] boolean_sort
  in
  let binop =
    Z3.FuncDecl.mk_func_decl_s z3ctx "BinOpExp"
      [ expr; binop_sort; expr; expr ]
      boolean_sort
  in
  let unop =
    Z3.FuncDecl.mk_func_decl_s z3ctx "UnOpExp" [ expr; unop_sort; expr ]
      boolean_sort
  in
  (* TODO: add extra relations for expr *)
  let cfpath =
    Z3.FuncDecl.mk_func_decl_s z3ctx "CFPath" [ node; node ] boolean_sort
  in
  let deduedge =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DetailedDUEdge" [ node; node; loc ]
      boolean_sort
  in
  let duedge =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUEdge" [ node; node ] boolean_sort
  in
  let dupath =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUPath" [ node; node ] boolean_sort
  in
  let evallv =
    Z3.FuncDecl.mk_func_decl_s z3ctx "EvalLv" [ node; lval; loc ] boolean_sort
  in
  let eval =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Eval" [ node; expr; value ] boolean_sort
  in
  let memory =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Memory" [ node; loc; value ] boolean_sort
  in
  let arrval =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ArrVal" [ value; bv_sort ] boolean_sort
  in
  let strval =
    Z3.FuncDecl.mk_func_decl_s z3ctx "StrVal" [ value; bv_sort ] boolean_sort
  in
  let conststr =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ConstStr" [ value; const ] boolean_sort
  in

  let sizeof =
    Z3.FuncDecl.mk_func_decl_s z3ctx "SizeOf" [ value; bv_sort ] boolean_sort
  in
  let strlen =
    Z3.FuncDecl.mk_func_decl_s z3ctx "StrLen" [ value; bv_sort ] boolean_sort
  in
  let val_rel =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Val" [ value; bv_sort ] boolean_sort
  in
  let alarm =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Alarm" [ node; node ] boolean_sort
  in
  let reach = Z3.FuncDecl.mk_func_decl_s z3ctx "Reach" [ node ] boolean_sort in
  let ioerror =
    Z3.FuncDecl.mk_func_decl_s z3ctx "IOError" [ node; bv_sort ] boolean_sort
  in
  let dzerror =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DZError" [ node; bv_sort ] boolean_sort
  in
  let errtrace =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ErrTrace" [ node; node ] boolean_sort
  in
  let bug = Z3.FuncDecl.mk_func_decl_s z3ctx "Bug" [] boolean_sort in
  let env =
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
      ast_node;
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
      ast_parent;
      eq_node;
      src;
      snk;
      skip;
      set;
      alloc;
      salloc;
      assume;
      lval_exp;
      var;
      index;
      deref;
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
  in
  env

let get_env () =
  Z3.Memory.reset ();
  mk_env ()
