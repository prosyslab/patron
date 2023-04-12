type t = {
  z3ctx : Z3.context;
  donor_solver : Z3.Fixedpoint.fixedpoint;
  patch_solver : Z3.Fixedpoint.fixedpoint;
  donee_solver : Z3.Fixedpoint.fixedpoint;
  pattern_solver : Z3.Fixedpoint.fixedpoint;
  boolean_sort : Z3.Sort.sort;
  int_sort : Z3.Sort.sort;
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
  value : Z3.Sort.sort;
  const : Z3.Sort.sort;
  (* Functions for specifying source, sink *)
  src : Z3.FuncDecl.func_decl;
  snk : Z3.FuncDecl.func_decl;
  skip : Z3.FuncDecl.func_decl;
  set : Z3.FuncDecl.func_decl;
  alloc : Z3.FuncDecl.func_decl;
  salloc : Z3.FuncDecl.func_decl;
  lval_exp : Z3.FuncDecl.func_decl;
  startof : Z3.FuncDecl.func_decl;
  var : Z3.FuncDecl.func_decl;
  call : Z3.FuncDecl.func_decl;
  libcall : Z3.FuncDecl.func_decl;
  arg : Z3.FuncDecl.func_decl;
  (* SubExp e1 e2: e2 is subexp of e1 *)
  subexp : Z3.FuncDecl.func_decl;
  constexp : Z3.FuncDecl.func_decl;
  ret : Z3.FuncDecl.func_decl;
  (* TODO: add extra relations for expr *)
  binop : Z3.FuncDecl.func_decl;
  unop : Z3.FuncDecl.func_decl;
  dupath : Z3.FuncDecl.func_decl;
  (* Functions for Semantic Constraint *)
  evallv : Z3.FuncDecl.func_decl;
  eval : Z3.FuncDecl.func_decl;
  memory : Z3.FuncDecl.func_decl;
  arrayval : Z3.FuncDecl.func_decl;
  conststr : Z3.FuncDecl.func_decl;
  sizeof : Z3.FuncDecl.func_decl;
  strlen : Z3.FuncDecl.func_decl;
  intval : Z3.FuncDecl.func_decl;
  alarm : Z3.FuncDecl.func_decl;
  bug : Z3.FuncDecl.func_decl;
  facts : (string * Z3.FuncDecl.func_decl * Z3.Sort.sort list) list;
  rels : string list;
}

let add_fact solver func args =
  Z3.Fixedpoint.add_rule solver (Z3.FuncDecl.apply func args) None

let mk_rule z3ctx vars cons =
  Z3.Quantifier.mk_forall_const z3ctx vars cons None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

let mk_fixedpoint z3ctx =
  let mk_string_symbol s = Z3.Symbol.mk_string z3ctx s in
  let s = Z3.Fixedpoint.mk_fixedpoint z3ctx in
  let param = Z3.Params.mk_params z3ctx in
  Z3.Params.add_symbol param
    (mk_string_symbol "engine")
    (mk_string_symbol "spacer");
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
  Z3.Fixedpoint.register_relation solver env.alloc;
  Z3.Fixedpoint.register_relation solver env.salloc;
  Z3.Fixedpoint.register_relation solver env.lval_exp;
  Z3.Fixedpoint.register_relation solver env.startof;
  Z3.Fixedpoint.register_relation solver env.var;
  Z3.Fixedpoint.register_relation solver env.call;
  Z3.Fixedpoint.register_relation solver env.libcall;
  Z3.Fixedpoint.register_relation solver env.arg;
  Z3.Fixedpoint.register_relation solver env.subexp;
  Z3.Fixedpoint.register_relation solver env.constexp;
  Z3.Fixedpoint.register_relation solver env.ret;
  Z3.Fixedpoint.register_relation solver env.binop;
  Z3.Fixedpoint.register_relation solver env.unop;
  Z3.Fixedpoint.register_relation solver env.dupath;
  Z3.Fixedpoint.register_relation solver env.evallv;
  Z3.Fixedpoint.register_relation solver env.eval;
  Z3.Fixedpoint.register_relation solver env.memory;
  Z3.Fixedpoint.register_relation solver env.arrayval;
  Z3.Fixedpoint.register_relation solver env.conststr;
  Z3.Fixedpoint.register_relation solver env.alarm;
  Z3.Fixedpoint.register_relation solver env.bug

let mk_env () =
  let z3ctx =
    Z3.mk_context
      [ ("model", "true"); ("proof", "true"); ("unsat_core", "true") ]
  in
  let donor_solver = mk_fixedpoint z3ctx in
  let patch_solver = mk_fixedpoint z3ctx in
  let donee_solver = mk_fixedpoint z3ctx in
  let pattern_solver = mk_fixedpoint z3ctx in
  let boolean_sort = Z3.Boolean.mk_sort z3ctx in
  let int_sort = Z3.Arithmetic.Integer.mk_sort z3ctx in
  let str_sort = Z3.Seq.mk_string_sort z3ctx in
  let zero = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 0 in
  let one = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 1 in
  let two = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 2 in
  let three = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 3 in
  let node = Z3.FiniteDomain.mk_sort_s z3ctx "node" 65536L in
  let lval = Z3.FiniteDomain.mk_sort_s z3ctx "lval" 65536L in
  let expr = Z3.FiniteDomain.mk_sort_s z3ctx "expr" 65536L in
  let binop_sort = Z3.FiniteDomain.mk_sort_s z3ctx "binop" 65536L in
  let unop_sort = Z3.FiniteDomain.mk_sort_s z3ctx "unop" 65536L in
  let identifier = Z3.FiniteDomain.mk_sort_s z3ctx "identifier" 65536L in
  let arg_list = Z3.FiniteDomain.mk_sort_s z3ctx "arg_list" 65536L in
  let str_literal = Z3.FiniteDomain.mk_sort_s z3ctx "str_literal" 65536L in
  let value = Z3.FiniteDomain.mk_sort_s z3ctx "value" 65536L in
  let const = Z3.FiniteDomain.mk_sort_s z3ctx "const" 65536L in
  let src = Z3.FuncDecl.mk_func_decl_s z3ctx "Src" [ node ] boolean_sort in
  let snk = Z3.FuncDecl.mk_func_decl_s z3ctx "Snk" [ node ] boolean_sort in
  let skip = Z3.FuncDecl.mk_func_decl_s z3ctx "Skip" [ node ] boolean_sort in
  let set =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Set" [ node; lval; expr ] boolean_sort
  in
  let alloc =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Alloc" [ node; lval; expr ] boolean_sort
  in
  let salloc =
    Z3.FuncDecl.mk_func_decl_s z3ctx "SAlloc" [ node; lval ] boolean_sort
  in
  let lval_exp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "LvalExp" [ expr; lval ] boolean_sort
  in
  let startof =
    Z3.FuncDecl.mk_func_decl_s z3ctx "StartOf" [ expr; lval ] boolean_sort
  in
  let var =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Var" [ lval; identifier ] boolean_sort
  in
  let call =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Call"
      [ node; lval; expr; arg_list ]
      boolean_sort
  in
  let libcall =
    Z3.FuncDecl.mk_func_decl_s z3ctx "LibCall"
      [ node; lval; expr; arg_list ]
      boolean_sort
  in
  let arg =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Arg"
      [ arg_list; int_sort; expr ]
      boolean_sort
  in
  (* SubExp e1 e2: e2 is subexp of e1 *)
  let subexp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "SubExp" [ expr; expr ] boolean_sort
  in
  let constexp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ConstExp" [ expr ] boolean_sort
  in
  let ret =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Return" [ node; expr ] boolean_sort
  in
  let binop =
    Z3.FuncDecl.mk_func_decl_s z3ctx "BinOp"
      [ expr; binop_sort; expr; expr ]
      boolean_sort
  in
  let unop =
    Z3.FuncDecl.mk_func_decl_s z3ctx "UnOp" [ expr; unop_sort; expr ]
      boolean_sort
  in
  (* TODO: add extra relations for expr *)
  let dupath =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUPath" [ node; node ] boolean_sort
  in
  let evallv =
    Z3.FuncDecl.mk_func_decl_s z3ctx "EvalLv" [ node; lval; value ] boolean_sort
  in
  let eval =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Eval" [ node; expr; value ] boolean_sort
  in
  let memory =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Memory" [ node; value; value ]
      boolean_sort
  in
  let arrayval =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ArrayVal" [ value; value ] boolean_sort
  in
  let conststr =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ConstStr" [ value; const ] boolean_sort
  in

  let sizeof = Z3.FuncDecl.mk_func_decl_s z3ctx "SizeOf" [ value ] int_sort in
  let strlen = Z3.FuncDecl.mk_func_decl_s z3ctx "StrLen" [ value ] int_sort in
  let intval = Z3.FuncDecl.mk_func_decl_s z3ctx "IntVal" [ value ] int_sort in
  let alarm = Z3.FuncDecl.mk_func_decl_s z3ctx "Alarm" [ node ] boolean_sort in
  let bug = Z3.FuncDecl.mk_func_decl_s z3ctx "bug" [] boolean_sort in
  let facts =
    [
      ("Alloc.facts", alloc, [ node; lval; expr ]);
      ("Arg.facts", arg, [ arg_list; int_sort; expr ]);
      ("Assign.facts", set, [ node; lval; expr ]);
      (* "Assume.facts" *)
      ("BinOpExp.facts", binop, [ expr; binop_sort; expr; expr ]);
      ("Call.facts", call, [ node; lval; expr; arg_list ]);
      (* "Cxp.facts" *)
      (* "Cmd.facts" *)
      (* "ConstExp.facts" *)
      (* "Div.facts" *)
      ("DUPath.facts", dupath, [ node; node ]);
      (* "Entry.facts" *)
      (* "Eq.facts" *)
      (* "Exit.facts" *)
      (* "FalseBranch.facts" *)
      (* "FalseCond.facts" *)
      (* "Field.facts" *)
      (* "Func.facts" *)
      ("GlobalVar.facts", var, [ lval; identifier ]);
      (* "Join.facts" *)
      ("LibCall.facts", libcall, [ node; lval; expr; arg_list ]);
      ("LocalVar.facts", var, [ lval; identifier ]);
      (* "LoopHead.facts" *)
      ("LvalExp.facts", lval_exp, [ expr; lval ]);
      (* "Lval.facts" *)
      (* "Mem.facts" *)
      (* "MinusA.facts" *)
      (* "MinusPI.facts" *)
      (* "MinusPP.facts" *)
      (* "Mod.facts" *)
      (* "Mult.facts" *)
      (* "Ne.facts" *)
      (* "Neg.facts" *)
      (* "OtherExp.facts" *)
      ("Return.facts", ret, [ node; expr ]);
      ("SAlloc.facts", salloc, [ node; lval ]);
      ("Skip.facts", skip, [ node ]);
      ("StartOf.facts", startof, [ expr; lval ]);
      (* "TrueBranch.facts" *)
      (* "TrueCond.facts" *)
      ("UnOpExp.facts", unop, [ expr; unop_sort; expr ]);
      ("EvalLv.facts", evallv, [ node; lval; value ]);
      ("Eval.facts", eval, [ node; expr; value ]);
      ("Memory.facts", memory, [ node; value; value ]);
      ("ArrayVal.facts", arrayval, [ value; value ]);
      ("ConstStr.facts", conststr, [ value; const ]);
      ("SubExp.facts", subexp, [ expr; expr ]);
    ]
  in
  let rels =
    [
      "Alloc";
      "Arg";
      "Set";
      "Call";
      "DUPath";
      "Var";
      "LibCall";
      "LvalExp";
      "Return";
      "SubExp";
      "BinOp";
      "UnOp";
      "SAlloc";
      "Skip";
      "StartOf";
      "EvalLv";
      "Eval";
      "Memory";
      "ArrayVal";
      "ConstStr";
      "Alarm";
    ]
  in
  let env =
    {
      z3ctx;
      donor_solver;
      patch_solver;
      donee_solver;
      pattern_solver;
      boolean_sort;
      int_sort;
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
      value;
      const;
      src;
      snk;
      skip;
      set;
      alloc;
      salloc;
      lval_exp;
      startof;
      var;
      call;
      libcall;
      arg;
      subexp;
      constexp;
      ret;
      binop;
      unop;
      dupath;
      evallv;
      eval;
      memory;
      arrayval;
      conststr;
      sizeof;
      strlen;
      intval;
      alarm;
      bug;
      facts;
      rels;
    }
  in
  reg_rel_to_solver env env.donor_solver;
  reg_rel_to_solver env env.patch_solver;
  reg_rel_to_solver env env.donee_solver;
  reg_rel_to_solver env env.pattern_solver;
  env

let reset () =
  Z3.Memory.reset ();
  mk_env ()
