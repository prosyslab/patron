type t = {
  z3ctx : Z3.context;
  donor_solver : Z3.Fixedpoint.fixedpoint;
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
  identifier : Z3.Sort.sort;
  arg_list : Z3.Sort.sort;
  str_literal : Z3.Sort.sort;
  skip : Z3.FuncDecl.func_decl;
  set : Z3.FuncDecl.func_decl;
  alloc : Z3.FuncDecl.func_decl;
  salloc : Z3.FuncDecl.func_decl;
  lval_exp : Z3.FuncDecl.func_decl;
  var : Z3.FuncDecl.func_decl;
  call : Z3.FuncDecl.func_decl;
  arg : Z3.FuncDecl.func_decl;
  (* SubExp e1 e2: e2 is subexp of e1 *)
  subexp : Z3.FuncDecl.func_decl;
  constexp : Z3.FuncDecl.func_decl;
  ret : Z3.FuncDecl.func_decl;
  (* TODO: add extra relations for expr *)
  duedge : Z3.FuncDecl.func_decl;
  dupath : Z3.FuncDecl.func_decl;
  dupath_r0 : Z3.Expr.expr;
  dupath_r1 : Z3.Expr.expr;
  bug : Z3.FuncDecl.func_decl;
  facts : (string * Z3.FuncDecl.func_decl * Z3.Sort.sort list) list;
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
  Z3.Fixedpoint.register_relation solver env.skip;
  Z3.Fixedpoint.register_relation solver env.set;
  Z3.Fixedpoint.register_relation solver env.alloc;
  Z3.Fixedpoint.register_relation solver env.salloc;
  Z3.Fixedpoint.register_relation solver env.lval_exp;
  Z3.Fixedpoint.register_relation solver env.var;
  Z3.Fixedpoint.register_relation solver env.call;
  Z3.Fixedpoint.register_relation solver env.arg;
  Z3.Fixedpoint.register_relation solver env.subexp;
  Z3.Fixedpoint.register_relation solver env.constexp;
  Z3.Fixedpoint.register_relation solver env.ret;
  Z3.Fixedpoint.register_relation solver env.duedge;
  Z3.Fixedpoint.register_relation solver env.dupath;
  Z3.Fixedpoint.register_relation solver env.bug

let mk_env () =
  let z3ctx =
    Z3.mk_context
      [ ("model", "true"); ("proof", "true"); ("unsat_core", "true") ]
  in
  let donor_solver = mk_fixedpoint z3ctx in
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
  let identifier = Z3.FiniteDomain.mk_sort_s z3ctx "identifier" 65536L in
  let arg_list = Z3.FiniteDomain.mk_sort_s z3ctx "arg_list" 65536L in
  let str_literal = Z3.FiniteDomain.mk_sort_s z3ctx "str_literal" 65536L in
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
  let var =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Var" [ lval; identifier ] boolean_sort
  in
  let call =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Call"
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
  (* TODO: add extra relations for expr *)
  let duedge =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUEdge" [ node; node ] boolean_sort
  in
  let dupath =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUPath" [ node; node ] boolean_sort
  in
  let x = Z3.Expr.mk_const_s z3ctx "x" node in
  let y = Z3.Expr.mk_const_s z3ctx "y" node in
  let z = Z3.Expr.mk_const_s z3ctx "z" node in
  let dupath_r0 =
    mk_rule z3ctx [ x; y; z ]
      (Z3.Boolean.mk_implies z3ctx
         (Z3.FuncDecl.apply duedge [ x; y ])
         (Z3.FuncDecl.apply dupath [ x; y ]))
  in
  let dupath_r1 =
    mk_rule z3ctx [ x; y; z ]
      (Z3.Boolean.mk_implies z3ctx
         (Z3.Boolean.mk_and z3ctx
            [
              Z3.FuncDecl.apply duedge [ x; z ];
              Z3.FuncDecl.apply duedge [ z; y ];
            ])
         (Z3.FuncDecl.apply dupath [ x; y ]))
  in
  let bug = Z3.FuncDecl.mk_func_decl_s z3ctx "bug" [] boolean_sort in
  let facts =
    [
      ("Alloc.facts", alloc, [ node; lval; expr ]);
      ("Arg.facts", arg, [ arg_list; int_sort; expr ]);
      ("Assign.facts", set, [ node; lval; expr ]);
      (* "Assume.facts" *)
      (* "BAnd.facts", *)
      (* "BinOpExp.facts" *)
      (* "BNot.facts" *)
      (* "BOr.facts" *)
      (* "BXor.facts" *)
      ("Call.facts", call, [ node; lval; expr; arg_list ]);
      (* "Cxp.facts" *)
      (* "Cmd.facts" *)
      (* "ConstExp.facts" *)
      (* "Div.facts" *)
      ("DUEdge.facts", duedge, [ node; node ]);
      (* "Entry.facts" *)
      (* "Eq.facts" *)
      (* "Exit.facts" *)
      (* "Exp.map" *)
      (* "FalseBranch.facts" *)
      (* "FalseCond.facts" *)
      (* "Field.facts" *)
      (* "Func.facts" *)
      (* "Ge.facts" *)
      ("GlobalVar.facts", var, [ lval; identifier ]);
      (* "Gt.facts" *)
      (* "IndexPI.facts" *)
      (* "Join.facts" *)
      (* "LAnd.facts" *)
      (* "Le.facts" *)
      ("LibCall.facts", call, [ node; lval; expr; arg_list ]);
      (* "LNot.facts" *)
      ("LocalVar.facts", var, [ lval; identifier ]);
      (* "LoopHead.facts" *)
      (* "LOr.facts" *)
      (* "Lt.facts" *)
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
      (* "PlusA.facts" *)
      (* "PlusPI.facts" *)
      ("Return.facts", ret, [ node; expr ]);
      ("SAlloc.facts", salloc, [ node; lval ]);
      (* "ShiftLt.facts" *)
      (* "ShiftRt.facts" *)
      ("Skip.facts", skip, [ node ]);
      (* "Start.facts" *)
      (* "StartOf.facts" *)
      (* "TrueBranch.facts" *)
      (* "TrueCond.facts" *)
      (* "UnOpExp.facts" *)
    ]
  in
  let env =
    {
      z3ctx;
      donor_solver;
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
      identifier;
      arg_list;
      str_literal;
      skip;
      set;
      alloc;
      salloc;
      lval_exp;
      var;
      call;
      arg;
      subexp;
      constexp;
      ret;
      duedge;
      dupath;
      dupath_r0;
      dupath_r1;
      bug;
      facts;
    }
  in
  reg_rel_to_solver env env.donor_solver;
  reg_rel_to_solver env env.donee_solver;
  reg_rel_to_solver env env.pattern_solver;
  env

let reset () =
  Z3.Memory.reset ();
  mk_env ()
