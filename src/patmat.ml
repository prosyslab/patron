module Y = Yojson

let z3ctx =
  Z3.mk_context [ ("model", "true"); ("proof", "true"); ("unsat_core", "true") ]

let solver =
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

let boolean_sort = Z3.Boolean.mk_sort z3ctx
let int_sort = Z3.Arithmetic.Integer.mk_sort z3ctx
let str_sort = Z3.Seq.mk_string_sort z3ctx
let zero = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 0
let one = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 1
let two = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 2
let three = Z3.Arithmetic.Integer.mk_numeral_i z3ctx 3

let fact func args =
  Z3.Fixedpoint.add_rule solver (Z3.FuncDecl.apply func args) None

let make_rule vars cons =
  Z3.Quantifier.mk_forall_const z3ctx vars cons None [] [] None None
  |> Z3.Quantifier.expr_of_quantifier

module AST = struct
  let node = Z3.FiniteDomain.mk_sort_s z3ctx "node" 65536L
  let lval = Z3.FiniteDomain.mk_sort_s z3ctx "lval" 65536L
  let expr = Z3.FiniteDomain.mk_sort_s z3ctx "expr" 65536L
  let identifier = Z3.FiniteDomain.mk_sort_s z3ctx "identifier" 65536L
  let arg_list = Z3.FiniteDomain.mk_sort_s z3ctx "arg_list" 65536L
  let str_literal = Z3.FiniteDomain.mk_sort_s z3ctx "str_literal" 65536L
  let skip = Z3.FuncDecl.mk_func_decl_s z3ctx "Skip" [ node ] boolean_sort

  let set =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Set" [ node; lval; expr ] boolean_sort

  let alloc =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Alloc" [ node; lval; expr ] boolean_sort

  let salloc =
    Z3.FuncDecl.mk_func_decl_s z3ctx "SAlloc" [ node; lval ] boolean_sort

  let lval_exp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "LvalExp" [ expr; lval ] boolean_sort

  let var =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Var" [ lval; identifier ] boolean_sort

  let call =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Call"
      [ node; lval; expr; arg_list ]
      boolean_sort

  let arg =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Arg"
      [ arg_list; int_sort; expr ]
      boolean_sort

  (* SubExp e1 e2: e2 is subexp of e1 *)
  let subexp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "SubExp" [ expr; expr ] boolean_sort

  let constexp =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ConstExp" [ expr ] boolean_sort

  let ret =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Return" [ node; expr ] boolean_sort
  (* TODO: add extra relations for expr *)
end

module Dataflow = struct
  let node = AST.node

  let duedge =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUEdge" [ node; node ] boolean_sort

  let dupath =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUPath" [ node; node ] boolean_sort
end

let bug = Z3.FuncDecl.mk_func_decl_s z3ctx "bug" [] boolean_sort

let _ =
  Z3.Fixedpoint.register_relation solver AST.skip;
  Z3.Fixedpoint.register_relation solver AST.set;
  Z3.Fixedpoint.register_relation solver AST.alloc;
  Z3.Fixedpoint.register_relation solver AST.salloc;
  Z3.Fixedpoint.register_relation solver AST.lval_exp;
  Z3.Fixedpoint.register_relation solver AST.var;
  Z3.Fixedpoint.register_relation solver AST.call;
  Z3.Fixedpoint.register_relation solver AST.arg;
  Z3.Fixedpoint.register_relation solver AST.subexp;
  Z3.Fixedpoint.register_relation solver AST.constexp;
  Z3.Fixedpoint.register_relation solver AST.ret;
  Z3.Fixedpoint.register_relation solver Dataflow.duedge;
  Z3.Fixedpoint.register_relation solver Dataflow.dupath;
  Z3.Fixedpoint.register_relation solver bug

let facts =
  [
    ("Alloc.facts", AST.alloc, [ AST.node; AST.lval; AST.expr ]);
    ("Arg.facts", AST.arg, [ AST.arg_list; int_sort; AST.expr ]);
    ("Assign.facts", AST.set, [ AST.node; AST.lval; AST.expr ]);
    (* "Assume.facts" *)
    (* "BAnd.facts", *)
    (* "BinOpExp.facts" *)
    (* "BNot.facts" *)
    (* "BOr.facts" *)
    (* "BXor.facts" *)
    ("Call.facts", AST.call, [ AST.node; AST.lval; AST.expr; AST.arg_list ]);
    (* "CastExp.facts" *)
    (* "Cmd.facts" *)
    (* "ConstExp.facts" *)
    (* "Div.facts" *)
    ("DUEdge.facts", Dataflow.duedge, [ Dataflow.node; Dataflow.node ]);
    (* "Entry.facts" *)
    (* "Eq.facts" *)
    (* "Exit.facts" *)
    (* "Exp.map" *)
    (* "FalseBranch.facts" *)
    (* "FalseCond.facts" *)
    (* "Field.facts" *)
    (* "Func.facts" *)
    (* "Ge.facts" *)
    ("GlobalVar.facts", AST.var, [ AST.lval; AST.identifier ]);
    (* "Gt.facts" *)
    (* "IndexPI.facts" *)
    (* "Join.facts" *)
    (* "LAnd.facts" *)
    (* "Le.facts" *)
    ("LibCall.facts", AST.call, [ AST.node; AST.lval; AST.expr; AST.arg_list ]);
    (* "LNot.facts" *)
    ("LocalVar.facts", AST.var, [ AST.lval; AST.identifier ]);
    (* "LoopHead.facts" *)
    (* "LOr.facts" *)
    (* "Lt.facts" *)
    ("LvalExp.facts", AST.lval_exp, [ AST.expr; AST.lval ]);
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
    ("Return.facts", AST.ret, [ AST.node; AST.expr ]);
    ("SAlloc.facts", AST.salloc, [ AST.node; AST.lval ]);
    (* "ShiftLt.facts" *)
    (* "ShiftRt.facts" *)
    ("Skip.facts", AST.skip, [ AST.node ]);
    (* "Start.facts" *)
    (* "StartOf.facts" *)
    (* "TrueBranch.facts" *)
    (* "TrueCond.facts" *)
    (* "UnOpExp.facts" *)
  ]

let sym_map = Hashtbl.create 1000
let cnt = ref 0

let z3_add_symbol args sym sort =
  if Hashtbl.mem sym_map sym then
    let z3sym = Hashtbl.find sym_map sym in
    z3sym :: args
  else
    let z3sym = Z3.Expr.mk_numeral_int z3ctx !cnt sort in
    Hashtbl.add sym_map sym z3sym;
    incr cnt;
    z3sym :: args

let mk_facts work_dir =
  Hashtbl.reset sym_map;
  let datalog_dir = Filename.concat work_dir "sparrow-out/interval/datalog" in
  let mk_fact (fact_file, func, arg_sorts) =
    (* Logger.log "mk_fact: %s" fact_file; *)
    let fact_file_path = Filename.concat datalog_dir fact_file in
    let ic = open_in fact_file_path in
    let rec loop () =
      try
        let line = input_line ic in
        let args =
          List.fold_left2 z3_add_symbol []
            (String.split_on_char '\t' line)
            arg_sorts
          |> List.rev
        in
        (* List.iter (fun arg -> Logger.log "%s\n" (Z3.Expr.to_string arg)) args; *)
        fact func args;
        loop ()
      with End_of_file -> ()
    in
    loop ();
    close_in ic
  in
  List.iter mk_fact facts;
  Logger.log "Symbol table:";
  Hashtbl.iter
    (fun sym z3sym -> Logger.log "%s -> %s" (Z3.Expr.to_string z3sym) sym)
    sym_map

let abstract_bug_pattern work_dir = ()
(* let src = Z3.Expr.mk_const_s z3ctx "src" AST.stmt in *)
(* let snk = Z3.Expr.mk_const_s z3ctx "snk" AST.stmt in *)
(* let lv = Z3.Expr.mk_const_s z3ctx "lv" AST.expr in *)
(* let rv = Z3.Expr.mk_const_s z3ctx "rv" AST.expr in *)
(* let getenv = Z3.Expr.mk_const_s z3ctx "getenv" AST.identifier in *)
(* let args0 = Z3.Expr.mk_const_s z3ctx "args0" AST.arg_list in *)
(* let call = Z3.Expr.mk_const_s z3ctx "call" AST.expr in *)
(* let sprintf = Z3.Expr.mk_const_s z3ctx "sprintf" AST.identifier in *)
(* let args1 = Z3.Expr.mk_const_s z3ctx "args1" AST.arg_list in *)
(* let arg10 = Z3.Expr.mk_const_s z3ctx "arg10" AST.expr in *)
(* let h = Z3.Expr.mk_const_s z3ctx "h" AST.identifier in *)
(* let nop = Z3.Expr.mk_const_s z3ctx "_" AST.expr in *)

(* let predicate = *)
(*   Z3.Boolean.mk_and z3ctx *)
(*     [ *)
(*       Z3.FuncDecl.apply AST.set [ src; lv; rv ]; *)
(*       Z3.FuncDecl.apply AST.call [ rv; getenv; args0 ]; *)
(*       Z3.FuncDecl.apply AST.set [ snk; nop; call ]; *)
(*       Z3.FuncDecl.apply AST.call [ call; sprintf; args1 ]; *)
(*       Z3.FuncDecl.apply AST.arg [ args1; zero; arg10 ]; *)
(*       Z3.FuncDecl.apply AST.var [ arg10; h ]; *)
(*       Z3.FuncDecl.apply Dataflow.dupath [ src; snk ]; *)
(*     ] *)
(* in *)
(* let bug = Z3.FuncDecl.apply bug [] in *)
(* let vars = *)
(*   [ src; snk; lv; rv; getenv; args0; call; sprintf; args1; arg10; h; nop ] *)
(* in *)
(* make_rule vars (Z3.Boolean.mk_implies z3ctx predicate bug) |> fun rule -> *)
(* Z3.Fixedpoint.add_rule solver rule None *)

let pattern_match work_dir =
  Logger.log "Pattern matching...";
  mk_facts work_dir;
  Logger.log "Make facts done";
  abstract_bug_pattern work_dir;
  Logger.log "Make pattern done";
  Logger.log "SMT Encoding Result:\n%s" (Z3.Fixedpoint.to_string solver);
  let status = Z3.Fixedpoint.query solver (Z3.FuncDecl.apply bug []) in
  match status with
  | Z3.Solver.UNSATISFIABLE -> print_endline "No bug found"
  | Z3.Solver.SATISFIABLE -> (
      print_endline "Bug found";
      match Z3.Fixedpoint.get_answer solver with
      | None -> print_endline "No answer"
      | Some answer ->
          print_endline "Instances:";
          answer |> Z3.Expr.to_string |> print_endline)
  | Z3.Solver.UNKNOWN -> print_endline "Unknown"
