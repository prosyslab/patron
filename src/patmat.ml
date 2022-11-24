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
  (* TODO: pick necessary ast nodes as logical relations in clang ast *)
  let stmt = Z3.FiniteDomain.mk_sort_s z3ctx "stmt" 65536L
  let expr = Z3.FiniteDomain.mk_sort_s z3ctx "expr" 65536L
  let arg_list = Z3.FiniteDomain.mk_sort_s z3ctx "arg_list" 65536L
  let identifier = Z3.FiniteDomain.mk_sort_s z3ctx "identifier" 65536L
  let str_literal = Z3.FiniteDomain.mk_sort_s z3ctx "str_literal" 65536L

  let set =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Set" [ stmt; expr; expr ] boolean_sort

  let var =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Var" [ expr; identifier ] boolean_sort

  let call =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Call"
      [ expr; identifier; arg_list ]
      boolean_sort

  let arg =
    Z3.FuncDecl.mk_func_decl_s z3ctx "Arg"
      [ arg_list; int_sort; expr ]
      boolean_sort

  let const_str =
    Z3.FuncDecl.mk_func_decl_s z3ctx "ConstStr" [ expr; str_literal ]
      boolean_sort
end

module Dataflow = struct
  let stmt = AST.stmt

  let duedge =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUEdge" [ stmt; stmt ] boolean_sort

  let dupath =
    Z3.FuncDecl.mk_func_decl_s z3ctx "DUPath" [ stmt; stmt ] boolean_sort
end

let bug = Z3.FuncDecl.mk_func_decl_s z3ctx "bug" [] boolean_sort

let _ =
  Z3.Fixedpoint.register_relation solver AST.set;
  Z3.Fixedpoint.register_relation solver AST.var;
  Z3.Fixedpoint.register_relation solver AST.call;
  Z3.Fixedpoint.register_relation solver AST.arg;
  Z3.Fixedpoint.register_relation solver AST.const_str;
  Z3.Fixedpoint.register_relation solver Dataflow.duedge;
  Z3.Fixedpoint.register_relation solver Dataflow.dupath;
  Z3.Fixedpoint.register_relation solver bug

(* TODO: make facts from given ast & dataflow *)
let mk_facts () =
  let src = Z3.Expr.mk_numeral_int z3ctx 0 AST.stmt in
  let snk = Z3.Expr.mk_numeral_int z3ctx 1 AST.stmt in
  let lv = Z3.Expr.mk_numeral_int z3ctx 2 AST.expr in
  let rv = Z3.Expr.mk_numeral_int z3ctx 3 AST.expr in
  let getenv = Z3.Expr.mk_numeral_int z3ctx 4 AST.identifier in
  let args0 = Z3.Expr.mk_numeral_int z3ctx 5 AST.arg_list in
  let arg00 = Z3.Expr.mk_numeral_int z3ctx 6 AST.expr in
  let home = Z3.Expr.mk_numeral_int z3ctx 7 AST.str_literal in
  let call = Z3.Expr.mk_numeral_int z3ctx 8 AST.expr in
  let sprintf = Z3.Expr.mk_numeral_int z3ctx 9 AST.identifier in
  let args1 = Z3.Expr.mk_numeral_int z3ctx 10 AST.arg_list in
  let arg10 = Z3.Expr.mk_numeral_int z3ctx 11 AST.expr in
  let h = Z3.Expr.mk_numeral_int z3ctx 12 AST.identifier in
  let arg11 = Z3.Expr.mk_numeral_int z3ctx 13 AST.expr in
  let yourhome = Z3.Expr.mk_numeral_int z3ctx 14 AST.str_literal in
  let arg12 = Z3.Expr.mk_numeral_int z3ctx 15 AST.expr in
  let ptr_h = Z3.Expr.mk_numeral_int z3ctx 16 AST.identifier in
  let nop = Z3.Expr.mk_numeral_int z3ctx 17 AST.expr in

  fact AST.set [ src; lv; rv ];
  fact AST.var [ lv; ptr_h ];
  fact AST.call [ rv; getenv; args0 ];
  fact AST.arg [ args0; zero; arg00 ];
  fact AST.const_str [ arg00; home ];
  fact AST.set [ snk; nop; call ];
  fact AST.call [ call; sprintf; args1 ];
  fact AST.arg [ args1; zero; arg10 ];
  fact AST.var [ arg10; h ];
  fact AST.arg [ args1; one; arg11 ];
  fact AST.const_str [ arg11; yourhome ];
  fact AST.arg [ args1; two; arg12 ];
  fact AST.var [ arg12; ptr_h ];
  fact Dataflow.dupath [ src; snk ]

let extract_bug_pattern () =
  (* Hard coding for the time being *)
  let src = Z3.Expr.mk_const_s z3ctx "src" AST.stmt in
  let snk = Z3.Expr.mk_const_s z3ctx "snk" AST.stmt in
  let lv = Z3.Expr.mk_const_s z3ctx "lv" AST.expr in
  let rv = Z3.Expr.mk_const_s z3ctx "rv" AST.expr in
  let getenv = Z3.Expr.mk_const_s z3ctx "getenv" AST.identifier in
  let args0 = Z3.Expr.mk_const_s z3ctx "args0" AST.arg_list in
  let call = Z3.Expr.mk_const_s z3ctx "call" AST.expr in
  let sprintf = Z3.Expr.mk_const_s z3ctx "sprintf" AST.identifier in
  let args1 = Z3.Expr.mk_const_s z3ctx "args1" AST.arg_list in
  let arg10 = Z3.Expr.mk_const_s z3ctx "arg10" AST.expr in
  let h = Z3.Expr.mk_const_s z3ctx "h" AST.identifier in
  let nop = Z3.Expr.mk_const_s z3ctx "_" AST.expr in

  let predicate =
    Z3.Boolean.mk_and z3ctx
      [
        Z3.FuncDecl.apply AST.set [ src; lv; rv ];
        Z3.FuncDecl.apply AST.call [ rv; getenv; args0 ];
        Z3.FuncDecl.apply AST.set [ snk; nop; call ];
        Z3.FuncDecl.apply AST.call [ call; sprintf; args1 ];
        Z3.FuncDecl.apply AST.arg [ args1; zero; arg10 ];
        Z3.FuncDecl.apply AST.var [ arg10; h ];
        Z3.FuncDecl.apply Dataflow.dupath [ src; snk ];
      ]
  in
  let bug = Z3.FuncDecl.apply bug [] in
  let vars =
    [ src; snk; lv; rv; getenv; args0; call; sprintf; args1; arg10; h; nop ]
  in
  make_rule vars (Z3.Boolean.mk_implies z3ctx predicate bug) |> fun rule ->
  Z3.Fixedpoint.add_rule solver rule None

let pattern_match () =
  print_endline "Pattern matching...";
  mk_facts ();
  print_endline "Make facts done";
  extract_bug_pattern ();
  print_endline "Make pattern done";
  print_endline (Z3.Fixedpoint.to_string solver);
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
