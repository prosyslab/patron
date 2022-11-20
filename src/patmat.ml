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

module AST = struct
  (* TODO: pick necessary ast nodes as logical relations in clang ast *)
  type t = TranslationUnitDecl | TypedefDecl | FunctionDecl | CompoundStmt
end

module Node = struct
  type t = { id : int; name : string; line : int }
end

module Dataflow = struct
  type t = DUEdge of Node.t * Node.t
end

(* TODO: make facts from given ast & dataflow *)
let mk_facts (ast : AST.t) (dataflow : Dataflow.t) = ()

let extract_bug_pattern () =
  (* Hard coding for the time being *)
  ()

let pattern_match work_dir = ()
