open Core
module Hashtbl = Stdlib.Hashtbl
module J = Yojson.Basic.Util
module F = Format

module CfgNode = struct
  type loc = { file : string; line : int }

  type t =
    | CNone
    | CSet of string * string * loc * string list (* (lv, e, loc) *)
    | CExternal of string * loc * string list (*(lv, loc)*)
    | CAlloc of string * string * loc * string list (*(lv, Array e, _, loc) *)
    | CSalloc of string * string * loc * string list (*(lv, s, loc) *)
    | CFalloc of string * string * loc * string list (*(lv, f, loc) *)
    | CCall of
        string
        * t
        * loc
        * string list (*(Some lv, CcallExp(fexp, params, loc))*)
    | CCallExp of string * string list * loc (*(None, fexp, params, loc)*)
    | CReturn1 of string * loc * string list (*(Some e, loc) *)
    | CReturn2 of loc (*(None, loc) *)
    | CIf of loc (*(_, _, _, loc) *)
    | CAssume of bool * string * loc (*(e, _, loc) *)
    | CLoop of loc (*loc *)
    | CAsm of loc (*(_, _, _, _, _, loc) *)
    | CSkip of loc (*(_, loc)*)

  let pp = function
    | CNone -> "CNone"
    | CSet (lv, e, _, _) -> F.sprintf "CSet(%s, %s)" lv e
    | CExternal (lv, _, _) -> F.sprintf "CExternal(%s)" lv
    | CAlloc (lv, e, _, _) -> F.sprintf "CAlloc(%s, %s)" lv e
    | CSalloc (lv, s, _, _) -> F.sprintf "CSalloc(%s, %s)" lv s
    | CFalloc (lv, f, _, _) -> F.sprintf "CFalloc(%s, %s)" lv f
    | CCall (lv, _, _, _) -> F.sprintf "CCall(%s)" lv
    | CCallExp (fexp, params, _) ->
        F.sprintf "CCallExp(%s, %s)" fexp (String.concat ~sep:", " params)
    | CReturn1 (e, _, _) -> F.sprintf "CReturn1(%s)" e
    | CReturn2 _ -> "CReturn2"
    | CIf _ -> "CIf"
    | CAssume (_, e, _) -> F.sprintf "CAssume(%s)" e
    | CLoop _ -> "CLoop"
    | CAsm _ -> "CAsm"
    | CSkip _ -> "CSkip"
end

type t = {
  sym_map : (string, Z3.Expr.expr) Hashtbl.t;
  numeral_map : (int, string) Hashtbl.t;
  ast_map : (Ast.t, int) Hashtbl.t;
  cfg_map : (CfgNode.t, string) Hashtbl.t;
  exp_map : (string, string) Hashtbl.t;
  node_map : (string, string) Hashtbl.t;
}

let create_maps () =
  {
    sym_map = Hashtbl.create 1000;
    numeral_map = Hashtbl.create 1000;
    ast_map = Hashtbl.create 1000;
    cfg_map = Hashtbl.create 1000;
    exp_map = Hashtbl.create 1000;
    node_map = Hashtbl.create 1000;
  }

let load_map cast1 cast2 ic map =
  let rec loop () =
    let line = In_channel.input_line ic in
    if Option.is_some line then (
      let pair = Option.value_exn line |> String.split ~on:'\t' in
      Hashtbl.add map
        (List.nth_exn pair 0 |> cast1)
        (List.nth_exn pair 1 |> cast2);
      loop ())
  in
  loop ();
  In_channel.close ic

let load_numeral_map = load_map int_of_string Fun.id

let reset_maps maps =
  Hashtbl.reset maps.sym_map;
  Hashtbl.reset maps.numeral_map;
  Hashtbl.reset maps.cfg_map;
  Hashtbl.reset maps.node_map;
  Hashtbl.reset maps.exp_map

let dump_map a_to_string b_to_string map_name mode map out_dir =
  let sym_map_file =
    F.sprintf "%s_%s.map" mode map_name |> Filename.concat out_dir
  in
  let sym_map_oc = Out_channel.create sym_map_file in
  let sym_map_fmt = F.formatter_of_out_channel sym_map_oc in
  Hashtbl.iter
    (fun a b ->
      F.fprintf sym_map_fmt "%s\t%s\n" (a_to_string a) (b_to_string b))
    map;
  F.pp_print_flush sym_map_fmt ();
  Out_channel.close sym_map_oc

let dump_sym_map = dump_map Fun.id Z3.Expr.to_string "sym"
let dump_numeral_map = dump_map string_of_int Fun.id "numeral"

let dump_ast_stmt x =
  match x.Cil.skind with
  | Cil.Instr i when List.length i = 0 -> "empty instr"
  | Cil.Instr i -> (
      match List.hd_exn i with
      | Cil.Set (_, _, l) -> "set:" ^ Ast.s_location l
      | Cil.Call (_, _, _, l) -> "call:" ^ Ast.s_location l
      | Cil.Asm _ -> "asm")
  | Cil.Return (_, l) -> "return:" ^ Ast.s_location l
  | Cil.Goto _ -> Ast.s_stmt x
  | Cil.Break l -> "break:" ^ Ast.s_location l
  | Cil.Continue l -> "continue:" ^ Ast.s_location l
  | Cil.If (_, _, _, l) -> "if:" ^ Ast.s_location l
  | Cil.Switch (_, _, _, l) -> "switch:" ^ Ast.s_location l
  | Cil.Loop (_, l, _, _) -> "loop:" ^ Ast.s_location l
  | Cil.Block _ -> "block"
  | Cil.TryFinally _ -> "tryfinally"
  | Cil.TryExcept _ -> "tryexcept"
  | Cil.ComputedGoto _ -> "computedgoto"

let dump_ast_glob x =
  match x with
  | Cil.GFun (f, l) -> "gfun:" ^ f.Cil.svar.vname ^ Ast.s_location l
  | _ -> failwith "dump_ast_glob"

let dump_ast_map =
  dump_map
    (fun x ->
      match x with
      | Ast.Global g -> dump_ast_glob g
      | Ast.Stmt s -> dump_ast_stmt s
      | _ -> failwith "dump_ast_map: unexpected ast type")
    string_of_int "ast"

let dump mode maps out_dir =
  dump_sym_map mode maps.sym_map out_dir;
  dump_numeral_map mode maps.numeral_map out_dir;
  dump_ast_map mode maps.ast_map out_dir

let dump_ast mode maps out_dir = dump_ast_map mode maps.ast_map out_dir
