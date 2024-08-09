open Core
module Hashtbl = Stdlib.Hashtbl
module J = Yojson.Basic.Util
module F = Format
module L = Logger

type loc = { file : string; line : int }

type cmd =
  | Set of string * string
  | Call of string option * string * string
  | Return of string option
  | Assume of bool
  | Skip of string
  | Etc

let parse_param_str param =
  String.sub param ~pos:1 ~len:(String.length param - 2)
  |> String.filter ~f:(fun c -> not (Char.equal c ' '))
  |> String.split ~on:','

let is_str_arg arg =
  String.prefix arg 2 |> String.equal "\\\""
  && String.suffix arg 2 |> String.equal "\\\""

let equal_param a b =
  let a' = parse_param_str a in
  let b' = parse_param_str b in
  if List.length a' <> List.length b' then false
  else
    List.fold2_exn a' b' ~init:true ~f:(fun acc a b ->
        is_str_arg a || is_str_arg b || (acc && String.equal a b))

let equal_cmd a b =
  match (a, b) with
  | Set (l1, e1), Set (l2, e2) -> String.equal l1 l2 && String.equal e1 e2
  | Call (Some l1, f1, e1), Call (Some l2, f2, e2) ->
      String.equal l1 l2 && String.equal f1 f2 && equal_param e1 e2
  | Call (None, f1, e1), Call (None, f2, e2) ->
      String.equal f1 f2 && equal_param e1 e2
  | Return (Some e1), Return (Some e2) -> String.equal e1 e2
  | Skip s1, Skip s2 -> String.equal s1 s2
  | Return None, Return None | Assume _, Assume _ | Etc, _ | _, Etc -> true
  | _ -> false

let pp_cmd fmt = function
  | Set (l, e) -> F.fprintf fmt "set %s %s" l e
  | Call (Some l, f, e) -> F.fprintf fmt "call %s %s %s" l f e
  | Call (None, f, e) -> F.fprintf fmt "call %s %s" f e
  | Return (Some e) -> F.fprintf fmt "return %s" e
  | Return None -> F.fprintf fmt "return"
  | Assume b -> F.fprintf fmt "assume %b" b
  | Skip _ -> F.fprintf fmt "skip"
  | Etc -> F.fprintf fmt "etc"

type t = {
  sym_map : (string, Z3.Expr.expr) Hashtbl.t; (* symbol -> z3 expr *)
  numeral_map : (int, string) Hashtbl.t; (* z3 numeral -> symbol *)
  loc_map : (loc, string) Hashtbl.t; (* location -> node symbol *)
  cmd_map : (string, cmd) Hashtbl.t; (* node symbol -> cmd (skip, ...) *)
  exp_map : (string, string) Hashtbl.t; (* exp symbol -> exp literal *)
  exp_rev_map : (string, string) Hashtbl.t; (* exp literal -> exp symbol *)
  lval_map : (string, string) Hashtbl.t; (* lval symbol -> lval literal *)
  lval_rev_map : (string, string) Hashtbl.t; (* lval literal -> lval symbol *)
  ast_map : (string, Ast.t) Hashtbl.t; (* symbol -> ast *)
  ast_rev_map : (Ast.t, string) Hashtbl.t; (* ast -> symbol *)
}

let create_maps () =
  {
    sym_map = Hashtbl.create 1000;
    numeral_map = Hashtbl.create 1000;
    loc_map = Hashtbl.create 1000;
    cmd_map = Hashtbl.create 1000;
    exp_map = Hashtbl.create 1000;
    exp_rev_map = Hashtbl.create 1000;
    lval_map = Hashtbl.create 1000;
    lval_rev_map = Hashtbl.create 1000;
    ast_map = Hashtbl.create 1000;
    ast_rev_map = Hashtbl.create 1000;
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
  Hashtbl.reset maps.loc_map;
  Hashtbl.reset maps.cmd_map;
  Hashtbl.reset maps.exp_map;
  Hashtbl.reset maps.exp_rev_map;
  Hashtbl.reset maps.lval_map;
  Hashtbl.reset maps.lval_rev_map;
  Hashtbl.reset maps.ast_map;
  Hashtbl.reset maps.ast_rev_map

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
  | _ -> L.error "dump_ast_glob"

let dump_ast_rev_map map =
  Hashtbl.iter
    (fun a b -> F.fprintf F.std_formatter "%s\n%s\n\n" (Ast.repr a) b)
    map

let dump_cmd_map map =
  Hashtbl.iter
    (fun a b -> F.fprintf F.std_formatter "%s\n%a\n\n" a pp_cmd b)
    map

let dump mode maps out_dir =
  dump_sym_map mode maps.sym_map out_dir;
  dump_numeral_map mode maps.numeral_map out_dir
