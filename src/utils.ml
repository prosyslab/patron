module J = Yojson.Basic.Util
module F = Format

let print_ekind exp =
  match exp with
  | Cil.Const _ -> print_endline "Const"
  | Cil.Lval _ -> print_endline "Lval"
  | Cil.SizeOf _ -> print_endline "SizeOf"
  | Cil.SizeOfE _ -> print_endline "SizeOfE"
  | Cil.SizeOfStr _ -> print_endline "SizeOfStr"
  | Cil.AlignOf _ -> print_endline "AlignOf"
  | Cil.AlignOfE _ -> print_endline "AlignOfE"
  | Cil.UnOp _ -> print_endline "UnOp"
  | Cil.BinOp _ -> print_endline "BinOp"
  | Cil.Question _ -> print_endline "Question"
  | Cil.CastE _ -> print_endline "CastE"
  | Cil.AddrOf _ -> print_endline "AddrOf"
  | Cil.AddrOfLabel _ -> print_endline "AddrOfLabel"
  | Cil.StartOf _ -> print_endline "StartOf"

let print_bool b =
  if b = true then print_endline "true" else print_endline "false"

let eq_stmt_line sk1 sk2 =
  match (sk1, sk2) with
  | Cil.Instr i1, Cil.Instr i2 -> (
      if i1 = [] || i2 = [] then false
      else
        match (List.hd i1, List.hd i2) with
        | Cil.Set (_, _, loc), Cil.Set (_, _, loc2) -> loc.line = loc2.line
        | Cil.Call (_, _, _, loc), Cil.Call (_, _, _, loc2) ->
            loc.line = loc2.line
        | _ -> false)
  | Cil.Return (_, loc), Cil.Return (_, loc') -> loc.line = loc'.line
  | Cil.Goto (_, loc), Cil.Goto (_, loc') -> loc.line = loc'.line
  | Cil.If (_, _, _, loc), Cil.If (_, _, _, loc') -> loc.line = loc'.line
  | Cil.Loop (_, loc, _, _), Cil.Loop (_, loc', _, _) -> loc.line = loc'.line
  | Cil.ComputedGoto (_, loc), Cil.ComputedGoto (_, loc') ->
      loc.line = loc'.line
  | Cil.Block _, Cil.Block _ -> false
  | Cil.TryExcept (_, _, _, loc), Cil.TryExcept (_, _, _, loc') ->
      loc.line = loc'.line
  | Cil.TryFinally (_, _, loc), Cil.TryFinally (_, _, loc') ->
      loc.line = loc'.line
  | Cil.Break loc, Cil.Break loc' -> loc.line = loc'.line
  | Cil.Continue loc, Cil.Continue loc' -> loc.line = loc'.line
  | _ -> false

let remove_comments globs =
  List.rev
    (List.fold_left
       (fun acc glob -> match glob with Cil.GText _ -> acc | _ -> glob :: acc)
       [] globs)

let print_exp_type exp =
  match exp with
  | Cil.Lval _ -> print_endline "Lval"
  | Cil.SizeOf _ -> print_endline "SizeOf"
  | Cil.SizeOfE _ -> print_endline "SizeOfE"
  | Cil.SizeOfStr _ -> print_endline "SizeOfStr"
  | Cil.AlignOf _ -> print_endline "AlignOf"
  | Cil.AlignOfE _ -> print_endline "AlignOfE"
  | Cil.UnOp _ -> print_endline "UnOp"
  | Cil.BinOp _ -> print_endline "BinOp"
  | Cil.Question _ -> print_endline "Question"
  | Cil.CastE _ -> print_endline "CastE"
  | Cil.AddrOf _ -> print_endline "AddrOf"
  | Cil.AddrOfLabel _ -> print_endline "AddrOfLabel"
  | Cil.StartOf _ -> print_endline "StartOf"
  | Cil.Const _ -> print_endline "Const"

let eq_global_type glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GType _, Cil.GType _
  | Cil.GCompTag _, Cil.GCompTag _
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _
  | Cil.GEnumTag _, Cil.GEnumTag _
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _
  | Cil.GVar _, Cil.GVar _
  | Cil.GVarDecl _, Cil.GVarDecl _
  | Cil.GFun _, Cil.GFun _
  | Cil.GAsm _, Cil.GAsm _
  | Cil.GPragma _, Cil.GPragma _ ->
      true
  | _ -> false

let print_global_type glob =
  match glob with
  | Cil.GType _ -> print_endline "GType"
  | Cil.GCompTag _ -> print_endline "GCompTag"
  | Cil.GCompTagDecl _ -> print_endline "GCompTagDecl"
  | Cil.GEnumTag _ -> print_endline "GEnumTag"
  | Cil.GEnumTagDecl _ -> print_endline "GEnumTagDecl"
  | Cil.GVar _ -> print_endline "GVar"
  | Cil.GVarDecl _ -> print_endline "GVarDecl"
  | Cil.GFun _ -> print_endline "GFun"
  | Cil.GAsm _ -> print_endline "GAsm"
  | Cil.GPragma _ -> print_endline "GPragma"
  | _ -> print_endline "Other"

let print_ikind instr =
  match instr with
  | Cil.Call _ -> print_endline "Call"
  | Cil.Set _ -> print_endline "Set"
  | Cil.Asm _ -> print_endline "Asm"

let string_of_skind sk =
  match sk with
  | Cil.Instr _ -> "Instr"
  | Cil.Return _ -> "Return"
  | Cil.Goto _ -> "Goto"
  | Cil.ComputedGoto _ -> "ComputedGoto"
  | Cil.Break _ -> "Break"
  | Cil.Continue _ -> "Continue"
  | Cil.If _ -> "If"
  | Cil.Loop _ -> "Loop"
  | Cil.Block _ -> "Block"
  | Cil.TryExcept _ -> "TryExcept"
  | Cil.TryFinally _ -> "TryFinally"
  | Cil.Switch _ -> "Switch"

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try
    ignore (Str.search_forward re s1 0);
    true
  with Not_found -> false

let read_lines name =
  let file = open_in name in
  let rec read_lines acc =
    match input_line file with
    | line -> read_lines (line :: acc)
    | exception End_of_file -> List.rev acc
  in
  let lines = read_lines [] in
  close_in file;
  lines

let parse_map path map file_name =
  let path = path ^ "/" ^ file_name in
  let lines = read_lines path in
  List.iter
    (fun line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      Hashtbl.add map key value)
    lines

let parse_node_json sparrow_dir =
  let file = Yojson.Basic.from_file (sparrow_dir ^ "/node.json") in
  let nodes = J.member "nodes" file in
  let key_list = J.keys nodes in
  List.fold_left
    (fun acc key ->
      let cont = J.member key nodes in
      let cmd =
        J.to_list (J.member "cmd" cont)
        |> List.fold_left
             (fun acc y ->
               try J.to_string y :: acc
               with _ -> (
                 try
                   let bool = J.to_bool y in
                   if bool then "true" :: acc else "false" :: acc
                 with _ -> "null" :: acc))
             []
        |> List.rev
      in
      let loc = J.member "loc" cont |> J.to_string in
      (key, cmd, loc) :: acc)
    [] key_list

let stmt_lst = ref []
let target_func = ref ""

let rec collect_stmts_from_block stmts =
  match stmts with
  | [] -> []
  | hd :: tl -> (
      match hd.Cil.skind with
      | Cil.Block b | Cil.Loop (b, _, _, _) ->
          (hd :: collect_stmts_from_block b.Cil.bstmts)
          @ collect_stmts_from_block tl
      | Cil.If (_, b1, b2, _) ->
          (hd :: collect_stmts_from_block b1.bstmts)
          @ collect_stmts_from_block b2.bstmts
          @ collect_stmts_from_block tl
      | _ -> hd :: collect_stmts_from_block tl)

class functionVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vfunc func =
      if func.svar.vname = !target_func then (
        stmt_lst := !stmt_lst @ func.sbody.bstmts;
        stmt_lst := collect_stmts_from_block !stmt_lst;
        SkipChildren)
      else DoChildren
  end

let extract_target_func_stmt_lst file target =
  stmt_lst := [];
  target_func := target;
  let vis = new functionVisitor in
  ignore (Cil.visitCilFile vis file);
  !stmt_lst

let extract_target_func ast target =
  List.find
    (fun x ->
      match x with Cil.GFun (x, _) -> x.Cil.svar.vname = target | _ -> false)
    ast.Cil.globals

let extract_target_funcs ast targets =
  List.fold_left
    (fun acc target -> extract_target_func ast target :: acc)
    [] targets

let get_first_nth_lines n str =
  let rec aux acc n str =
    if n = 0 then List.rev acc
    else
      let idx = String.index str '\n' in
      let line = String.sub str 0 idx in
      let str = String.sub str (idx + 1) (String.length str - idx - 1) in
      aux (line :: acc) (n - 1) str
  in
  aux [] n str

let get_target_file target_dir =
  Sys.readdir target_dir |> Array.to_list
  |> List.filter (fun x -> Filename.check_suffix x ".c")
  |> List.hd |> Filename.concat target_dir

let parse_model path =
  let lines = read_lines path in
  List.fold_left
    (fun map line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      (key, value) :: map)
    [] lines

let reverse_hashtbl tbl =
  let rev_tbl_init = Hashtbl.create 1000 in
  Hashtbl.iter (fun k v -> Hashtbl.add rev_tbl_init v k) tbl;
  rev_tbl_init

let mk_ast_node_str id = "AstNode-" ^ id
