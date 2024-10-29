open Core
module Hashtbl = Stdlib.Hashtbl
module Sys = Stdlib.Sys
module J = Yojson.Basic.Util
module F = Format
module Cil = ProsysCil.Cil

let is_alpha str =
  let check_char = function 'a' .. 'z' | 'A' .. 'Z' -> true | _ -> false in
  String.for_all ~f:check_char str

let is_digit =
  let check_char = function '0' .. '9' -> true | _ -> false in
  String.for_all ~f:check_char

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

let eq_stmt_line sk1 sk2 =
  match (sk1, sk2) with
  | Cil.Instr (Cil.Set (_, _, loc1) :: _), Cil.Instr (Cil.Set (_, _, loc2) :: _)
  | ( Cil.Instr (Cil.Call (_, _, _, loc1) :: _),
      Cil.Instr (Cil.Call (_, _, _, loc2) :: _) )
  | Cil.Return (_, loc1), Cil.Return (_, loc2)
  | Cil.Goto (_, loc1), Cil.Goto (_, loc2)
  | Cil.If (_, _, _, loc1), Cil.If (_, _, _, loc2)
  | Cil.Loop (_, loc1, _, _), Cil.Loop (_, loc2, _, _)
  | Cil.ComputedGoto (_, loc1), Cil.ComputedGoto (_, loc2)
  | Cil.TryExcept (_, _, _, loc1), Cil.TryExcept (_, _, _, loc2)
  | Cil.TryFinally (_, _, loc1), Cil.TryFinally (_, _, loc2)
  | Cil.Break loc1, Cil.Break loc2
  | Cil.Continue loc1, Cil.Continue loc2 ->
      loc1.line = loc2.line
  | _ -> false

let remove_comments globs =
  List.rev
    (List.fold_left
       ~f:(fun acc glob ->
         match glob with Cil.GText _ -> acc | _ -> glob :: acc)
       ~init:[] globs)

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

let parse_map ?(rev_too = false) ?(rev_map = None) path file_name map =
  let lines = Filename.concat path file_name |> In_channel.read_lines in
  List.iter
    ~f:(fun line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd_exn splited in
      let value = List.hd_exn (List.tl_exn splited) in
      Hashtbl.add map key value;
      if rev_too then Hashtbl.add (Option.value_exn rev_map) value key)
    lines

let parse_loc loc =
  let parsed =
    String.split ~on:'/' loc |> List.last_exn |> String.split ~on:':'
  in
  if List.length parsed <> 2 then { Maps.file = ""; line = -1 }
  else
    {
      Maps.file = List.hd_exn parsed;
      line = int_of_string (List.nth_exn parsed 1);
    }

let parse_cmd = function
  | [ `String "set"; `String lv; `String exp ] -> Maps.Set (lv, exp)
  | [ `String "call"; `String lv; `String f; `String exp ] ->
      Maps.Call (Some lv, f, exp)
  | [ `String "call"; `Null; `String f; `String exp ] -> Maps.Call (None, f, exp)
  | [ `String "return"; `String e ] -> Maps.Return (Some e)
  | [ `String "return"; `Null ] -> Maps.Return None
  | [ `String "skip"; `String s ] -> Maps.Skip s
  | `String "assume" :: `Bool b :: _ -> Maps.Assume b
  | _ -> Maps.Etc

let parse_node_json sparrow_dir loc_map cmd_map =
  let file = Yojson.Basic.from_file (sparrow_dir ^ "/node.json") in
  let nodes = J.member "nodes" file in
  J.to_assoc nodes
  |> List.iter ~f:(fun (key, node) ->
         let loc = J.member "loc" node |> J.to_string |> parse_loc in
         let cmd = J.member "cmd" node |> J.to_list |> parse_cmd in
         Hashtbl.add cmd_map key cmd;
         Hashtbl.add loc_map loc key)

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
      if String.equal func.svar.vname !target_func then (
        stmt_lst := !stmt_lst @ func.sbody.bstmts;
        stmt_lst := collect_stmts_from_block !stmt_lst;
        SkipChildren)
      else DoChildren
  end

let extract_target_func_stmt_lst file target =
  stmt_lst := [];
  target_func := target;
  let vis = new functionVisitor in
  Cil.visitCilFile vis file;
  !stmt_lst

let extract_target_func ast target =
  List.find_exn
    ~f:(fun x ->
      match x with
      | Cil.GFun (x, _) -> String.equal x.Cil.svar.vname target
      | _ -> false)
    ast.Cil.globals

let extract_target_funcs ast targets =
  List.fold_left
    ~f:(fun acc target -> extract_target_func ast target :: acc)
    ~init:[] targets

let get_target_file target_dir =
  Sys.readdir target_dir |> Array.to_list
  |> List.filter ~f:(fun x -> Filename.check_suffix x ".c")
  |> List.hd_exn |> Filename.concat target_dir

let reverse_hashtbl tbl =
  let rev_tbl_init = Hashtbl.create 1000 in
  Hashtbl.iter (fun k v -> Hashtbl.add rev_tbl_init v k) tbl;
  rev_tbl_init

let get_func_name_from_node n = String.split ~on:'-' n |> List.hd_exn

let find_alarm_file alarm_dir f =
  String.is_substring_at ~pos:0 ~substring:"Alarm" f
  && String.is_substring_at ~pos:0 ~substring:"AlarmTaint" f |> not
  && String.is_substring_at ~pos:0 ~substring:"AlarmBufferOver" f |> not
  && Filename.concat alarm_dir f
     |> In_channel.read_lines |> List.is_empty |> not

let hotfix_for_io = String.substr_replace_first ~pattern:"IO" ~with_:""

let find_bug_type dir alarm =
  let alarm_dir = Filename.concat dir ("sparrow-out/taint/datalog/" ^ alarm) in
  Sys.readdir alarm_dir
  |> Array.find_exn ~f:(find_alarm_file alarm_dir)
  |> Filename.chop_extension
  |> String.chop_prefix_exn ~prefix:"Alarm"
  |> hotfix_for_io
