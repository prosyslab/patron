open Yojson
module J = Yojson.Basic
module F = Format
module L = Logger
module StrMap = Map.Make (String)

type node_string = Node of string * string * string list

module Element = struct
  type t = Empty | EStmt of Cil.stmt | EInstr of Cil.instr | EExp of Cil.exp

  let compare = compare
end

type node = { id : string; elem : Element.t; subelem : Cil.exp StrMap.t }

type syntatic_context =
  | Root
  | GlobalContext of Cil.global
  | StmtContext of Cil.stmt * syntatic_context
  | InstrContext of Cil.instr * syntatic_context
  | ExpContext of Cil.exp * syntatic_context
  | LvalContext of Cil.lval * syntatic_context
  | NodeLevelContext of node

type action =
  (* InsrtGlobal(g1, g2) : insert statement s2 before statement s1 *)
  | Equal
  | InsertGlobal of Cil.global * Cil.global
  | DeleteGlobal of Cil.global * Cil.global
  | InsertLastGlobal of Cil.global list
  | DeleteLastGlobal of Cil.global list
  | InsertStmt of syntatic_context * Cil.stmt * Cil.stmt
  | InsertLastStmt of syntatic_context * Cil.block * Cil.stmt list
  | DeleteStmt of syntatic_context * Cil.stmt * Cil.stmt
  | DeleteLastStmt of syntatic_context * Cil.block * Cil.stmt list
  | UpdateStmt of syntatic_context * Cil.stmt * Cil.stmt
  | InsertInstr of syntatic_context * Cil.instr * Cil.instr
  | InsertLastInstr of syntatic_context * Cil.stmt * Cil.instr list
  | DeleteInstr of syntatic_context * Cil.instr * Cil.instr
  | DeleteLastInstr of syntatic_context * Cil.stmt * Cil.instr list
  | UpdateInstr of syntatic_context * Cil.instr * Cil.instr
  | InsertExp of syntatic_context * Cil.exp * Cil.exp
  | InsertLastExp of syntatic_context * Cil.exp * Cil.exp list
  | DeleteExp of syntatic_context * Cil.exp * Cil.exp
  | DeleteLastExp of syntatic_context * Cil.exp * Cil.exp list
  | UpdateExp of syntatic_context * Cil.exp * Cil.exp
  | UpdateLval of syntatic_context * Cil.lval * Cil.lval

type semantic_action = {
  action : action;
  cfg_edges : (string * string) list;
  dug_edges : (string * string) list;
}

type sparrow_node =
  | Node of string * sparrow_node * int (* id, node, loc *)
  | Skip of string
  | Return of string
  | Call of string * string * string list (* lval, func name, args *)
  | Assume of bool * string (* bool, exp *)
  | Salloc of string * string (* to, from *)
  | Set of string * string (* to, from *)
  | Alloc of string * string (* to, from *)
  | Falloc of string * string (* to, from *)

type graph = {
  nodes : node list;
  cfg_edges : (string * string) list;
  dug_edges : (string * string) list;
}

let string_of_file file = Cil.dumpFile !Cil.printerForMaincil stdout "" file

let string_of_global global =
  Cil.printGlobal !Cil.printerForMaincil () global |> Pretty.sprint ~width:80

let string_of_instr instr =
  Cil.printInstr !Cil.printerForMaincil () instr |> Pretty.sprint ~width:80

let string_of_stmt stmt =
  Cil.printStmt !Cil.printerForMaincil () stmt |> Pretty.sprint ~width:80

let string_of_exp exp = Cil.d_exp () exp |> Pretty.sprint ~width:80
let string_of_typ typ = Cil.d_type () typ |> Pretty.sprint ~width:80
let string_of_lval lval = Cil.d_lval () lval |> Pretty.sprint ~width:80

let rec string_of_context context =
  match context with
  | Root -> "Root"
  | GlobalContext global ->
      "GlobalContext(" ^ string_of_global global ^ ")\n==== context ends ===="
  | StmtContext (stmt, c) ->
      "StmtContext(" ^ string_of_stmt stmt ^ ")\n\n" ^ string_of_context c
  | InstrContext (instr, c) ->
      "InstrContext(" ^ string_of_instr instr ^ ")\n\n" ^ string_of_context c
  | ExpContext (exp, c) ->
      "ExpContext(" ^ string_of_exp exp ^ ")\n\n" ^ string_of_context c
  | LvalContext (lval, c) ->
      "LvalContext("
      ^ string_of_exp (Cil.Lval lval)
      ^ ")\n\n" ^ string_of_context c

let pp_action fmt = function
  | InsertGlobal (g1, g2) ->
      F.fprintf fmt "InsertGlobal(%s, %s)" (string_of_global g1)
        (string_of_global g2)
  | DeleteGlobal (g1, g2) ->
      F.fprintf fmt "DeleteGlobal(%s, %s)" (string_of_global g1)
        (string_of_global g2)
  | InsertStmt (context, s1, s2) ->
      F.fprintf fmt "InsertStmt(%s, %s)"
        (* "\n====Context====\n%s\n"  *)
        (string_of_stmt s1)
        (string_of_stmt s2)
      (* (string_of_context context) *)
  | InsertLastStmt (context, _, sl) ->
      List.iter
        (fun s -> F.fprintf fmt "InsertLastStmt(%s)" (string_of_stmt s))
        sl
  (* F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context) *)
  | DeleteStmt (context, s1, s2) ->
      F.fprintf fmt "DeleteStmt(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_stmt s1)
        (string_of_stmt s2)
      (* (string_of_context context) *)
  | DeleteLastStmt (context, _, sl) ->
      List.iter
        (fun s -> F.fprintf fmt "DeleteLastStmt(%s)" (string_of_stmt s))
        sl
  (* F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context) *)
  | InsertInstr (context, i1, i2) ->
      F.fprintf fmt "InsertInstr(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_instr i1)
        (string_of_instr i2)
      (* (string_of_context context) *)
  | InsertLastInstr (context, _, il) ->
      List.iter
        (fun i -> F.fprintf fmt "InsertLastInstr(%s)" (string_of_instr i))
        il
  (* F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context) *)
  | DeleteInstr (context, i1, i2) ->
      F.fprintf fmt "DeleteInstr(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_instr i1)
        (string_of_instr i2)
      (* (string_of_context context) *)
  | DeleteLastInstr (context, _, il) ->
      List.iter
        (fun i -> F.fprintf fmt "DeleteLastInstr(%s)" (string_of_instr i))
        il
  (* F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context) *)
  | UpdateStmt (context, s1, s2) ->
      F.fprintf fmt "UpdateStmt(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_stmt s1)
        (string_of_stmt s2)
      (* (string_of_context context) *)
  | UpdateInstr (context, i1, i2) ->
      F.fprintf fmt "UpdateInstr(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_instr i1)
        (string_of_instr i2)
      (* (string_of_context context) *)
  | UpdateExp (context, e1, e2) ->
      F.fprintf fmt "UpdateExp(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_exp e1)
        (string_of_exp e2)
      (* (string_of_context context) *)
  | InsertExp (context, e1, e2) ->
      F.fprintf fmt "InsertExp(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_exp e1)
        (string_of_exp e2)
      (* (string_of_context context) *)
  | DeleteExp (context, e1, e2) ->
      F.fprintf fmt "DeleteExp(%s, %s)"
        (* "\n====Context====\n%s\n" *)
        (string_of_exp e1)
        (string_of_exp e2)
  (* (string_of_context context) *)
  (* TODO: Instr level not validated *)
  | _ -> ()

let pp_edit_script fmt script =
  List.iter (fun action -> F.fprintf fmt "%a\n" pp_action action) script

let eq_instr instr1 instr2 =
  match (instr1, instr2) with
  | Cil.Set _, Cil.Set _ | Cil.Call _, Cil.Call _ | Cil.Asm _, Cil.Asm _ -> true
  | _ -> false

let eq_stmt_kind skind1 skind2 =
  match (skind1, skind2) with
  | Cil.Instr instrs1, Cil.Instr instrs2 ->
      List.length instrs1 = List.length instrs2
  | Cil.Return _, Cil.Return _
  | Cil.Goto _, Cil.Goto _
  | Cil.ComputedGoto _, Cil.ComputedGoto _
  | Cil.Break _, Cil.Break _
  | Cil.Continue _, Cil.Continue _
  | Cil.If _, Cil.If _
  | Cil.Loop _, Cil.Loop _
  | Cil.Block _, Cil.Block _
  | Cil.TryExcept _, Cil.TryExcept _
  | Cil.TryFinally _, Cil.TryFinally _ ->
      true
  | _ -> false

let rec eq_exp (a : Cil.exp) (b : Cil.exp) =
  match (a, b) with
  | Lval (Var a, NoOffset), Lval (Var b, NoOffset) -> a.vname = b.vname
  | Lval (Mem a, NoOffset), Lval (Mem b, NoOffset) -> eq_exp a b
  | BinOp (a, b, c, _), BinOp (d, e, f, _) -> a = d && eq_exp b e && eq_exp c f
  | UnOp (a, b, _), UnOp (c, d, _) -> a = c && eq_exp b d
  | CastE (a, b), CastE (c, d) -> a = c && eq_exp b d
  | AddrOf (Var a, NoOffset), AddrOf (Var b, NoOffset) -> a.vname = b.vname
  | AddrOf (Mem a, NoOffset), AddrOf (Mem b, NoOffset) -> eq_exp a b
  | StartOf (Var a, NoOffset), StartOf (Var b, NoOffset) -> a.vname = b.vname
  | StartOf (Mem a, NoOffset), StartOf (Mem b, NoOffset) -> eq_exp a b
  | Cil.SizeOfE a, Cil.SizeOfE b -> eq_exp a b
  | Const a, Const b -> a = b
  | Lval (Var a, NoOffset), StartOf (Var b, NoOffset)
  | StartOf (Var a, NoOffset), Lval (Var b, NoOffset) ->
      a.vname = b.vname
  | _ -> false

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

let eq_lval l1 l2 =
  match (l1, l2) with
  | (lhost1, _), (lhost2, _) -> (
      match (lhost1, lhost2) with
      | Cil.Var vi1, Cil.Var vi2 -> vi1.Cil.vname = vi2.Cil.vname
      | Cil.Mem _, Cil.Mem _ -> true
      | _ -> false)

let extract_exp_change e1 e2 context =
  if eq_exp e1 e2 then []
  else
    let _ = L.debug "exp update detected" in
    print_endline "exp update detected";
    [ UpdateExp (context, e1, e2) ]

let rec find_param_change_rec e1 es2 pred result_list =
  match es2 with
  | [] -> result_list
  | e2 :: es2' ->
      if eq_exp e1 e2 then pred :: result_list
      else find_param_change_rec e1 es2' e2 result_list

let find_param_change e1 es2 result_list =
  match es2 with
  | [] -> result_list
  | e2 :: es2' ->
      if eq_exp e1 e2 then [ e1 ]
      else find_param_change_rec e1 es2' e2 result_list

let rec find_continue_point_param param1 params =
  match params with
  | [] -> []
  | hd :: tl ->
      if eq_exp param1 hd then params else find_continue_point_param param1 tl

let rec fold_params2 params1 params2 context =
  match (params1, params2) with
  | p1 :: ps1, p2 :: ps2 ->
      if eq_exp p1 p2 then fold_params2 ps1 ps2 context
      else
        let insertions = find_param_change p1 params2 [] in
        if insertions <> [] then (
          let _ = L.debug "param insert detected\n" in
          print_endline "param insert detected";
          fold_params2 ps1
            (find_continue_point_param (List.hd insertions) ps2)
            context
          @ List.map
              (fun p -> InsertExp (ExpContext (p1, context), p1, p))
              insertions)
        else
          let deletions = find_param_change p2 params1 [] in
          if deletions <> [] then (
            let _ = L.debug "param delete detected" in
            print_endline "param delete detected";
            fold_params2
              (find_continue_point_param (List.hd deletions) ps1)
              ps2 context
            @ List.map
                (fun p -> DeleteExp (ExpContext (p2, context), p2, p))
                deletions)
          else
            let _ = L.debug "param update detected" in
            print_endline "param update detected";
            UpdateExp (ExpContext (p1, context), p1, p2)
            :: fold_params2 ps1 (List.tl ps2) context
  | [], [] -> []
  | _ -> []

let rec find_instr_change_rec i1 is2 pred result_list =
  match is2 with
  | [] -> result_list
  | i2 :: is2' ->
      if eq_instr i1 i2 then pred :: result_list
      else find_instr_change_rec i1 is2' i2 result_list

let find_instr_change i1 is2 result_list =
  match is2 with
  | [] -> []
  | i2 :: is2' ->
      if eq_instr i1 i2 then []
      else find_instr_change_rec i1 is2' i2 result_list

let extract_instr i1 i2 context =
  match (i1, i2) with
  | Cil.Call (_, e1, params1, _), Cil.Call (_, e2, params2, _) ->
      let e_result = extract_exp_change e1 e2 (ExpContext (e1, context)) in
      let params_result = fold_params2 params1 params2 context in
      e_result @ params_result
  | _ -> []

let rec find_continue_point_instr instr1 instrs =
  match instrs with
  | [] -> []
  | hd :: tl ->
      if eq_instr instr1 hd then instrs else find_continue_point_instr instr1 tl

let rec fold_instrs2 s1 instrs1 instrs2 context =
  match (instrs1, instrs2) with
  | i1 :: is1, i2 :: is2 ->
      if eq_instr i1 i2 then
        let work_result = extract_instr i1 i2 (InstrContext (i1, context)) in
        if work_result <> [] then work_result
        else fold_instrs2 s1 is1 is2 context
      else
        let insertions = find_instr_change i1 instrs2 [] in
        if insertions <> [] then
          let _ = L.debug "instr insertion detected\n" in
          fold_instrs2 s1 is1
            (find_continue_point_instr (List.hd insertions) is2)
            context
          @ List.map (fun i -> InsertInstr (context, i1, i)) insertions
        else
          let deletions = find_instr_change i2 instrs1 [] in
          if deletions <> [] then
            let _ = L.debug "instr deletion detected\n" in
            fold_instrs2 s1
              (find_continue_point_instr (List.hd deletions) is1)
              is2 context
            @ List.map (fun i -> DeleteInstr (context, i2, i)) deletions
          else fold_instrs2 s1 is1 is2 context
  | [], [] -> []
  | [], _ -> [ InsertLastInstr (context, s1, instrs2) ]
  | _, [] -> [ DeleteLastInstr (context, s1, instrs1) ]

let rec find_continue_point_stmt stmt1 stmts =
  match stmts with
  | [] -> []
  | hd :: tl ->
      if eq_stmt_kind stmt1.Cil.skind hd.Cil.skind then stmts
      else find_continue_point_stmt stmt1 tl

let rec find_stmt_change_rec s1 ss2 pred result_list =
  match ss2 with
  | [] -> result_list
  | s2 :: ss2' ->
      if eq_stmt_kind s1.Cil.skind s2.Cil.skind then pred :: result_list
      else find_stmt_change_rec s1 ss2' s2 result_list

let find_stmt_change s1 ss2 result_list =
  match ss2 with
  | [] -> []
  | s2 :: ss2' ->
      if eq_stmt_kind s1.Cil.skind s2.Cil.skind then []
      else find_stmt_change_rec s1 ss2' s2 result_list

let rec fold_stmts2 b1 stmts1 stmts2 context =
  match (stmts1, stmts2) with
  | s1 :: ss1, s2 :: ss2 ->
      if eq_stmt_kind s1.Cil.skind s2.Cil.skind then
        let extract_result = extract_skind s1 s2 (StmtContext (s1, context)) in
        if extract_result <> [] then extract_result
        else fold_stmts2 b1 ss1 ss2 context
      else
        let insertions = find_stmt_change s1 stmts2 [] in
        if insertions <> [] then (
          let _ = L.debug "stmt insertion detected\n" in
          print_endline "stmt insertion detected";
          fold_stmts2 b1 ss1
            (find_continue_point_stmt (List.hd insertions) ss2)
            context
          @ List.map (fun s -> InsertStmt (context, s1, s)) insertions)
        else
          let deletions = find_stmt_change s2 stmts1 [] in
          if deletions <> [] then (
            let _ = L.debug "stmt deletion detected\n" in
            print_endline "stmt deletion detected";
            fold_stmts2 b1
              (find_continue_point_stmt (List.hd deletions) ss1)
              ss2 context
            @ List.map (fun s -> DeleteStmt (context, s2, s)) deletions)
          else UpdateStmt (context, s1, s2) :: fold_stmts2 b1 ss1 ss2 context
  | [], [] -> []
  | [], _ -> [ InsertLastStmt (context, b1, stmts2) ]
  | _, [] -> [ DeleteLastStmt (context, b1, stmts1) ]

and extract_block block1 block2 context =
  fold_stmts2 block1 block1.Cil.bstmts block2.Cil.bstmts context

and extract_skind s1 s2 context =
  match (s1.Cil.skind, s2.Cil.skind) with
  | Cil.Instr instrs1, Cil.Instr instrs2 ->
      let instr_result = fold_instrs2 s1 instrs1 instrs2 context in
      if instr_result <> [] then instr_result else []
  | Cil.If (_, t_block1, e_block1, _), Cil.If (_, t_block2, e_block2, _) ->
      let t_result = extract_block t_block1 t_block2 context in
      let e_result = extract_block e_block1 e_block2 context in
      t_result @ e_result
  | _ -> []

let eq_typ typ_info1 typ_info2 =
  match (typ_info1, typ_info2) with
  | Cil.TVoid _, Cil.TVoid _
  | Cil.TInt _, Cil.TInt _
  | Cil.TFloat _, Cil.TFloat _
  | Cil.TPtr _, Cil.TPtr _
  | Cil.TArray _, Cil.TArray _
  | Cil.TFun _, Cil.TFun _
  | Cil.TNamed _, Cil.TNamed _
  | Cil.TComp _, Cil.TComp _
  | Cil.TEnum _, Cil.TEnum _ ->
      true
  | _ -> false

let eq_global glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      eq_typ func_info1.svar.vtype func_info2.svar.vtype
      && func_info1.svar.vname = func_info2.svar.vname
  | Cil.GType _, Cil.GType _
  | Cil.GCompTag _, Cil.GCompTag _
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _
  | Cil.GEnumTag _, Cil.GEnumTag _
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _ ->
      true
  | Cil.GVarDecl (v1, _), Cil.GVarDecl (v2, _) -> v1.vname = v2.vname
  | Cil.GVar _, Cil.GVar _
  | Cil.GAsm _, Cil.GAsm _
  | Cil.GPragma _, Cil.GPragma _
  | Cil.GText _, Cil.GText _ ->
      true
  | _ -> false

let extract_global glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      if
        eq_typ func_info1.svar.vtype func_info2.svar.vtype
        && eq_global glob1 glob2
      then
        let diff_result =
          extract_block func_info1.sbody func_info2.sbody (GlobalContext glob1)
        in
        if diff_result = [] then [ Equal ] else diff_result
      else []
  | Cil.GVarDecl (v1, _), Cil.GVarDecl (v2, _) ->
      if v1.vname = v2.vname then [ Equal ] else []
  | _ -> []

let rec find_global_change_rec glob1 globals pred result_list =
  match globals with
  | [] -> result_list
  | hd :: tl ->
      if eq_global glob1 hd then pred :: result_list
      else find_global_change_rec glob1 tl hd (pred :: result_list)

let find_global_change glob1 glob2 globals =
  match globals with
  | [] -> []
  | hd :: tl ->
      if eq_global glob1 hd then [ glob2 ]
      else find_global_change_rec glob1 tl hd [ glob2 ]

let rec find_continue_point_glob glob1 globals =
  match globals with
  | [] -> []
  | hd :: tl ->
      if eq_global glob1 hd then tl else find_continue_point_glob glob1 tl

let rec fold_globals2 doner_gobals patch_globals =
  match (doner_gobals, patch_globals) with
  | hd1 :: tl1, hd2 :: tl2 ->
      let es = extract_global hd1 hd2 in
      if es <> [] then
        if List.hd es = Equal then fold_globals2 tl1 tl2
        else es @ fold_globals2 tl1 tl2
      else
        let insertions = find_global_change hd1 hd2 tl2 in
        if insertions <> [] then
          let _ =
            L.debug "global insertion detected";
            print_endline "global insertion detected"
          in
          fold_globals2 tl1 (find_continue_point_glob hd1 tl2)
          @ List.map (fun g -> InsertGlobal (hd1, g)) insertions
        else
          let deletions = find_global_change hd2 hd1 tl1 in
          if deletions <> [] then
            let _ =
              L.debug "global deletion detected";
              print_endline "global deletion detected"
            in
            fold_globals2 tl1 (find_continue_point_glob (List.hd deletions) tl2)
            @ List.map (fun g -> DeleteGlobal (hd2, g)) deletions
          else fold_globals2 tl1 tl2
  | [], _ -> [ InsertLastGlobal doner_gobals ]
  | _, [] -> [ DeleteLastGlobal patch_globals ]

let extract doner_file patch_file =
  fold_globals2 doner_file.Cil.globals patch_file.Cil.globals

let trim_node_str str =
  Str.global_replace (Str.regexp " ") ""
    (Str.global_replace (Str.regexp "?") "\\\\"
       (Str.global_replace (Str.regexp "\\\\") ""
          (Str.global_replace (Str.regexp "\\\\\\") "?" str)))

let remove_skip map = StrMap.filter (fun _ v -> not (String.equal v "skip")) map

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let rev =
  let rec rev_append acc l =
    match l with [] -> acc | h :: t -> rev_append (h :: acc) t
  in
  fun l -> rev_append [] l

let rec search_seq s1 s2 =
  match s2 with
  | [] -> true
  | hd :: tl ->
      let rec search s1 s2 =
        match s1 with
        | [] -> false
        | hd1 :: tl1 -> if hd1 = hd then search_seq tl1 tl else search tl1 s2
      in
      search s1 s2

(* is s2 in s1? *)
let subset s1 s2 =
  let set1 = explode s1 in
  let set2 = explode s2 in
  search_seq set1 set2

let extract_location str =
  let parsed_str =
    if str <> ":-1" then List.nth (Str.split (Str.regexp_string ":") str) 1
    else Str.global_replace (Str.regexp_string ":") "" str
  in
  int_of_string parsed_str

let rec parse_args_rec args output tmp_str bracket_num =
  match args with
  | [] -> [ tmp_str ] @ output
  | hd :: tl -> (
      match hd with
      | '(' ->
          if bracket_num <> 0 then
            parse_args_rec tl output (tmp_str ^ "(") (bracket_num + 1)
          else parse_args_rec tl output tmp_str (bracket_num + 1)
      | ')' ->
          if bracket_num > 1 then
            parse_args_rec tl output (tmp_str ^ ")") (bracket_num - 1)
          else parse_args_rec tl output tmp_str (bracket_num - 1)
      | ',' ->
          if bracket_num = 1 then
            parse_args_rec tl ([ tmp_str ] @ output) "" bracket_num
          else parse_args_rec tl output (tmp_str ^ ",") bracket_num
      | ' ' -> parse_args_rec tl output tmp_str bracket_num
      | _ -> parse_args_rec tl output (tmp_str ^ String.make 1 hd) bracket_num)

let parse_args args =
  rev (parse_args_rec (explode (trim_node_str args)) [] "" 0)

let parse_node node_path =
  let json = J.from_file node_path in
  let nodes = J.Util.member "nodes" json in
  let key_list = J.Util.keys nodes in
  List.fold_left
    (fun acc k ->
      let cont = J.Util.member k nodes in
      let cmd = J.Util.to_list (J.Util.member "cmd" cont) in
      let loc = J.Util.member "loc" cont in
      let cmd =
        match J.Util.to_string (List.hd cmd) with
        | "skip" -> Skip (J.Util.to_string (List.nth cmd 1))
        | "return" -> Return (J.Util.to_string (List.nth cmd 1))
        | "call" ->
            let lval =
              try J.Util.to_string (List.nth cmd 1) with _ -> ""
              (* if J.Util.to_string (List.nth cmd 1) = null then ""
                 else J.Util.to_string (List.nth cmd 1) *)
            in
            Call
              ( lval,
                J.Util.to_string (List.nth cmd 2),
                parse_args (J.Util.to_string (List.nth cmd 3)) )
        | "assume" ->
            Assume
              ( J.Util.to_bool (List.nth cmd 1),
                J.Util.to_string (List.nth cmd 2) )
        | "salloc" ->
            Salloc
              ( J.Util.to_string (List.nth cmd 1),
                J.Util.to_string (List.nth cmd 2) )
        | "set" ->
            Set
              ( J.Util.to_string (List.nth cmd 1),
                J.Util.to_string (List.nth cmd 2) )
        | "alloc" ->
            Alloc
              ( J.Util.to_string (List.nth cmd 1),
                J.Util.to_string (List.nth cmd 2) )
        | "falloc" ->
            Falloc
              ( J.Util.to_string (List.nth cmd 1),
                J.Util.to_string (List.nth cmd 2) )
        | _ -> failwith "Unknown Command"
      in
      acc @ [ Node (k, cmd, extract_location (J.Util.to_string loc)) ])
    [] key_list

let rec print_sparrow_node node =
  match node with
  | Node (id, cmd, loc) ->
      print_endline "Node: ";
      print_string "\tid: ";
      print_endline id;
      print_endline "\tcmd: ";
      print_sparrow_node cmd;
      print_string "\tloc: ";
      print_int loc;
      print_endline ""
  | Skip str ->
      print_string "\t\tSkip: ";
      print_endline str
  | Return str ->
      print_string "\t\tReturn: ";
      print_endline str
  | Call (lval, func, args) ->
      print_endline "\t\tCall: ";
      print_string "\t\t\tlval: ";
      print_endline lval;
      print_string "\t\t\tfunc: ";
      print_endline func;
      print_endline "\t\t\targs: ";
      List.iter (fun x -> print_endline ("\t\t\t\t" ^ x)) args
  | Assume (b, exp) ->
      print_endline "\t\tAssume: ";
      print_string "\t\t\tbool: ";
      if b = true then print_endline "true" else print_endline "false";
      print_string "\t\t\texp: ";
      print_endline exp
  | Salloc (to_, from_) ->
      print_endline "\t\tSalloc: ";
      print_string "\t\t\tto: ";
      print_endline to_;
      print_string "\t\t\tfrom: ";
      print_endline from_
  | Set (to_, from_) ->
      print_endline "\t\tSet: ";
      print_string "\t\t\tto: ";
      print_endline to_;
      print_string "\t\t\tfrom: ";
      print_endline from_
  | Alloc (to_, from_) ->
      print_endline "\t\tAlloc: ";
      print_string "\t\t\tto: ";
      print_endline to_;
      print_string "\t\t\tfrom: ";
      print_endline from_
  | Falloc (to_, from_) ->
      print_endline "\t\tFalloc: ";
      print_string "\t\t\tto: ";
      print_endline to_;
      print_string "\t\t\tfrom: ";
      print_endline from_

let rec parse_strmap file map =
  match file with
  | [] -> map
  | hd :: tl ->
      let splited = Str.split (Str.regexp "\t") hd in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      parse_strmap tl
        (StrMap.add
           (Str.global_replace (Str.regexp " ") "" (trim_node_str key))
           (Str.global_replace (Str.regexp " ") "" (trim_node_str value))
           map)

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try
    ignore (Str.search_forward re s1 0);
    true
  with Not_found -> false

let print_map_exp map =
  StrMap.iter
    (fun k v ->
      print_string "\t";
      print_string (k ^ " -> ");
      print_string (string_of_exp v);
      print_endline "")
    map

let print_node node =
  print_string "ID: ";
  print_endline node.id;
  print_string "Element: ";
  (match node.elem with
  | EExp e -> print_endline (string_of_exp e)
  | EStmt s -> print_endline (string_of_stmt s)
  | EInstr c -> print_endline (string_of_instr c)
  | _ -> print_string "Unknown");
  print_endline "";
  print_endline "Sub: ";
  print_map_exp node.subelem;
  print_endline ""

let read_lines name =
  let ic = open_in name in
  let try_read () = try Some (input_line ic) with End_of_file -> None in
  let rec loop acc =
    match try_read () with
    | Some s -> loop (s :: acc)
    | None ->
        close_in ic;
        List.rev acc
  in
  loop []

let rec create_temp_map node_lst output_map =
  match node_lst with
  | [] -> output_map
  | hd :: tl -> (
      match hd with
      | Node (_, node, _) -> (
          match node with
          | Alloc (to_, from_) | Salloc (to_, from_) | Set (to_, from_) ->
              if subset to_ "__cil_tmp" then
                create_temp_map tl
                  (StrMap.union
                     (fun _ v1 _ -> Some v1)
                     (StrMap.add (trim_node_str to_) (trim_node_str from_)
                        StrMap.empty)
                     output_map)
              else if subset from_ "__cil_tmp" then
                create_temp_map tl
                  (StrMap.union
                     (fun _ v1 _ -> Some v1)
                     (StrMap.add (trim_node_str from_) (trim_node_str to_)
                        StrMap.empty)
                     output_map)
              else create_temp_map tl output_map
          | _ -> create_temp_map tl output_map)
      | _ -> create_temp_map tl output_map)

let print_map map =
  StrMap.iter
    (fun k v ->
      print_string (k ^ " -> ");
      print_endline v)
    map

let print_bool b =
  if b = true then print_endline "true" else print_endline "false"

let print_graph graph =
  print_endline "==========Nodes========= ";
  graph.nodes |> List.iter (fun node -> print_node node);
  print_endline "==========CFG========= ";
  graph.cfg_edges
  |> List.iter (fun edge ->
         match edge with
         | from_, to_ ->
             print_string (from_ ^ " -> ");
             print_endline to_);
  print_endline "==========DUG========= ";
  graph.dug_edges
  |> List.iter (fun edge ->
         match edge with
         | from_, to_ ->
             print_string (from_ ^ " -> ");
             print_endline to_)

let read_lines name =
  let ic = open_in name in
  let try_read () = try Some (input_line ic) with End_of_file -> None in
  let rec loop acc =
    match try_read () with
    | Some s -> loop (s :: acc)
    | None ->
        close_in ic;
        List.rev acc
  in
  loop []

let make_str_map path =
  let lines = read_lines path in
  List.fold_left
    (fun map line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      StrMap.add (trim_node_str key) (trim_node_str value) map)
    StrMap.empty lines

let append_before_elt elt loc lst =
  let rec loop lst acc =
    match lst with
    | [] -> acc
    | hd :: tl ->
        if string_of_exp hd = string_of_exp loc then
          List.rev ([ elt ] @ acc) @ [ hd ] @ tl
        else loop tl ([ hd ] @ acc)
  in
  loop lst []

let eq_call context target_instr =
  let extract_instr_from_node node =
    match node.elem with
    | EInstr i -> i
    | _ -> raise (Failure "Not an instruction")
  in
  let instr =
    match context with
    | NodeLevelContext n -> extract_instr_from_node n
    | _ -> raise (Failure "Not a node")
  in
  let exp_lst =
    match instr with
    | Call (_, _, exp_lst, _) -> exp_lst
    | _ -> raise (Failure "Not a call")
  in
  let target_exp_lst =
    match target_instr with
    | Cil.Call (_, _, exp_lst, _) -> exp_lst
    | _ -> raise (Failure "Not a call")
  in
  let rec loop exp_lst target_exp_lst =
    match (exp_lst, target_exp_lst) with
    | [], [] -> true
    | [], _ | _, [] -> false
    | hd :: tl, hd' :: tl' ->
        if string_of_exp hd = string_of_exp hd' then loop tl tl' else false
  in
  loop exp_lst target_exp_lst
