module F = Format
module L = Logger
module C = Cmdline
module Cil_map = Map.Make (String)

type map_type =
  | NullMap
  | GlobalMap of Cil.global Cil_map.t
  | StmtMap of Cil.stmt Cil_map.t
  | InstrMap of Cil.instr Cil_map.t
  | ExpMap of Cil.exp Cil_map.t
  | LvalMap of Cil.lval Cil_map.t

type combined_map = CombinedMap of map_type * map_type * map_type

(* let map = Cil_map.empty in
   let map2 = Cil_map.add "a" instr *)
type node_string = Node of string * string list

type context =
  | Root
  | GlobalContext of Cil.global
  | StmtContext of Cil.stmt * context
  | InstrContext of Cil.instr * context
  | ExpContext of Cil.exp * context
  | LvalContext of Cil.lval * context

type action =
  (* InsrtGlobal(g1, g2) : insert statement s2 before statement s1 *)
  | InsertGlobal of Cil.global * Cil.global
  | DeleteGlobal of Cil.global * Cil.global
  | InsertLastGlobal of Cil.global list
  | DeleteLastGlobal of Cil.global list
  | InsertStmt of context * Cil.stmt * Cil.stmt
  | InsertLastStmt of context * Cil.block * Cil.stmt list
  | DeleteStmt of context * Cil.stmt * Cil.stmt
  | DeleteLastStmt of context * Cil.block * Cil.stmt list
  | UpdateStmt of context * Cil.stmt * Cil.stmt
  | InsertInstr of context * Cil.instr * Cil.instr
  | InsertLastInstr of context * Cil.stmt * Cil.instr list
  | DeleteInstr of context * Cil.instr * Cil.instr
  | DeleteLastInstr of context * Cil.stmt * Cil.instr list
  | UpdateInstr of context * Cil.instr * Cil.instr
  | InsertExp of context * Cil.exp * Cil.exp
  | InsertLastExp of context * Cil.exp * Cil.exp list
  | DeleteExp of context * Cil.exp * Cil.exp
  | DeleteLastExp of context * Cil.exp * Cil.exp list
  | UpdateExp of context * Cil.exp * Cil.exp
  | UpdateLval of context * Cil.lval * Cil.lval

let print_skind stmt =
  match stmt.Cil.skind with
  | Cil.Instr _ -> print_string "Instr"
  | Cil.Return _ -> print_string "Return"
  | Cil.Goto _ -> print_string "Goto"
  | Cil.ComputedGoto _ -> print_string "ComputedGoto"
  | Cil.Break _ -> print_string "Break"
  | Cil.Continue _ -> print_string "Continue"
  | Cil.If _ -> print_string "If"
  | Cil.Loop _ -> print_string "Loop"
  | Cil.Block _ -> print_string "Block"
  | Cil.TryExcept _ -> print_string "TryExcept"
  | Cil.TryFinally _ -> print_string "TryFinally"
  | _ -> print_string "unidentified"

let print_ekind e =
  match e with
  | Cil.Lval _ -> print_string "Lval"
  | Cil.SizeOf _ -> print_string "SizeOf"
  | Cil.SizeOfE _ -> print_string "SizeOfE"
  | Cil.SizeOfStr _ -> print_string "SizeOfStr"
  | Cil.AlignOf _ -> print_string "AlignOf"
  | Cil.AlignOfE _ -> print_string "AlignOfE"
  | Cil.UnOp _ -> print_string "UnOp"
  | Cil.BinOp _ -> print_string "BinOp"
  | Cil.Question _ -> print_string "Question"
  | Cil.CastE _ -> print_string "CastE"
  | Cil.Const _ -> print_string "Const"
  | Cil.AddrOf _ -> print_string "AddrOf"
  | Cil.StartOf _ -> print_string "StartOf"
  | _ -> print_string "unidentified"

type edit_script = action list

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
      F.fprintf fmt "InsertStmt(%s, %s)\n====Context====\n%s\n"
        (string_of_stmt s1) (string_of_stmt s2)
        (string_of_context context)
  | InsertLastStmt (context, _, sl) ->
      List.iter
        (fun s -> F.fprintf fmt "InsertLastStmt(%s)" (string_of_stmt s))
        sl;
      F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context)
  | DeleteStmt (context, s1, s2) ->
      F.fprintf fmt "DeleteStmt(%s, %s)\n====Context====\n%s\n"
        (string_of_stmt s1) (string_of_stmt s2)
        (string_of_context context)
  | DeleteLastStmt (context, _, sl) ->
      List.iter
        (fun s -> F.fprintf fmt "DeleteLastStmt(%s)" (string_of_stmt s))
        sl;
      F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context)
  | InsertInstr (context, i1, i2) ->
      F.fprintf fmt "InsertInstr(%s, %s)\n====Context====\n%s\n"
        (string_of_instr i1) (string_of_instr i2)
        (string_of_context context)
  | InsertLastInstr (context, _, il) ->
      List.iter
        (fun i -> F.fprintf fmt "InsertLastInstr(%s)" (string_of_instr i))
        il;
      F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context)
  | DeleteInstr (context, i1, i2) ->
      F.fprintf fmt "DeleteInstr(%s, %s)\n====Context====\n%s\n"
        (string_of_instr i1) (string_of_instr i2)
        (string_of_context context)
  | DeleteLastInstr (context, _, il) ->
      List.iter
        (fun i -> F.fprintf fmt "DeleteLastInstr(%s)" (string_of_instr i))
        il;
      F.fprintf fmt "\n====Context====\n%s\n" (string_of_context context)
  | UpdateStmt (context, s1, s2) ->
      F.fprintf fmt "UpdateStmt(%s, %s)\n====Context====\n%s\n"
        (string_of_stmt s1) (string_of_stmt s2)
        (string_of_context context)
  | UpdateInstr (context, i1, i2) ->
      F.fprintf fmt "UpdateInstr(%s, %s)\n====Context====\n%s\n"
        (string_of_instr i1) (string_of_instr i2)
        (string_of_context context)
  | UpdateExp (context, e1, e2) ->
      F.fprintf fmt "UpdateExp(%s, %s)\n====Context====\n%s\n"
        (string_of_exp e1) (string_of_exp e2)
        (string_of_context context)
  | InsertExp (context, e1, e2) ->
      F.fprintf fmt "InsertExp(%s, %s)\n====Context====\n%s\n"
        (string_of_exp e1) (string_of_exp e2)
        (string_of_context context)
  | DeleteExp (context, e1, e2) ->
      F.fprintf fmt "DeleteExp(%s, %s)\n====Context====\n%s\n"
        (string_of_exp e1) (string_of_exp e2)
        (string_of_context context)
  (* TODO: Instr level not validated *)
  | _ -> ()

let print_exp e1 = Cil.d_exp () e1 |> Pretty.sprint ~width:80 |> print_endline

let print_node node =
  match node with
  | Node (name, elm_lst) -> (
      print_endline ("Node: " ^ name);
      print_string "Elements: ";
      match elm_lst with
      | [] -> print_endline ""
      | _ ->
          List.iter (fun elm -> print_string (elm ^ ", ")) elm_lst;
          print_endline "")

let pp_edit_script fmt script =
  List.iter (fun action -> F.fprintf fmt "%a\n" pp_action action) script

let print_glob glob =
  Cil.printGlobal !Cil.printerForMaincil () glob
  |> Pretty.sprint ~width:80 |> print_endline

let print_combined_map combined_map =
  print_endline "==========Sparrow - Cil Mapping Result=============";
  match combined_map with
  | CombinedMap (a, b, c) ->
      let stmt_map =
        match a with StmtMap sm -> sm | _ -> failwith "Not a StmtMap"
      in
      let instr_map =
        match b with InstrMap im -> im | _ -> failwith "Not a StmtMap"
      in
      let exp_map =
        match c with ExpMap em -> em | _ -> failwith "Not a StmtMap"
      in
      Cil_map.iter
        (fun k v ->
          print_string (k ^ " --> ");
          print_endline (string_of_stmt v))
        stmt_map;
      Cil_map.iter
        (fun k v ->
          print_string (k ^ " --> ");
          print_endline (string_of_instr v))
        instr_map;
      Cil_map.iter
        (fun k v ->
          print_string (k ^ " --> ");
          print_endline (string_of_exp v))
        exp_map

let print_map map =
  Cil_map.iter
    (fun k v ->
      print_string (k ^ " -> ");
      print_endline v)
    map

(* Utility Functions *)
let rev =
  let rec rev_append acc l =
    match l with [] -> acc | h :: t -> rev_append (h :: acc) t
  in
  fun l -> rev_append [] l

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

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

let subset s1 s2 =
  let set1 = explode s1 in
  let set2 = explode s2 in
  search_seq set1 set2

(* is s2 in s1? *)
let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try
    ignore (Str.search_forward re s1 0);
    true
  with Not_found -> false

let merge_cil_map map1 map2 =
  match (map1, map2) with
  | StmtMap m1, StmtMap m2 ->
      StmtMap (Cil_map.union (fun _ _ y -> Some y) m1 m2)
  | InstrMap m1, InstrMap m2 ->
      InstrMap (Cil_map.union (fun _ _ y -> Some y) m1 m2)
  | ExpMap m1, ExpMap m2 -> ExpMap (Cil_map.union (fun _ _ y -> Some y) m1 m2)
  | _ -> failwith "merge_cil_map: not supported"

let merge_combined_map map1 map2 =
  match (map1, map2) with
  | CombinedMap (sm1, im1, em1), CombinedMap (sm2, im2, em2) ->
      CombinedMap
        (merge_cil_map sm1 sm2, merge_cil_map im1 im2, merge_cil_map em1 em2)

let add_to_combined_map map combined_map =
  match map with
  | NullMap -> combined_map
  | StmtMap _ -> (
      match combined_map with
      | CombinedMap (csm, cim, cem) ->
          CombinedMap (merge_cil_map map csm, cim, cem))
  | InstrMap _ -> (
      match combined_map with
      | CombinedMap (csm, cim, cem) ->
          CombinedMap (csm, merge_cil_map map cim, cem))
  | ExpMap _ -> (
      match combined_map with
      | CombinedMap (csm, cim, cem) ->
          CombinedMap (csm, cim, merge_cil_map map cem))
  | _ -> failwith "add_to_combined_map: not supported"

(* Checking Functions *)
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

let check_instrs stmt =
  match stmt.Cil.skind with Cil.Instr _ -> true | _ -> false

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

let eq_instr instr1 instr2 =
  match (instr1, instr2) with
  | Cil.Set _, Cil.Set _ | Cil.Call _, Cil.Call _ | Cil.Asm _, Cil.Asm _ -> true
  | _ -> false

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

let eq_lval l1 l2 =
  match (l1, l2) with
  | (lhost1, _), (lhost2, _) -> (
      match (lhost1, lhost2) with
      | Cil.Var vi1, Cil.Var vi2 -> vi1.Cil.vname = vi2.Cil.vname
      | Cil.Mem _, Cil.Mem _ -> true
      | _ -> false)

let rec eq_exp e1 e2 =
  match (e1, e2) with
  | Cil.Lval l1, Cil.Lval l2 -> eq_lval l1 l2
  | Cil.SizeOf _, Cil.SizeOf _
  | Cil.SizeOfE _, Cil.SizeOfE _
  | Cil.SizeOfStr _, Cil.SizeOfStr _
  | Cil.AlignOf _, Cil.AlignOf _
  | Cil.AlignOfE _, Cil.AlignOfE _
  | Cil.UnOp _, Cil.UnOp _
  | Cil.BinOp _, Cil.BinOp _
  | Cil.Question _, Cil.Question _ ->
      true
  | Cil.CastE (typ1, e1), Cil.CastE (typ2, e2) ->
      eq_typ typ1 typ2 && eq_exp e1 e2
  | Cil.Const _, Cil.Const _
  | Cil.AddrOf _, Cil.AddrOf _
  | Cil.StartOf _, Cil.StartOf _ ->
      true
  | _ -> false

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

let extract_exp_change e1 e2 context =
  if eq_exp e1 e2 then []
  else
    let _ = L.debug "exp update detected" in
    print_endline "exp update detected";
    [ UpdateExp (context, e1, e2) ]

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

let eq_global glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      eq_typ func_info1.svar.vtype func_info2.svar.vtype
      && func_info1.svar.vname = func_info2.svar.vname
  | Cil.GType _, Cil.GType _
  | Cil.GCompTag _, Cil.GCompTag _
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _
  | Cil.GEnumTag _, Cil.GEnumTag _
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _
  | Cil.GVarDecl _, Cil.GVarDecl _
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
      then extract_block func_info1.sbody func_info2.sbody (GlobalContext glob1)
      else []
  | _ -> []

let rec find_global_change_rec glob1 globals pred result_list =
  match globals with
  | [] -> result_list
  | hd :: tl ->
      if eq_global glob1 hd then pred :: result_list
      else find_global_change_rec glob1 tl hd (pred :: result_list)

let find_global_change glob1 globals =
  match globals with
  | [] -> []
  | hd :: tl ->
      if eq_global glob1 hd then [] else find_global_change_rec glob1 tl hd []

let rec find_continue_point_glob glob1 globals =
  match globals with
  | [] -> []
  | hd :: tl ->
      if eq_global glob1 hd then globals else find_continue_point_glob glob1 tl

let rec fold_globals2 doner_gobals patch_globals =
  match (doner_gobals, patch_globals) with
  | hd1 :: tl1, hd2 :: tl2 ->
      let es = extract_global hd1 hd2 in
      if es <> [] then es @ fold_globals2 tl1 tl2
      else
        let insertions = find_global_change hd1 tl2 in
        if insertions <> [] then
          let _ =
            L.debug "global insertion detected";
            print_endline "global insertion detected"
          in
          fold_globals2 tl1 (find_continue_point_glob (List.hd insertions) tl2)
          @ List.map (fun g -> InsertGlobal (hd1, g)) insertions
        else
          let deletions = find_global_change hd2 tl1 in
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

(* Mapping Functions *)
let rec find_rest c out =
  match c with
  | hd :: tl -> (
      match int_of_string_opt (String.make 1 hd) with
      | Some _ -> find_rest tl (out ^ String.make 1 hd)
      | None -> out)
  | [] -> out

let rec extract_tmp_var char_lst target original =
  match (char_lst, target) with
  | hd1 :: tl1, hd2 :: tl2 ->
      if hd1 = hd2 then extract_tmp_var tl1 tl2 target
      else extract_tmp_var tl1 original original
  | _, [] -> "__cil_tmp" ^ find_rest char_lst ""
  | _ -> failwith "extract_tmp_var: not supported"

let rec eq_param cil_p node_p temp_var_table =
  match (cil_p, node_p) with
  | hd1 :: tl1, hd2 :: tl2 ->
      let p =
        if contains hd1 "__cil_tmp" then
          let found_var =
            extract_tmp_var (explode hd1) (explode "__cil_tmp")
              (explode "__cil_tmp")
          in
          let value =
            Str.global_replace (Str.regexp "\\") ""
              (Cil_map.find found_var temp_var_table)
          in
          Str.global_replace (Str.regexp found_var) value hd1
        else hd1
      in
      if subset p (Str.global_replace (Str.regexp "\"") "" (string_of_exp hd2))
      then eq_param tl1 tl2 temp_var_table
      else false
  | _ -> true

let eq_call node instr lv n p temp_var_table =
  match node with
  | Node (name, elms) -> (
      match elms with
      | [] -> InstrMap Cil_map.empty
      | _ :: tl -> (
          let node_lv = if List.hd tl = "null" then "" else List.hd tl in
          match lv with
          | None ->
              if contains (List.hd (List.tl tl)) (string_of_exp n) then
                if eq_param (List.tl (List.tl tl)) p temp_var_table then
                  InstrMap (Cil_map.add name instr Cil_map.empty)
                else InstrMap Cil_map.empty
              else InstrMap Cil_map.empty
          | Some lv ->
              if node_lv <> "" then
                if
                  contains (string_of_lval lv) node_lv
                  && eq_param (List.tl (List.tl tl)) p temp_var_table
                then InstrMap (Cil_map.add name instr Cil_map.empty)
                else InstrMap Cil_map.empty
              else InstrMap Cil_map.empty))

let eq_set node instr lv exp =
  match node with
  | Node (_, _) ->
      (* TODO: easy *)
      NullMap

let eq_instr node instr temp_var_table =
  match instr with
  | Cil.Set (lv, exp, _) -> eq_set node instr lv exp
  | Cil.Call (lv, n, p, _) -> eq_call node instr lv n p temp_var_table
  | Cil.Asm _ -> NullMap

let rec iter_instrs node instrs combined_map temp_var_table =
  match instrs with
  | [] -> combined_map
  | hd :: tl ->
      iter_instrs node tl
        (add_to_combined_map (eq_instr node hd temp_var_table) combined_map)
        temp_var_table

let eq_if node exp =
  match node with
  | Node (name, elms) ->
      if List.hd elms = "assume" then
        if
          subset
            (Str.global_replace (Str.regexp " ") ""
               (List.hd (List.tl (List.tl elms))))
            (Str.global_replace (Str.regexp " ") "" (string_of_exp exp))
        then ExpMap (Cil_map.add name exp Cil_map.empty)
        else ExpMap Cil_map.empty
      else ExpMap Cil_map.empty

let eq_return stmt node exp =
  match node with
  | Node (name, elms) ->
      if List.hd elms = "return" then
        match exp with
        | Some e ->
            if List.hd (List.tl elms) = string_of_exp e then
              StmtMap (Cil_map.add name stmt Cil_map.empty)
            else StmtMap Cil_map.empty
        | None -> StmtMap (Cil_map.add name stmt Cil_map.empty)
      else StmtMap Cil_map.empty

let rec work_stmt node stmt combined_map temp_var_table =
  match stmt.Cil.skind with
  | Cil.Instr instrs -> iter_instrs node instrs combined_map temp_var_table
  | Cil.Return (exp, _) ->
      add_to_combined_map (eq_return stmt node exp) combined_map
  | Cil.Goto _ -> combined_map
  | Cil.ComputedGoto _ -> combined_map
  | Cil.Break _ -> combined_map
  | Cil.Continue _ -> combined_map
  | Cil.If (exp, t_block, e_block, _) ->
      let condition = eq_if node exp in
      add_to_combined_map condition
        (combine_if_blocks node t_block e_block combined_map temp_var_table)
  | Cil.Switch _ -> combined_map
  | Cil.Loop _ -> combined_map
  | Cil.Block block -> iter_stmts node block.bstmts combined_map temp_var_table
  | Cil.TryFinally _ -> combined_map
  | Cil.TryExcept _ -> combined_map

and combine_if_blocks node t_block e_block combined_map temp_var_table =
  match node with
  | Node (_, elms) ->
      if List.hd elms <> "return" then
        let t_result =
          iter_stmts node t_block.bstmts combined_map temp_var_table
        in
        let e_result =
          iter_stmts node e_block.bstmts combined_map temp_var_table
        in
        merge_combined_map (merge_combined_map t_result e_result) combined_map
      else combined_map

and iter_stmts node stmts combined_map temp_var_table =
  match stmts with
  | [] -> combined_map
  | hd :: tl ->
      merge_combined_map
        (work_stmt node hd combined_map temp_var_table)
        (iter_stmts node tl combined_map temp_var_table)

let work_global node global combined_map temp_var_table =
  match global with
  | Cil.GType _ | Cil.GCompTag _ | Cil.GCompTagDecl _ | Cil.GEnumTag _
  | Cil.GEnumTagDecl _ | Cil.GVarDecl _ | Cil.GVar _ ->
      combined_map
  | Cil.GFun (fundec, _) ->
      iter_stmts node fundec.sbody.bstmts combined_map temp_var_table
  | Cil.GAsm _ | Cil.GPragma _ | Cil.GText _ -> combined_map

let rec iter_globals node globals combined_map temp_var_table =
  match globals with
  | [] -> combined_map
  | hd :: tl ->
      merge_combined_map
        (work_global node hd combined_map temp_var_table)
        (iter_globals node tl combined_map temp_var_table)

let is_call node =
  match node with
  | Node (_, elm) -> (
      match List.hd elm with "call" | "return" | "assume" -> true | _ -> false)

let rec iter_elms globals node_lst combined_map temp_var_table =
  match node_lst with
  | [] -> combined_map
  | hd :: tl ->
      if is_call hd then
        merge_combined_map
          (iter_elms globals tl combined_map temp_var_table)
          (iter_globals hd globals combined_map temp_var_table)
      else
        merge_combined_map
          (iter_elms globals tl combined_map temp_var_table)
          combined_map

let match_kv elms =
  let key = List.hd (List.tl elms) in
  let value = List.hd (List.tl (List.tl elms)) in
  Cil_map.add key value Cil_map.empty

let rec create_temp_map node_lst output_map =
  match node_lst with
  | [] -> output_map
  | hd :: tl -> (
      match hd with
      | Node (_, elms) ->
          if List.hd elms = "alloc" || List.hd elms = "salloc" then
            create_temp_map tl
              (Cil_map.union (fun _ v1 _ -> Some v1) (match_kv elms) output_map)
          else create_temp_map tl output_map)

let map_str_to_cil node_lst file =
  let temp_var_table = create_temp_map node_lst Cil_map.empty in
  iter_elms file.Cil.globals node_lst
    (CombinedMap
       (StmtMap Cil_map.empty, InstrMap Cil_map.empty, ExpMap Cil_map.empty))
    temp_var_table

(* Functions for Parsing Sparrow Node Text *)
let rec parse_rec elm output tmp_str bracket_num quote_num =
  match elm with
  | [] -> [ tmp_str ] @ output
  | hd :: tl -> (
      match hd with
      | '(' -> parse_rec tl output (tmp_str ^ "(") (bracket_num + 1) quote_num
      | ')' -> parse_rec tl output (tmp_str ^ ")") (bracket_num - 1) quote_num
      | ',' ->
          if quote_num = 0 && bracket_num = 0 then
            parse_rec tl ([ tmp_str ] @ output) "" bracket_num quote_num
          else parse_rec tl output (tmp_str ^ ",") bracket_num quote_num
      | '"' ->
          if quote_num = 0 && bracket_num = 0 then
            parse_rec tl output (tmp_str ^ "\"") bracket_num quote_num
          else if quote_num > 0 && bracket_num = 0 then
            parse_rec tl output tmp_str bracket_num (quote_num - 1)
          else parse_rec tl output (tmp_str ^ "\"") bracket_num quote_num
      | ' ' -> parse_rec tl output tmp_str bracket_num quote_num
      | _ ->
          parse_rec tl output (tmp_str ^ String.make 1 hd) bracket_num quote_num
      )

let parse elm = rev (parse_rec elm [] "" 0 0)

let rec parse_sparrow lines =
  match lines with
  | [] -> []
  | hd :: tl ->
      let name_idx = Str.search_forward (Str.regexp {| |}) hd 0 in
      let node_name = Str.first_chars hd name_idx in
      let rest = Str.string_after hd (name_idx + 1) in
      let list_with_quote =
        parse (explode (String.sub rest 1 (String.length rest - 2)))
      in
      let parsed_list =
        List.fold_left
          (fun acc f -> acc @ [ Str.global_replace (Str.regexp "\"") "" f ])
          [] list_with_quote
      in
      [ Node (node_name, parsed_list) ] @ parse_sparrow tl

let init () =
  Cil.initCIL ();
  Cil.insertImplicitCasts := false;
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir);
  Filename.concat !Cmdline.out_dir "transformer.log.txt" |> Logger.from_file;
  Logger.set_level !Cmdline.log_level

let main () =
  init ();
  let doner, patch, donee =
    match Array.to_list Sys.argv |> List.tl with
    | [ a; b; c; _ ] -> (Frontc.parse a (), Frontc.parse b (), Frontc.parse c ())
    | _ ->
        failwith
          "Argument mismatch: must be <Donor> <Patch> <Donee> <Semantic \
           Pattern>"
  in
  let es = extract doner patch in
  Logger.info "#edit script: %d\n%a\n" (List.length es) pp_edit_script es;
  let node_lst = parse_sparrow (read_lines Sys.argv.(4)) in
  let cil_map = map_str_to_cil node_lst donee in
  print_combined_map cil_map

let _ = main ()
