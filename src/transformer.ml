module F = Format
module L = Logger
module C = Cmdline

type action =
  (* InsrtStmt(s1, s2) : insert statement s2 before statement s1 *)
  | InsertStmt of Cil.stmt * Cil.stmt
  | InsertLastStmt of Cil.block * Cil.stmt list
  | DeleteStmt of Cil.stmt * Cil.stmt
  | DeleteLastStmt of Cil.block * Cil.stmt list
  | UpdateStmt of Cil.stmt * Cil.stmt
  | InsertInstr of Cil.instr * Cil.instr
  | InsertLastInstr of Cil.stmt * Cil.instr list
  | DeleteInstr of Cil.instr * Cil.instr
  | DeleteLastInstr of Cil.stmt * Cil.instr list
  | UpdateInstr of Cil.instr * Cil.instr
  | InsertExp of Cil.exp * Cil.exp
  | InsertLastExp of Cil.exp * Cil.exp list
  | DeleteExp of Cil.exp * Cil.exp
  | DeleteLastExp of Cil.exp * Cil.exp list
  | UpdateExp of Cil.exp * Cil.exp
  | UpdateLval of Cil.lval * Cil.lval

type edit_script = action list

let string_of_instr instr =
  Cil.printInstr !Cil.printerForMaincil () instr |> Pretty.sprint ~width:80

let string_of_stmt stmt =
  Cil.printStmt !Cil.printerForMaincil () stmt |> Pretty.sprint ~width:80

let string_of_exp exp =
  Cil.d_exp () exp |> Pretty.sprint ~width:80

let pp_action fmt = function
  | InsertStmt (s1, s2) ->
      F.fprintf fmt "InsertStmt(%s, %s)" (string_of_stmt s1) (string_of_stmt s2)
  | InsertLastStmt (_, sl) ->
      List.iter
        (fun s -> F.fprintf fmt "InsertLastStmt(%s)" (string_of_stmt s))
        sl
  | DeleteStmt (s1, s2) ->
      F.fprintf fmt "DeleteStmt(%s, %s)" (string_of_stmt s1) (string_of_stmt s2)
  | DeleteLastStmt (_, sl) ->
      List.iter
        (fun s -> F.fprintf fmt "DeleteLastStmt(%s)" (string_of_stmt s))
        sl
  | InsertInstr (i1, i2) ->
      F.fprintf fmt "InsertInstr(%s, %s)" (string_of_instr i1)
        (string_of_instr i2)
  | InsertLastInstr (_, il) ->
      List.iter
        (fun i -> F.fprintf fmt "InsertLastInstr(%s)" (string_of_instr i))
        il
  | DeleteInstr (i1, i2) ->
      F.fprintf fmt "DeleteInstr(%s, %s)" (string_of_instr i1)
        (string_of_instr i2)
  | DeleteLastInstr (_, il) ->
      List.iter
        (fun i -> F.fprintf fmt "DeleteLastInstr(%s)" (string_of_instr i))
        il
  | UpdateStmt (s1, s2) ->
      F.fprintf fmt "UpdateStmt(%s, %s)" (string_of_stmt s1) (string_of_stmt s2)
  | UpdateInstr (i1, i2) ->
      F.fprintf fmt "UpdateInstr(%s, %s)" (string_of_instr i1)
        (string_of_instr i2)
  | UpdateExp (e1, e2) ->
      F.fprintf fmt "UpdateExp(%s, %s)"
        (Cil.d_exp () e1 |> Pretty.sprint ~width:80)
        (Cil.d_exp () e2 |> Pretty.sprint ~width:80)
  | InsertExp (e1, e2) ->
      F.fprintf fmt "InsertExp(%s, %s)"
        (Cil.d_exp () e1 |> Pretty.sprint ~width:80)
        (Cil.d_exp () e2 |> Pretty.sprint ~width:80)
  | DeleteExp (e1, e2) ->
      F.fprintf fmt "DeleteExp(%s, %s)"
        (Cil.d_exp () e1 |> Pretty.sprint ~width:80)
        (Cil.d_exp () e2 |> Pretty.sprint ~width:80)
  (* TODO: Instr level not validated *)
  | _ -> ()

let print_exp e1 =
  Cil.d_exp () e1 |> Pretty.sprint ~width:80 |> print_endline
let pp_edit_script fmt script =
  List.iter (fun action -> F.fprintf fmt "%a\n" pp_action action) script

let print_skind skind =
  Printf.printf "%s" skind.Cil.cname


let print_glob glob =
  Cil.printGlobal !Cil.printerForMaincil () glob
  |> Pretty.sprint ~width:80 |> print_endline

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

let check_instrs stmt =
  match stmt.Cil.skind with Cil.Instr _ -> true | _ -> false

let rec find_stmt_change_rec s1 ss2 pred result_list =
  match ss2 with
  | [] -> result_list
  | s2 :: ss2' ->
      if eq_stmt_kind s1.Cil.skind s2.Cil.skind then [ pred ] @ result_list
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
      if eq_instr i1 i2 then [ pred ] @ result_list
      else find_instr_change_rec i1 is2' i2 result_list

let find_instr_change i1 is2 result_list =
  match is2 with
  | [] -> []
  | i2 :: is2' ->
      if eq_instr i1 i2 then []
      else find_instr_change_rec i1 is2' i2 result_list
      

  let eq_lval l1 l2 =
    match (l1, l2) with
    | (lhost1, _), (lhost2, _) -> match (lhost1, lhost2) with
      | Cil.Var vi1, Cil.Var vi2 -> vi1.Cil.vname = vi2.Cil.vname
      | Cil.Mem _, Cil.Mem _ -> true
    | _ -> false

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
    | Cil.Question _, Cil.Question _ -> true
    | Cil.CastE (typ1, e1), Cil.CastE (typ2, e2) -> eq_typ typ1 typ2 && eq_exp e1 e2
    | Cil.Const _, Cil.Const _
    | Cil.AddrOf _, Cil.AddrOf _
    | Cil.StartOf _, Cil.StartOf _ -> true
    | _ -> false

let rec find_param_change_rec e1 es2 pred result_list =
  match es2 with
  | [] -> result_list
  | e2 :: es2' ->
      if eq_exp e1 e2 then [ pred ] @ result_list
      else find_param_change_rec e1 es2' e2 result_list

let find_param_change e1 es2 result_list =
  match es2 with
  | [] -> result_list
  | e2 :: es2' ->
      if eq_exp e1 e2 then [ e1 ] else find_param_change_rec e1 es2' e2 result_list

let rec fold_params2 i1 params1 params2 =
  match (params1, params2) with
  | p1 :: ps1, p2 :: ps2 ->
      if eq_exp p1 p2 then fold_params2 i1 ps1 ps2
      else
        let insertions = find_param_change p1 params2 [] in
        if insertions <> [] then (
          let _ = L.debug "param insert detected\n" in
          List.map (fun p -> InsertExp (p1, p)) insertions)
        else
          let deletions = find_param_change p2 params1 [] in
          if deletions <> [] then (
            let _ = L.debug "param delete detected" in
            List.map (fun p -> DeleteExp (p2, p)) deletions)
          else let _ = L.debug "param update detected" in
          [ UpdateExp (p1, p2) ] @ fold_params2 i1 ps1 (List.tl ps2)
  | [], [] -> []
  | _ -> []

let rec work_exp_change e1 e2 =
  if eq_exp e1 e2 then []
  else
    let _ = L.debug "exp update detected" in
    [ UpdateExp (e1, e2) ]

let work_instr i1 i2 =
  match (i1, i2) with
  | Cil.Call (_, e1, params1, _), Cil.Call (_, e2, params2, _) ->
      let e_result = work_exp_change e1 e2 in
      let params_result = fold_params2 i1 params1 params2 in
      e_result @ params_result
  | _ -> []

let rec fold_instrs2 s1 instrs1 instrs2 =
  match (instrs1, instrs2) with
  | i1 :: is1, i2 :: is2 ->
      if eq_instr i1 i2 then
        let work_result = work_instr i1 i2 in
        if work_result <> [] then work_result else fold_instrs2 s1 is1 is2
      else
        let insertions = find_instr_change i1 instrs2 [] in
        if insertions <> [] then (
          let _ = L.debug "instr insertion detected\n" in
          List.map (fun i -> InsertInstr (i1, i)) insertions)
        else
          let deletions = find_instr_change i2 instrs1 [] in
          if deletions <> [] then (
            let _ = L.debug "instr deletion detected\n" in
            List.map (fun i -> DeleteInstr (i2, i)) deletions)
          else fold_instrs2 s1 is1 is2
  | [], [] -> [] (* Last cases needed*)
  | [], _ -> [ InsertLastInstr (s1, instrs2) ]
  | _, [] -> [ DeleteLastInstr (s1, instrs1) ]

let rec fold_stmts2 b1 stmts1 stmts2 =
  match (stmts1, stmts2) with
  | s1 :: ss1, s2 :: ss2 ->
      if eq_stmt_kind s1.Cil.skind s2.Cil.skind then
        let work_result = work_skind s1 s2 in
        if work_result <> [] then work_result else fold_stmts2 b1 ss1 ss2
      else
        let insertions = find_stmt_change s1 stmts2 [] in
        if insertions <> [] then (
          let _ = L.debug "stmt insertion detected\n" in
          List.map (fun s -> InsertStmt (s1, s)) insertions)
        else
          let deletions = find_stmt_change s2 stmts1 [] in
          if deletions <> [] then (
            let _ = L.debug "stmt deletion detected\n" in
            List.map (fun s -> DeleteStmt (s2, s)) deletions)
          else fold_stmts2 b1 ss1 ss2
  | [], [] -> []
  | [], _ -> [ InsertLastStmt (b1, stmts2) ]
  | _, [] -> [ DeleteLastStmt (b1, stmts1) ]

and extract_block block1 block2 =
  fold_stmts2 block1 block1.Cil.bstmts block2.Cil.bstmts

and work_skind s1 s2 =
  match (s1.Cil.skind, s2.Cil.skind) with
  | Cil.Instr instrs1, Cil.Instr instrs2 ->
      let instr_result = fold_instrs2 s1 instrs1 instrs2 in
      if instr_result <> [] then instr_result else []
  | Cil.If (_, t_block1, e_block1, _), Cil.If (_, t_block2, e_block2, _)
    ->
      let t_result = extract_block t_block1 t_block2 in
      let e_result = extract_block e_block1 e_block2 in
      t_result @ e_result
  | _ -> []

let extract_global glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      if
        eq_typ func_info1.svar.vtype func_info2.svar.vtype
        && func_info1.svar.vname = func_info2.svar.vname
      then extract_block func_info1.sbody func_info2.sbody
      else []
  | _ -> []

let rec fold_globals2 doner_gobals patch_globals =
  match (doner_gobals, patch_globals) with
  | hd1 :: tl1, hd2 :: tl2 ->
      let es = extract_global hd1 hd2 in
      es @ fold_globals2 tl1 tl2
  | _ -> []

let extract doner_file patch_file =
  fold_globals2 doner_file.Cil.globals patch_file.Cil.globals

let init () =
  Cil.initCIL ();
  Cil.insertImplicitCasts := true;
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir);
  Filename.concat !Cmdline.out_dir "transformer.log.txt" |> Logger.from_file;
  Logger.set_level !Cmdline.log_level

let main () =
  init ();
  let doner, patch, _donee =
    match Array.to_list Sys.argv |> List.tl with
    | [ a; b; c ] -> (Frontc.parse a (), Frontc.parse b (), Frontc.parse c ())
    | _ -> failwith "Argument mismatch: must be <Donor> <Patch> <Donee>"
  in
  let es = extract doner patch in
  Logger.info "#edit script: %d\n%a\n" (List.length es) pp_edit_script es

let _ = main ()
