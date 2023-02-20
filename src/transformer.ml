module F = Format
module L = Logger

type action =
  (* InsrtStmt(s1, s2) : insert statement s2 before statement s1 *)
  | InsertStmt of Cil.stmt * Cil.stmt
  | InsertLastStmt of Cil.block * Cil.stmt list
  | DeleteStmt of Cil.stmt
  | DeleteLastStmt of Cil.block * Cil.stmt list
  | UpdateStmt of Cil.stmt * Cil.stmt
  | InsertInstr of Cil.instr * Cil.instr
  | DeleteInstr of Cil.instr
  | UpdateInstr of Cil.instr * Cil.instr
  | UpdateExp of Cil.exp * Cil.exp
  | UpdateLval of Cil.lval * Cil.lval

type edit_script = action list

let string_of_instr instr =
  Cil.printInstr !Cil.printerForMaincil () instr |> Pretty.sprint ~width:80

let string_of_stmt stmt =
  Cil.printStmt !Cil.printerForMaincil () stmt |> Pretty.sprint ~width:80

let pp_action fmt = function
  | InsertStmt (s1, s2) ->
      F.fprintf fmt "InsertStmt(%s, %s)" (string_of_stmt s1) (string_of_stmt s2)
  | InsertLastStmt (_, sl) ->
      List.iter
        (fun s -> F.fprintf fmt "InsertLastStmt(%s)" (string_of_stmt s))
        sl
  | DeleteStmt s -> F.fprintf fmt "DeleteStmt(%s)" (string_of_stmt s)
  (* TODO: Changgong *)
  | _ -> ()

let pp_edit_script fmt script =
  List.iter (fun action -> F.fprintf fmt "%a\n" pp_action action) script

let print_skind skind =
  let () = Printf.printf "%s" skind.Cil.cname in
  print_endline "-----------------"

let print_glob glob =
  Cil.printGlobal !Cil.printerForMaincil () glob
  |> Pretty.sprint ~width:80 |> print_endline

(* Checking Functions *)
let eq_stmt_kind skind1 skind2 =
  match (skind1, skind2) with
  | Cil.Instr _, Cil.Instr _
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

let rec find_insertion s1 ss2 =
  match ss2 with
  | [] -> []
  | s2 :: ss2' ->
      if eq_stmt_kind s1.Cil.skind s2.Cil.skind then []
      else s2 :: find_insertion s1 ss2'

let rec find_deletion s2 ss1 =
  match ss1 with
  | [] -> []
  | s1 :: ss2' ->
      if eq_stmt_kind s2.Cil.skind s2.Cil.skind then []
      else s1 :: find_deletion s1 ss2'

let rec fold_stmts2 b1 stmts1 stmts2 =
  match (stmts1, stmts2) with
  | s1 :: ss1, s2 :: ss2 ->
      if eq_stmt_kind s1.Cil.skind s2.Cil.skind then fold_stmts2 b1 ss1 ss2
      else
        let insertions = find_insertion s1 stmts2 in
        if insertions <> [] then
          let _ = L.debug "insertion detected\n" in
          List.map (fun s -> InsertStmt (s1, s)) insertions
        else
          let deletions = find_deletion s2 stmts1 in
          if deletions <> [] then
            let _ = L.debug "deletion detected\n" in
            List.map (fun s -> DeleteStmt s) deletions
          else fold_stmts2 b1 ss1 ss2
  | [], _ -> [ InsertLastStmt (b1, stmts2) ]
  | _, [] -> [ DeleteLastStmt (b1, stmts1) ]

let extract_block block1 block2 =
  fold_stmts2 block1 block1.Cil.bstmts block2.Cil.bstmts

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
