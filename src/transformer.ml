type action =
  | InsertStmt of Cil.stmt * Cil.stmt
  | DeleteStmt of Cil.stmt
  | UpdateStmt of Cil.stmt * Cil.stmt
  | InsertInstr of Cil.instr * Cil.instr
  | DeleteInstr of Cil.instr
  | UpdateInstr of Cil.instr * Cil.instr
  | UpdateExp of Cil.exp * Cil.exp
  | UpdateLval of Cil.lval * Cil.lval

type edit_script = action list

(* Print Functions *)
let print_skind skind =
  let () = Printf.printf "%s" skind.Cil.cname in
  print_endline "-----------------"

let print_stmt stmt =
  let () =
    Cil.printStmt !Cil.printerForMaincil () stmt
    |> Pretty.sprint ~width:80 |> print_endline
  in
  print_endline "-----------------"

let print_glob glob =
  Cil.printGlobal !Cil.printerForMaincil () glob
  |> Pretty.sprint ~width:80 |> print_endline

(* Checking Functions *)
let eq_stmt_type skind1 skind2 =
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

module StmtMap = Map.Make (struct
  type t = Cil.stmt

  let compare s1 s2 = compare s1.Cil.sid s2.Cil.sid
end)

let is_same_stmt stmt1 stmt2 =
  eq_stmt_type stmt1.Cil.skind stmt2.Cil.skind && stmt1.Cil.sid = stmt2.Cil.sid

(* Bipartite twice *)

let search_stmt stmt2 stmts stmt_map =
  List.fold_left
    (fun stmap stmt ->
      if
        eq_stmt_type stmt.Cil.skind stmt2.Cil.skind
        && not (StmtMap.exists (fun _ y -> is_same_stmt stmt y) stmap)
      then StmtMap.add stmt stmt2 stmap
      else stmap)
    stmt_map stmts

let search_func stmt2 file stmt_map =
  Cil.foldGlobals file
    (fun sm global ->
      match global with
      | Cil.GFun (dec, _) -> search_stmt stmt2 dec.sbody.bstmts sm
      | _ -> sm)
    stmt_map

let map_stmt file mapped_stmts stmts =
  List.fold_left
    (fun mapped_stmts stmt ->
      if not (StmtMap.exists (fun x _ -> is_same_stmt stmt x) mapped_stmts) then
        search_func stmt file mapped_stmts
      else mapped_stmts)
    mapped_stmts stmts

let mapping file1 file2 =
  Cil.foldGlobals file1
    (fun mapped_stmts global ->
      match global with
      | Cil.GFun (dec, _) -> map_stmt file2 mapped_stmts dec.sbody.bstmts
      | _ -> mapped_stmts)
    StmtMap.empty

let extract doner_file patch_file =
  let fwd_map = mapping doner_file patch_file in
  let bwd_map = mapping patch_file doner_file in
  print_int (StmtMap.cardinal fwd_map);
  print_endline "";
  print_int (StmtMap.cardinal bwd_map);
  print_endline ""

(* let translate cil1 cil3 es = es in
   let apply es cil3 = cil3 in *)

let main () =
  Cil.initCIL ();
  Cil.insertImplicitCasts := true;
  let doner, patch, donee =
    match Array.to_list Sys.argv |> List.tl with
    | [ a; b; c ] -> (Frontc.parse a (), Frontc.parse b (), Frontc.parse c ())
    | _ -> failwith "Argument mismatch: must be <Donor> <Patch> <Donee>"
  in

  extract doner patch

let _ = main ()
