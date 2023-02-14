type edit_script =
  | InsertStmt of Cil.stmt * Cil.stmt
  | DeleteStmt of Cil.stmt
  | UpdateStmt of Cil.stmt * Cil.stmt
  | InsertInstr of Cil.instr * Cil.instr
  | DeleteInstr of Cil.instr
  | UpdateInstr of Cil.instr * Cil.instr
  | UpdateExp of Cil.exp * Cil.exp
  | UpdateLval of Cil.lval * Cil.lval

let extract cil1 cil2 = ()
let translate cil1 cil3 es = es
let apply es cil3 = cil3

let main () =
  Cil.initCIL ();
  Cil.insertImplicitCasts := false;
  let donor, patch, donee =
    match Array.to_list Sys.argv |> List.tl with
    | [ a; b; c ] -> (Frontc.parse a (), Frontc.parse b (), Frontc.parse c ())
    | _ -> failwith "Argument mismatch: must be <Donor> <Patch> <Donee>"
  in
  let es = extract donor patch in
  let es' = translate donor donee es in
  let patched_donee = apply es' donee in
  Cil.dumpFile !Cil.printerForMaincil stdout "" patched_donee

let _ = main ()
