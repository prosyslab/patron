type edit_script =
  | InsertStmt of Cil.stmt * Cil.stmt
  | DeleteStmt of Cil.stmt
  | UpdateStmt of Cil.stmt * Cil.stmt
  | InsertInstr of Cil.instr * Cil.instr
  | DeleteInstr of Cil.instr
  | UpdateInstr of Cil.instr * Cil.instr
  | UpdateExp of Cil.exp * Cil.exp

let extract cil1 cil2 = ()
let translate cil1 cil3 es = ()
let apply es cil3 = cil3
let main () = ()
let _ = main ()
