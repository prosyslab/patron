open Core
module S = AbsDiff
module D = Diff
module EF = EditFunction
module H = Utils
module L = Logger

let is_patched = ref false

let partition_using_before before stmts =
  let blst, _, alst =
    List.fold_left
      ~f:(fun (blst, found, alst) stmt ->
        if not found then
          if phys_equal stmt before then (blst, true, alst)
          else (stmt :: blst, found, alst)
        else (blst, found, stmt :: alst))
      ~init:([], false, []) stmts
  in
  (List.rev blst, alst)

let insert_internal ?(update = false) after patch stmts =
  if Option.is_none after then patch @ stmts
  else
    let after = Option.value_exn after in
    let new_stmts_rev, patched =
      List.fold_left
        ~f:(fun (new_stmts, patched) stmt ->
          if phys_equal stmt after || (update && Ast.is_cil_goto stmt.Cil.skind)
          then (patch @ (after :: new_stmts), true)
          else (stmt :: new_stmts, patched))
        ~init:([], false) stmts
    in
    let new_stmts = List.rev new_stmts_rev in
    if patched then new_stmts else new_stmts @ patch

let insert_ss_into_stmts ?(update = false) before after patch stmts =
  let blst, alst = partition_using_before before stmts in
  match before.Cil.skind with
  | Cil.Loop (block, loc, t1, t2) ->
      let new_b_stmts =
        insert_internal ~update after patch (List.rev block.bstmts)
      in
      let new_stmt =
        Cil.Loop ({ block with bstmts = new_b_stmts }, loc, t1, t2)
      in
      blst @ [ { before with skind = new_stmt } ] @ alst
  | Cil.If (e, tb, fb, loc) ->
      (* TODO: check true branch false branch *)
      if List.is_empty tb.bstmts then
        let new_b_stmts =
          insert_internal ~update after patch (List.rev tb.bstmts)
        in
        let new_stmt = Cil.If (e, { tb with bstmts = new_b_stmts }, fb, loc) in
        blst @ [ { before with skind = new_stmt } ] @ alst
      else
        let new_b_stmts =
          insert_internal ~update after patch (List.rev fb.bstmts)
        in
        let new_stmt = Cil.If (e, tb, { fb with bstmts = new_b_stmts }, loc) in
        blst @ [ { before with skind = new_stmt } ] @ alst
  | _ ->
      let new_alst = insert_internal ~update after patch (List.rev alst) in
      blst @ [ before ] @ new_alst

let is_in_stmt s b = List.exists ~f:(fun stmt -> phys_equal s stmt) b.Cil.bstmts

class insertStmtFuncVisitor ?(update = false) before after ss =
  object
    inherit Cil.nopCilVisitor

    method! vblock b =
      if is_in_stmt before b then (
        let new_stmts = insert_ss_into_stmts ~update before after ss b.bstmts in
        is_patched := true;
        ChangeTo { b with bstmts = new_stmts })
      else DoChildren
  end

class insertStmtVisitor ?(update = false) target_func before after ss =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then
        ChangeTo
          (Cil.visitCilFunction
             (new insertStmtFuncVisitor ~update before after ss)
             f)
      else DoChildren
  end

let delete_elt_stmt s stmts =
  let new_stmts, patched =
    List.fold_left
      ~f:(fun (new_stmts, patched) stmt ->
        if (not patched) && phys_equal stmt s then (new_stmts, true)
        else (stmt :: new_stmts, patched))
      ~init:([], false) stmts
  in
  (List.rev new_stmts, patched)

class deleteStmtfromBlockVisitor s =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      let new_bstmts, patched = delete_elt_stmt s b.bstmts in
      if patched then (
        is_patched := true;
        ChangeTo { b with bstmts = new_bstmts })
      else DoChildren
  end

class deleteStmtfromFuncVisitor target_func ss =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then
        let vis = new deleteStmtfromBlockVisitor ss in
        ChangeTo (Cil.visitCilFunction vis f)
      else SkipChildren
  end

class replaceExpVisitor from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vexpr e =
      if Ast.eq_exp from_exp e then (
        is_patched := true;
        ChangeTo to_exp)
      else DoChildren
  end

class replaceExpinStmt parent from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vstmt s =
      if phys_equal parent s then
        let vis = new replaceExpVisitor from_exp to_exp in
        ChangeTo (Cil.visitCilStmt vis s)
      else DoChildren
  end

class updateExpVisitor target_func parent from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then
        let vis = new replaceExpinStmt parent from_exp to_exp in
        ChangeTo (Cil.visitCilFunction vis f)
      else SkipChildren
  end

let apply_insert_stmt ?(update = false) func_name before after ss donee =
  if update then L.info "Applying UpdateStmt..."
  else L.info "Applying InsertStmt...";
  is_patched := false;
  List.iter ~f:(fun s -> L.info "before:\n%s" (Ast.s_stmt s)) before;
  if List.is_empty before then
    L.error "apply_insert_stmt - cannot be patched because before list is empty";
  let very_before = List.last_exn before in
  L.info "very_before:\n%s" (Ast.s_stmt very_before);
  let very_after = List.hd after in
  let vis = new insertStmtVisitor ~update func_name very_before very_after ss in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply InsertStmt"
  else L.info "Successfully applied InsertStmt at %s" func_name

let apply_delete_stmt func_name s donee =
  L.info "Applying DeleteStmt...";
  is_patched := false;
  let vis = new deleteStmtfromFuncVisitor func_name s in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply DeleteStmt"
  else L.info "Successfully applied DeleteStmt at %s" func_name

let apply_update_exp func_name s e1 e2 donee =
  L.info "Applying UpdateExp...";
  is_patched := false;
  let vis = new updateExpVisitor func_name s e1 e2 in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply UpdateExp"
  else L.info "Successfully applied UpdateExp at %s" func_name

let apply_action donee = function
  | D.InsertStmt (func_name, before, ss, after) ->
      apply_insert_stmt func_name before after ss donee
  | D.DeleteStmt (func_name, s) -> apply_delete_stmt func_name s donee
  | D.UpdateStmt (func_name, before, ss, after) ->
      apply_insert_stmt ~update:true func_name before after ss donee
  | D.UpdateExp (func_name, s, e1, e2) ->
      apply_update_exp func_name s e1 e2 donee
  | _ -> L.error "apply_action - Not implemented"

let write_out path ast =
  let out_chan_orig = Core.Out_channel.create path in
  Cil.dumpFile Cil.defaultCilPrinter out_chan_orig path ast

let apply donee diff =
  Logger.info "%d actions to apply" (List.length diff);
  List.iter ~f:(apply_action donee) diff;
  donee
