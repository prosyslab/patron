module S = AbsDiff
module D = Diff
module EF = EditFunction
module H = Utils

let is_patched = ref false

let check_sibling_exp sibling exp_list =
  match sibling with
  | Ast.Exp e -> List.exists (fun x -> Ast.isom_exp x e) exp_list
  | _ ->
      failwith
        "check_sibling_exp: sibling of an expression must be an expression"

let check_stmt stmt stmt_list =
  List.exists (fun x -> Ast.isom_stmt x stmt) stmt_list

let check_exp exp exp_list = List.exists (fun x -> Ast.isom_exp x exp) exp_list

let get_sibling_exp sibling exp_list =
  match sibling with
  | Ast.Exp e -> List.find (fun x -> Ast.isom_exp x e) exp_list
  | _ ->
      failwith "get_sibling_exp: sibling of an expression must be an expression"

let get_snk snk stmt_list =
  match snk with
  | Ast.Stmt s -> List.find (fun x -> Ast.isom_stmt x s) stmt_list
  | _ -> failwith "get_snk: snk must be a stmt"

let check_snk snk stmt_list =
  match snk with
  | Ast.Stmt s -> List.exists (fun x -> Ast.isom_stmt x s) stmt_list
  | _ -> failwith "check_snk: snk must be a stmt"

let get_sibling_stmt sibling stmt_list =
  match sibling with
  | Ast.Stmt s -> List.find (fun x -> Ast.isom_stmt x s) stmt_list
  | _ -> failwith "get_sibling_stmt: sibling of a stmt must be a stmt"

let mk_patch_blk old_blk node new_stmt =
  List.fold_left
    (fun acc s ->
      if Utils.eq_stmt_line node.Cil.skind s.Cil.skind then s :: new_stmt :: acc
      else s :: acc)
    [] old_blk
  |> List.rev

let insert_patch func new_stmt patch_block before after =
  let block_size = List.length patch_block in
  if before = [] && after = [] then patch_block @ [ new_stmt ]
  else if before = [] then
    let after = List.hd after in
    let new_blk = mk_patch_blk patch_block after new_stmt in
    if List.length new_blk = block_size then (
      Logger.info "Could not find the appropriate patch location";
      Logger.info
        "Appending the new statement to the end of the block in function %s"
        func;
      patch_block @ [ new_stmt ])
    else (
      Logger.info "Successfully added patch under function %s" func;
      new_blk)
  else
    let before = List.rev before |> List.hd in
    let new_blk = mk_patch_blk patch_block before new_stmt in
    if List.length new_blk = block_size then (
      Logger.info "Could not find the appropriate patch location";
      Logger.info
        "Appending the new statement to the end of the block in function %s"
        func;
      patch_block @ [ new_stmt ])
    else (
      Logger.info "Successfully added patch under function %s" func;
      new_blk)

let iter_body func stmts parent patch_bw patch =
  let before, after = patch_bw in
  List.fold_left
    (fun acc x ->
      match (x.Cil.skind, parent.Cil.skind) with
      | Cil.Loop (b, loc, t1, t2), Cil.Loop (_, loc', _, _) ->
          if loc.Cil.line = loc'.Cil.line || Ast.isom_stmt x parent then
            let new_body = insert_patch func patch b.bstmts before after in
            let new_block = { b with bstmts = new_body } in
            let new_stmt =
              { x with skind = Cil.Loop (new_block, loc, t1, t2) }
            in
            new_stmt :: acc
          else x :: acc
      | Cil.If (e, b1, b2, loc), Cil.If (_, _, _, loc') ->
          (* TODO: bring branch info *)
          if loc.Cil.line = loc'.Cil.line || Ast.isom_stmt x parent then
            let new_b1 = insert_patch func patch b1.bstmts before after in
            (* let new_b2 = insert_patch patch b2.bstmts before after in *)
            let new_block1 = { b1 with bstmts = new_b1 } in
            (* let new_block2 = { b2 with bstmts = new_b2 } in *)
            let new_stmt = { x with skind = Cil.If (e, new_block1, b2, loc) } in
            new_stmt :: acc
          else x :: acc
      | _ -> x :: acc)
    [] stmts
  |> List.rev

let replace_exp_in_stmt stmt from_exp to_exp =
  match stmt.Cil.skind with
  | Cil.Instr i ->
      let new_instr =
        List.fold_left
          (fun acc x ->
            match x with
            | Cil.Call (lval, e, exp_list, loc) ->
                if Ast.isom_exp e from_exp then
                  Cil.Call (lval, to_exp, exp_list, loc) :: acc
                else x :: acc
            | Cil.Set (lval, e, loc) ->
                if Ast.isom_exp e from_exp then
                  Cil.Set (lval, to_exp, loc) :: acc
                else x :: acc
            | _ -> x :: acc)
          [] i
        |> List.rev
      in
      { stmt with skind = Cil.Instr new_instr }
  | _ -> failwith "replace_exp_in_stmt: not implemented"

let delete_elt_stmt elt list =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if Ast.isom_stmt elt hd then aux acc tl else aux (hd :: acc) tl
  in
  let result = aux [] list in
  if List.length result = List.length list - 1 then result
  else failwith "stmt_list delete error"

let replace_exp_in_stmts stmts parent from_exp to_exp =
  List.fold_left
    (fun acc x ->
      if Ast.s_stmt x = Ast.s_stmt parent then
        let new_stmt = replace_exp_in_stmt x from_exp to_exp in
        new_stmt :: acc
      else x :: acc)
    [] stmts
  |> List.rev

class stmtInsertVisitorUnderStmt target_func parent patch_bw stmt =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if f.svar.vname = target_func then (
        let stmts = f.sbody.bstmts in
        let new_stmts = iter_body target_func stmts parent patch_bw stmt in
        is_patched := true;
        ChangeTo { f with sbody = { f.sbody with bstmts = new_stmts } })
      else DoChildren
  end

class stmtInsertVisitorUnderFun target_func patch_bw stmt =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if f.svar.vname = target_func then (
        let stmts = f.sbody.bstmts in
        let before, after = patch_bw in
        let new_stmts = insert_patch target_func stmt stmts before after in
        is_patched := true;
        ChangeTo { f with sbody = { f.sbody with bstmts = new_stmts } })
      else DoChildren
  end

class stmtDeleteVisitor stmt =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      if check_stmt stmt b.bstmts then (
        is_patched := true;
        ChangeTo { b with bstmts = delete_elt_stmt stmt b.bstmts })
      else DoChildren
  end

class expUpdateVisitor target_func parent from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if f.svar.vname = target_func then (
        let stmts = f.sbody.bstmts in
        let new_stmts = replace_exp_in_stmts stmts parent from_exp to_exp in
        is_patched := true;
        ChangeTo { f with sbody = { f.sbody with bstmts = new_stmts } })
      else DoChildren
  end

(* class expInsertVisitor target_func parent exp =
     object
       inherit Cil.nopCilVisitor

       method! vfunc (f : Cil.fundec) =
         if f.svar.vname = target_func then
           let stmts = f.sbody.bstmts in
           let new_stmts =
             List.fold_left
               (fun acc x ->
                 match (x.Cil.skind, parent) with
                 | Cil.Loop (b, loc, t1,*)
let paths2stmts (path1, path2) = (Ast.path2stmts path1, Ast.path2stmts path2)

let apply_insert_stmt ctx stmt donee =
  Logger.info "Applying InsertStmt...";
  is_patched := false;
  let parent = List.hd ctx.D.root_path in
  match parent with
  | Fun func_name ->
      let patch_bound = paths2stmts ctx.D.patch_bound in
      let vis = new stmtInsertVisitorUnderFun func_name patch_bound stmt in
      ignore (Cil.visitCilFile vis donee);
      if not !is_patched then Logger.warn "failed to apply InsertStmt"
      else Logger.info "Successfully applied InsertStmt at %s" func_name
  | Stmt s ->
      let patch_bound = paths2stmts ctx.D.patch_bound in
      let vis =
        new stmtInsertVisitorUnderStmt ctx.top_func_name s patch_bound stmt
      in
      ignore (Cil.visitCilFile vis donee);
      if not !is_patched then Logger.warn "failed to apply InsertStmt"
      else Logger.info "Successfully applied InsertStmt at %s" ctx.top_func_name
  | _ -> failwith "InsertStmt: Incorrect parent type"

let apply_delete_stmt ctx stmt donee =
  Logger.info "Applying DeleteStmt...";
  is_patched := false;
  let vis = new stmtDeleteVisitor stmt in
  ignore (Cil.visitCilFile vis donee);
  if not !is_patched then Logger.info "failed to apply DeleteStmt"
  else Logger.info "Successfully applied DeleteStmt at %s" ctx.D.top_func_name

let apply_update_exp conc_ctx abs_ctx from_exp to_exp donee =
  Logger.info "Applying UpdateExp...";
  let parent = List.hd conc_ctx.D.root_path in
  let target_func = abs_ctx.AbsDiff.func_name in
  is_patched := false;
  match parent with
  | Fun _ -> failwith "UpdateExp: not implemented"
  | Stmt s ->
      let vis = new expUpdateVisitor target_func s from_exp to_exp in
      ignore (Cil.visitCilFile vis donee);
      if not !is_patched then Logger.warn "failed to apply UpdateExp"
      else Logger.info "Successfully applied UpdateExp at %s" target_func
  | _ -> failwith "UpdateExp: Incorrect parent type"

let apply_action diff donee action =
  match (action, diff) with
  | D.InsertStmt (ctx, stmt), AbsDiff.SInsertStmt _ ->
      apply_insert_stmt ctx stmt donee
  | DeleteStmt (ctx, stmt), AbsDiff.SDeleteStmt _ ->
      apply_delete_stmt ctx stmt donee
  | UpdateExp (conc_ctx, from_exp, to_exp), AbsDiff.SUpdateExp (abs_ctx, _, _)
    ->
      apply_update_exp conc_ctx abs_ctx from_exp to_exp donee
  (* | InsertExp (context, exp) ->
         let vis = new expInsertVisitorInstr context exp in
         ignore (Cil.visitCilFile vis donee)
     | DeleteExp (context, exp) ->
         let vis = new expDeleteVisitorInstr context exp in
         ignore (Cil.visitCilFile vis donee)
     | UpdateExp (context, _from, _to) ->
         let vis = new expUpdateVisitorInstr context _from _to in
         ignore (Cil.visitCilFile vis donee)
     | InsertLval (context, lval) ->
         let vis = new lvalInsertVisitorInstr context lval in
         ignore (Cil.visitCilFile vis donee)
     | DeleteLval (context, lval) ->
         let vis = new lvalDeleteVisitorInstr context lval in
         ignore (Cil.visitCilFile vis donee)
     | UpdateLval (context, _from, _to) ->
         let vis = new lvalUpdateVisitorInstr context _from _to in
         ignore (Cil.visitCilFile vis donee) *)
  | _ -> failwith "apply_action:Not implemented"

let write_out path ast =
  let out_chan_orig = Core.Out_channel.create path in
  Cil.dumpFile Cil.defaultCilPrinter out_chan_orig path ast

let apply abs_diff donee edit_function =
  Logger.info "%d actions to apply" (List.length edit_function);
  List.iter2
    (fun action diff -> apply_action diff donee action)
    edit_function (List.rev abs_diff);
  donee
