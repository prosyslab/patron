module S = SymDiff
module D = Diff
module EF = EditFunction
module H = Utils

(* let check_parent parent instr =
   match parent with
   | D.CilElement.EStmt s -> (
       match s.skind with
       | Cil.Instr i -> (
           match (List.hd i, instr) with
           | Cil.Call (l, e, _, loc1), Cil.Call (l', e', _', loc2) ->
               l = l' && e = e' && loc1 = loc2
           | Cil.Set (l, e, loc1), Cil.Set (l', e', loc2) ->
               l = l' && e = e' && loc1 = loc2
           | _ -> false)
       | _ -> false)
   | _ ->
       failwith
         "check_parent: an expression cannot be inserted without the parent" *)

let check_sibling_exp sibling exp_list =
  match sibling with
  | D.CilElement.EExp e ->
      List.exists (fun x -> H.string_of_exp x = H.string_of_exp e) exp_list
  | _ ->
      failwith
        "check_sibling_exp: sibling of an expression must be an expression"

let check_stmt stmt stmt_list =
  List.exists (fun x -> H.string_of_stmt x = H.string_of_stmt stmt) stmt_list

let check_exp exp exp_list =
  List.exists (fun x -> H.string_of_exp x = H.string_of_exp exp) exp_list

(* let check_parent_stmt parent node =
   match parent.Cil.skind with
   | Cil.Loop (b, _, _, _) -> H.eq_block b node
   | Cil.Block b -> H.eq_block b node
   | Cil.If (_, b1, b2, _) -> H.eq_block b1 node || H.eq_block b2 node
   | _ -> failwith "check_parent_stmt: parent is not a stmt" *)

let get_sibling_exp sibling exp_list =
  match sibling with
  | D.CilElement.EExp e ->
      List.find (fun x -> H.string_of_exp x = H.string_of_exp e) exp_list
  | _ ->
      failwith "get_sibling_exp: sibling of an expression must be an expression"

let get_snk snk stmt_list =
  match snk with
  | D.CilElement.EStmt s ->
      List.find (fun x -> H.string_of_stmt x = H.string_of_stmt s) stmt_list
  | _ -> failwith "get_snk: snk must be a stmt"

let check_snk snk stmt_list =
  match snk with
  | D.CilElement.EStmt s ->
      List.exists (fun x -> H.string_of_stmt x = H.string_of_stmt s) stmt_list
  | _ -> failwith "check_snk: snk must be a stmt"

let get_sibling_stmt sibling stmt_list =
  match sibling with
  | D.CilElement.EStmt s ->
      List.find (fun x -> H.string_of_stmt x = H.string_of_stmt s) stmt_list
  | _ -> failwith "get_sibling_stmt: sibling of a stmt must be a stmt"

(* class expInsertVisitorInstr context (exp : Cil.exp) =
     object
       inherit Cil.nopCilVisitor

       method! vinst (i : Cil.instr) =
         if check_parent context.D.Diff.parent i then
           match i with
           | Cil.Call (lval, e, exp_list, loc) ->
               if check_sibling_exp context.left_sibling exp_list then
                 let prev_exp = get_sibling_exp context.left_sibling exp_list in
                 ChangeTo
                   [
                     Cil.Call
                       (lval, e, H.append_after_elt_exp prev_exp exp exp_list, loc);
                   ]
               else if check_sibling_exp context.right_sibling exp_list then
                 let next_exp = get_sibling_exp context.right_sibling exp_list in
                 ChangeTo
                   [
                     Cil.Call
                       (lval, e, H.append_before_elt_exp next_exp exp exp_list, loc);
                   ]
               else
                 failwith
                   "expInsertVisitorInstr: an expression cannot be inserted \
                    without any sibling info"
           | _ -> DoChildren
         else DoChildren
     end

   class lvalInsertVisitorInstr context (lval : Cil.lval) =
     object
       inherit Cil.nopCilVisitor

       method! vinst (i : Cil.instr) =
         if check_parent context.D.Diff.parent i then
           match i with
           | Cil.Call (None, e, exp_list, loc) ->
               ChangeTo [ Cil.Call (Some lval, e, exp_list, loc) ]
           | _ -> DoChildren
         else DoChildren
     end

   class lvalDeleteVisitorInstr context (lval : Cil.lval) =
     object
       inherit Cil.nopCilVisitor

       method! vinst (i : Cil.instr) =
         if check_parent context.D.Diff.parent i then
           match i with
           | Cil.Call (Some l, e, exp_list, loc) ->
               if H.string_of_lval l = H.string_of_lval lval then
                 ChangeTo [ Cil.Call (None, e, exp_list, loc) ]
               else failwith "lvalDeleteVisitorInstr: lval not found"
           | _ -> DoChildren
         else DoChildren
     end

   class lvalUpdateVisitorInstr context (_from : Cil.lval) (_to : Cil.lval) =
     object
       inherit Cil.nopCilVisitor

       method! vinst (i : Cil.instr) =
         if check_parent context.D.Diff.parent i then
           match i with
           | Cil.Call (Some l, e, exp_list, loc) ->
               if H.string_of_lval l = H.string_of_lval _from then
                 ChangeTo [ Cil.Call (Some _to, e, exp_list, loc) ]
               else failwith "lvalDeleteVisitorInstr: lval not found"
           | _ -> DoChildren
         else DoChildren
     end

   class expDeleteVisitorInstr context (exp : Cil.exp) =
     object
       inherit Cil.nopCilVisitor

       method! vinst (i : Cil.instr) =
         if check_parent context.D.Diff.parent i then
           match i with
           | Cil.Call (lval, e, exp_list, loc) ->
               if check_exp exp exp_list then
                 ChangeTo
                   [ Cil.Call (lval, e, H.delete_elt_exp exp exp_list, loc) ]
               else if check_sibling_exp context.left_sibling exp_list then
                 let prev_exp = get_sibling_exp context.left_sibling exp_list in
                 ChangeTo
                   [
                     Cil.Call
                       (lval, e, H.delete_before_elt_exp prev_exp exp_list, loc);
                   ]
               else if check_sibling_exp context.right_sibling exp_list then
                 let next_exp = get_sibling_exp context.right_sibling exp_list in
                 ChangeTo
                   [
                     Cil.Call
                       (lval, e, H.delete_after_elt_exp next_exp exp_list, loc);
                   ]
               else
                 failwith
                   "expInsertVisitorInstr: an expression cannot be inserted \
                    without any sibling info"
           | _ -> DoChildren
         else DoChildren
     end

   class expUpdateVisitorInstr context (from_exp : Cil.exp) (to_exp : Cil.exp) =
     object
       inherit Cil.nopCilVisitor

       method! vinst (i : Cil.instr) =
         if check_parent context.D.Diff.parent i then
           match i with
           | Cil.Call (lval, e, exp_list, loc) -> (
               match (e, from_exp) with
               | Cil.Lval (Cil.Var v1, _), Cil.Lval (Cil.Var v2, _) ->
                   if v1.vname = v2.vname then
                     ChangeTo [ Cil.Call (lval, to_exp, exp_list, loc) ]
                   else DoChildren
               | _ -> DoChildren)
           | Cil.Set (lval, e, loc) ->
               if H.string_of_exp from_exp = H.string_of_exp e then
                 ChangeTo [ Cil.Set (lval, to_exp, loc) ]
               else failwith "expUpdateVisitorInstr: rval is not matched"
           | _ -> DoChildren
         else DoChildren
     end *)
let insert_patch new_stmt patch_block before after =
  if before = None && after = None then new_stmt :: patch_block
  else if before = None then
    let after = Option.get after in
    List.fold_left
      (fun acc s ->
        if Utils.eq_stmt_line after.Cil.skind s.Cil.skind then
          s :: new_stmt :: acc
        else s :: acc)
      [] patch_block
    |> List.rev
  else
    let before = Option.get before in
    List.fold_left
      (fun acc s ->
        if Utils.eq_stmt_line before.Cil.skind s.Cil.skind then
          new_stmt :: s :: acc
        else s :: acc)
      [] patch_block
    |> List.rev

let rec iter_body stmts parent patch_bw patch =
  let before, after = patch_bw in
  List.fold_left
    (fun acc x ->
      match (x.Cil.skind, parent) with
      | Cil.Loop (b, loc, t1, t2), Cil.Loop (b', loc', _, _) ->
          if loc.Cil.line = loc'.Cil.line then
            let new_body = insert_patch patch b.bstmts before after in
            let new_block = { b with bstmts = new_body } in
            let new_stmt =
              { x with skind = Cil.Loop (new_block, loc, t1, t2) }
            in
            new_stmt :: acc
          else x :: acc
      | _ -> x :: acc)
    [] stmts
  |> List.rev

class stmtInsertVisitor target_func parent patch_bw stmt =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if f.svar.vname = target_func then
        let stmts = f.sbody.bstmts in
        let new_stmts = iter_body stmts parent patch_bw stmt in
        ChangeTo { f with sbody = { f.sbody with bstmts = new_stmts } }
      else DoChildren
  end

class stmtDeleteVisitor stmt =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      if check_stmt stmt b.bstmts then
        ChangeTo { b with bstmts = H.delete_elt_stmt stmt b.bstmts }
      else DoChildren
  end

let apply_action diff donee action =
  match (action, diff) with
  | EF.InsertStmt (ctx, stmt), SymDiff.SDiff.SInsertStmt (context, _) -> (
      let parent = ctx.EF.parent_node in
      let target_func = context.SymDiff.SDiff.func_name in
      match parent with
      | Fun g -> failwith "InsertStmt: not implemented"
      | Stmt s ->
          let patch_bw = ctx.EF.patch_between in
          let vis =
            new stmtInsertVisitor target_func s.Cil.skind patch_bw stmt
          in
          ignore (Cil.visitCilFile vis donee)
      | _ -> failwith "InsertStmt: Incorrect parent type")
  | DeleteStmt stmt, _ ->
      let vis = new stmtDeleteVisitor stmt in
      ignore (Cil.visitCilFile vis donee)
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
  | _ -> failwith "Not implemented"

let apply sym_diff donee edit_function =
  let donee_backup = donee in
  List.iter2
    (fun action diff -> apply_action diff donee action)
    edit_function sym_diff;
  if H.compare_files donee_backup donee then (true, donee) else (false, donee)
