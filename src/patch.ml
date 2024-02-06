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
  | Ast.Exp e -> List.exists (fun x -> Ast.isom_exp x e) exp_list
  | _ ->
      failwith
        "check_sibling_exp: sibling of an expression must be an expression"

let check_stmt stmt stmt_list =
  List.exists (fun x -> Ast.isom_stmt x stmt) stmt_list

let check_exp exp exp_list = List.exists (fun x -> Ast.isom_exp x exp) exp_list

(* let check_parent_stmt parent node =
   match parent.Cil.skind with
   | Cil.Loop (b, _, _, _) -> H.eq_block b node
   | Cil.Block b -> H.eq_block b node
   | Cil.If (_, b1, b2, _) -> H.eq_block b1 node || H.eq_block b2 node
   | _ -> failwith "check_parent_stmt: parent is not a stmt" *)

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

let insert_patch new_stmt patch_block before after =
  if before = [] && after = [] then new_stmt :: patch_block
  else if before = [] then
    let after = List.hd after in
    List.fold_left
      (fun acc s ->
        if Utils.eq_stmt_line after.Cil.skind s.Cil.skind then
          s :: new_stmt :: acc
        else s :: acc)
      [] patch_block
    |> List.rev
  else
    let before = List.rev before |> List.hd in
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
      | Cil.Loop (b, loc, t1, t2), Cil.Loop (_, loc', _, _) ->
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
      if f.svar.vname = target_func then
        let stmts = f.sbody.bstmts in
        let new_stmts = iter_body stmts parent patch_bw stmt in
        ChangeTo { f with sbody = { f.sbody with bstmts = new_stmts } }
      else DoChildren
  end

class stmtInsertVisitorUnderFun target_func patch_bw stmt =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if f.svar.vname = target_func then
        let stmts = f.sbody.bstmts in
        let before, after = patch_bw in
        let new_stmts = insert_patch stmt stmts before after in
        ChangeTo { f with sbody = { f.sbody with bstmts = new_stmts } }
      else DoChildren
  end

class stmtDeleteVisitor stmt =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      if check_stmt stmt b.bstmts then
        ChangeTo { b with bstmts = delete_elt_stmt stmt b.bstmts }
      else DoChildren
  end

class expUpdateVisitor target_func parent from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if f.svar.vname = target_func then
        let stmts = f.sbody.bstmts in
        let new_stmts = replace_exp_in_stmts stmts parent from_exp to_exp in
        ChangeTo { f with sbody = { f.sbody with bstmts = new_stmts } }
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

let apply_action diff donee action =
  match (action, diff) with
  | D.InsertStmt (ctx, stmt), SymDiff.SInsertStmt (context, _) -> (
      let parent = List.hd ctx.D.root_path in
      let target_func = context.SymDiff.func_name in
      match parent with
      | Fun func_name ->
          let patch_bound = paths2stmts ctx.D.patch_bound in
          let vis = new stmtInsertVisitorUnderFun func_name patch_bound stmt in
          ignore (Cil.visitCilFile vis donee)
      | Stmt s ->
          let patch_bound = paths2stmts ctx.D.patch_bound in
          let vis =
            new stmtInsertVisitorUnderStmt
              target_func s.Cil.skind patch_bound stmt
          in
          ignore (Cil.visitCilFile vis donee)
      | _ -> failwith "InsertStmt: Incorrect parent type")
  | DeleteStmt (_, stmt), _ ->
      let vis = new stmtDeleteVisitor stmt in
      ignore (Cil.visitCilFile vis donee)
  | UpdateExp (ctx, from_exp, to_exp), SymDiff.SUpdateExp (context, _, _) -> (
      let parent = List.hd ctx.D.root_path in
      let target_func = context.SymDiff.func_name in
      match parent with
      | Fun _ -> failwith "UpdateExp: not implemented"
      | Stmt s ->
          let vis = new expUpdateVisitor target_func s from_exp to_exp in
          ignore (Cil.visitCilFile vis donee)
      | _ -> failwith "UpdateExp: Incorrect parent type")
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
  List.iter2
    (fun action diff -> apply_action diff donee action)
    edit_function sym_diff;
  donee
