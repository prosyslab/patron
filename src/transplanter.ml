module S = SymDiff
module D = Diff
module H = TransformerHelper

let check_parent parent instr =
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
        "check_parent: an expression cannot be inserted without the parent"

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

let check_sibling_stmt sibling stmt_list =
  match sibling with
  | D.CilElement.EStmt s ->
      List.exists (fun x -> H.eq_stmt x.Cil.skind s.skind) stmt_list
  | D.CilElement.Null -> false
  | _ -> failwith "check_sibling_stmt: sibling of a stmt must be a stmt"

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

class expInsertVisitorInstr context (exp : Cil.exp) =
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
  end

class stmtInsertVisitor context stmt =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      if check_sibling_stmt context.D.Diff.left_sibling b.bstmts then
        ChangeTo
          {
            b with
            bstmts =
              H.append_after_elt_stmt
                (get_sibling_stmt context.D.Diff.left_sibling b.bstmts)
                stmt b.bstmts;
          }
      else if check_sibling_stmt context.right_sibling b.bstmts then
        ChangeTo
          {
            b with
            bstmts =
              H.append_before_elt_stmt
                (get_sibling_stmt context.right_sibling b.bstmts)
                stmt b.bstmts;
          }
      else if check_snk context.snk b.bstmts then
        ChangeTo
          {
            b with
            bstmts =
              H.append_before_elt_stmt
                (get_snk context.snk b.bstmts)
                stmt b.bstmts;
          }
      else DoChildren
  end

class stmtDeleteVisitor context stmt =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      if check_stmt stmt b.bstmts then
        ChangeTo { b with bstmts = H.delete_elt_stmt stmt b.bstmts }
      else if check_sibling_stmt context.D.Diff.left_sibling b.bstmts then
        ChangeTo
          {
            b with
            bstmts =
              H.delete_after_elt_stmt
                (get_sibling_stmt context.D.Diff.left_sibling b.bstmts)
                b.bstmts;
          }
      else if check_sibling_stmt context.right_sibling b.bstmts then
        ChangeTo
          {
            b with
            bstmts =
              H.delete_before_elt_stmt
                (get_sibling_stmt context.right_sibling b.bstmts)
                b.bstmts;
          }
      else DoChildren
  end

let apply_action donee action =
  match action with
  | D.Diff.InsertStmt (context, stmt) ->
      let vis = new stmtInsertVisitor context stmt in
      ignore (Cil.visitCilFile vis donee)
  | DeleteStmt (context, stmt) ->
      let vis = new stmtDeleteVisitor context stmt in
      ignore (Cil.visitCilFile vis donee)
  | InsertExp (context, exp) ->
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
      ignore (Cil.visitCilFile vis donee)
  | _ -> failwith "Not implemented"

let apply donee edit_script =
  let donee_backup = donee in
  List.iter (fun action -> apply_action donee action) edit_script;
  if H.compare_files donee_backup donee then (true, donee) else (false, donee)
