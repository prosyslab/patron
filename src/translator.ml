module S = SymDiff
module D = Diff
module H = TransformerHelper

let match_const const =
  match const with
  | S.SElement.SIntConst i -> Cil.CInt64 (Int64.of_int i, Cil.IInt, None)
  | S.SElement.SCharConst c -> Cil.CChr c
  | S.SElement.SFloatConst f -> Cil.CReal (f, Cil.FFloat, None)
  | S.SElement.SStringConst s -> Cil.CStr s

let rec match_sym imap (emap : Cil.exp H.StrMap.t) (lmap : Cil.lval H.StrMap.t)
    (sym : S.SElement.t) =
  match sym with
  | SNull -> D.CilElement.Null
  | SStmt stmt ->
      let stmt = match_stmt imap emap lmap stmt in
      if stmt <> [] then D.CilElement.EStmt (List.hd stmt)
      else D.CilElement.Null
  | SExp exp ->
      let exp = match_exp lmap emap exp in
      if exp <> [] then D.CilElement.EExp (List.hd exp) else D.CilElement.Null
  | SLval lval ->
      let lval = match_lval lmap lval in
      if lval <> [] then D.CilElement.ELval (List.hd lval)
      else D.CilElement.Null

and match_lval (lmap : Cil.lval H.StrMap.t) (lval : S.SElement.sym_lval) =
  match lval with
  | LID (LvalID id) -> [ H.StrMap.find id lmap ]
  | _ -> failwith "match_lval: undefined behavior"

and match_exp lmap emap (exp : S.SElement.sym_exp) =
  match exp with
  | EID (ExpID id) -> [ H.StrMap.find id emap ]
  | SSizeOf (typ, id) -> (
      match id with
      | ExpID id ->
          let info = H.StrMap.find id emap in
          [ info ]
      | _ -> [ Cil.SizeOf (S.SElement.to_typ typ) ])
  | SSizeOfE (exp, id) -> (
      match id with
      | ExpID id ->
          let info = H.StrMap.find id emap in
          [ info ]
      | _ ->
          let e = match_exp lmap emap exp in
          if e <> [] then [ Cil.SizeOfE (List.hd e) ] else [])
  | SSizeOfStr (str, id) -> (
      match id with
      | ExpID id ->
          let info = H.StrMap.find id emap in
          [ info ]
      | _ -> [ Cil.SizeOfStr str ])
  | SBinOp (op, exp1, exp2, typ, id) -> (
      match id with
      | ExpID id ->
          let info = H.StrMap.find id emap in
          [ info ]
      | _ ->
          let e1 =
            let e = match_exp lmap emap exp1 in
            if e <> [] then List.hd e
            else failwith "match_exp: undefined behavior"
          in
          let e2 =
            let e = match_exp lmap emap exp2 in
            if e <> [] then List.hd e
            else failwith "match_exp: undefined behavior"
          in
          [ Cil.BinOp (S.SElement.to_binop op, e1, e2, S.SElement.to_typ typ) ])
  | SCastE (typ, exp, id) -> (
      match id with
      | ExpID id ->
          let info = H.StrMap.find id emap in
          [ info ]
      | _ ->
          let exp =
            let e = match_exp lmap emap exp in
            if e <> [] then List.hd e
            else failwith "match_exp: undefined behavior"
          in
          [ Cil.CastE (S.SElement.to_typ typ, exp) ])
  | SENULL -> []
  | SConst (const, id) -> (
      match id with
      | ExpID id ->
          let info = H.StrMap.find id emap in
          [ info ]
      | _ -> [ Cil.Const (match_const const) ])
  | SELval (lval, id) -> (
      match id with
      | ExpID id ->
          let info = H.StrMap.find id emap in
          [ info ]
      | _ -> (
          match lval with
          | LID (ExpID id) -> match_exp lmap emap (EID (ExpID id))
          | LID (LvalID _) ->
              let lval = match_lval lmap lval in
              if lval <> [] then [ Cil.Lval (List.hd lval) ] else []
          | _ -> failwith "match_exp: undefined behavior"))
  | _ -> failwith "match_exp: undefined behavior"

and match_stmt (imap : H.stmt_info_rev H.StrMap.t) emap lmap
    (stmt : S.SElement.sym_stmt) =
  match stmt with
  | SID (StmtID id) ->
      let info = H.StrMap.find id imap in
      [ info.stmt ]
  | SIf (cond, then_, else_, id) -> (
      match id with
      | StmtID id ->
          let info = H.StrMap.find id imap in
          [ info.stmt ]
      | _ ->
          let cond =
            let exp = match_exp lmap emap cond in
            if exp <> [] then List.hd exp
            else failwith "match_stmt: cond is null"
          in
          let then_ =
            List.flatten
              (List.rev
                 (List.fold_left
                    (fun acc s ->
                      let stmt = match_stmt imap emap lmap s in
                      if stmt <> [] then stmt :: acc else acc)
                    [] then_))
          in
          let else_ =
            List.flatten
              (List.rev
                 (List.fold_left
                    (fun acc s ->
                      let stmt = match_stmt imap emap lmap s in
                      if stmt <> [] then stmt :: acc else acc)
                    [] else_))
          in
          [
            Cil.mkStmt
              (If (cond, Cil.mkBlock then_, Cil.mkBlock else_, Cil.locUnknown));
          ])
  | SReturn (Some exp, id) -> (
      match id with
      | StmtID id ->
          let info = H.StrMap.find id imap in
          [ info.stmt ]
      | _ ->
          let value =
            let exp = match_exp lmap emap exp in
            if exp <> [] then List.hd exp
            else failwith "match_stmt: cond is null"
          in
          [ Cil.mkStmt (Return (Some value, Cil.locUnknown)) ])
  | SReturn (None, id) -> (
      match id with
      | StmtID id ->
          let info = H.StrMap.find id imap in
          [ info.stmt ]
      | _ -> [ Cil.mkStmt (Return (None, Cil.locUnknown)) ])
  | SSet (lval, exp, id) -> (
      match id with
      | StmtID id ->
          let info = H.StrMap.find id imap in
          [ info.stmt ]
      | _ ->
          let lval = match_lval lmap lval in
          let e =
            let exp = match_exp lmap emap exp in
            if exp <> [] then List.hd exp
            else failwith "match_stmt: cond is null"
          in
          let l =
            if lval <> [] then List.hd lval else failwith "match_stmt: lval"
          in
          [ Cil.mkStmt (Instr [ Set (l, e, Cil.locUnknown) ]) ])
  | SCall (None, exp, exps, id) -> (
      match id with
      | StmtID id ->
          let info = H.StrMap.find id imap in
          [ info.stmt ]
      | _ ->
          let e =
            let exp = match_exp lmap emap exp in
            if exp <> [] then List.hd exp
            else failwith "match_stmt: cond is null"
          in
          let mapped_exps = List.map (fun e -> match_exp lmap emap e) exps in
          let exps =
            if List.length mapped_exps <> List.length exps then
              failwith "match_stmt: cond is null"
            else List.map (fun e -> List.hd e) mapped_exps
          in
          [ Cil.mkStmt (Instr [ Call (None, e, exps, Cil.locUnknown) ]) ])
  | SCall (Some lv, exp, exps, id) -> (
      match id with
      | StmtID id ->
          let info = H.StrMap.find id imap in
          [ info.stmt ]
      | _ ->
          let lv = match_lval lmap lv in
          let l =
            if lv <> [] then List.hd lv else failwith "match_stmt: lval"
          in
          let e =
            let exp = match_exp lmap emap exp in
            if exp <> [] then List.hd exp
            else failwith "match_stmt: cond is null"
          in
          let mapped_exps = List.map (fun e -> match_exp lmap emap e) exps in
          let exps =
            if List.length mapped_exps <> List.length exps then
              failwith "match_stmt: cond is null"
            else List.map (fun e -> List.hd e) mapped_exps
          in
          [ Cil.mkStmt (Instr [ Call (Some l, e, exps, Cil.locUnknown) ]) ])
  | SSNull -> []
  | _ -> failwith "match_stmt: undefined behavior"

let match_context imap emap (lmap : Cil.lval H.StrMap.t)
    (context : S.SDiff.sym_context) =
  let parent = match_sym imap emap lmap context.s_parent in
  let left = match_sym imap emap lmap context.s_left_sibling in
  let right = match_sym imap emap lmap context.s_right_sibling in
  let snk = match_sym imap emap lmap context.s_snk in
  { D.Diff.parent; left_sibling = left; right_sibling = right; snk }

let translate_action imap emap (lmap : Cil.lval H.StrMap.t) (action : S.SDiff.t)
    =
  match action with
  | SInsertStmt (context, sym) ->
      let new_cont = match_context imap emap lmap context in
      let new_stmt =
        let stmt = match_stmt imap emap lmap sym in
        if stmt <> [] then List.hd stmt
        else failwith "translate_action: stmt is null"
      in
      D.Diff.InsertStmt (new_cont, new_stmt)
  | SDeleteStmt (context, sym) ->
      let new_cont = match_context imap emap lmap context in
      let new_stmt =
        let stmt = match_stmt imap emap lmap sym in
        if stmt <> [] then List.hd stmt
        else failwith "translate_action: stmt is null"
      in
      DeleteStmt (new_cont, new_stmt)
  | SInsertExp (context, sym) ->
      let new_cont = match_context imap emap lmap context in
      let new_exp =
        let exp = match_exp lmap emap sym in
        if exp <> [] then List.hd exp
        else failwith "translate_action: exp is null"
      in
      InsertExp (new_cont, new_exp)
  | SDeleteExp (context, sym) ->
      let new_cont = match_context imap emap lmap context in
      let new_exp =
        let exp = match_exp lmap emap sym in
        if exp <> [] then List.hd exp
        else failwith "translate_action: exp is null"
      in
      DeleteExp (new_cont, new_exp)
  | SUpdateExp (context, _from, _to) ->
      let new_cont = match_context imap emap lmap context in
      let new_from =
        let exp = match_exp lmap emap _from in
        if exp <> [] then List.hd exp
        else failwith "translate_action: exp is null"
      in
      let new_to =
        let exp = match_exp lmap emap _to in
        if exp <> [] then List.hd exp
        else
          match _to with
          | EID (IDNotAvailable str) ->
              Cil.Lval
                (Cil.Var (Cil.makeGlobalVar str Cil.intType), Cil.NoOffset)
          | _ -> failwith "translate_action: exp is null"
      in
      UpdateExp (new_cont, new_from, new_to)
  | SInsertLval (context, sym) ->
      let new_cont = match_context imap emap lmap context in
      let new_lval =
        let lval = match_lval lmap sym in
        if lval <> [] then List.hd lval
        else failwith "translate_action: lval is null"
      in
      InsertLval (new_cont, new_lval)
  | SDeleteLval (context, sym) ->
      let new_cont = match_context imap emap lmap context in
      let new_lval =
        let lval = match_lval lmap sym in
        if lval <> [] then List.hd lval
        else failwith "translate_action: lval is null"
      in
      DeleteLval (new_cont, new_lval)
  | SUpdateLval (context, _from, _to) ->
      let new_cont = match_context imap emap lmap context in
      let new_from =
        let lval = match_lval lmap _from in
        if lval <> [] then List.hd lval
        else failwith "translate_action: lval is null"
      in
      let new_to =
        let lval = match_lval lmap _to in
        if lval <> [] then List.hd lval
        else
          match _to with
          | LID (IDNotAvailable str) ->
              (Cil.Var (Cil.makeGlobalVar str Cil.intType), Cil.NoOffset)
          | _ -> failwith "translate_action: lval is null"
      in
      UpdateLval (new_cont, new_from, new_to)

let translate_diff imap emap (lmap : Cil.lval H.StrMap.t) diff =
  List.fold_left
    (fun acc action -> translate_action imap emap lmap action :: acc)
    [] diff

let remove_cast sparrow_path exp =
  let exp_map = Filename.concat sparrow_path "taint/datalog/Exp.map" in
  let exp_map = H.make_str_map_rev exp_map in
  let rec parse_exp exp =
    match exp with
    | Cil.Const const ->
        if H.StrMap.exists (fun k _ -> H.string_of_constant const = k) exp_map
        then
          let sub_exp_id = H.StrMap.find (H.string_of_constant const) exp_map in
          H.StrMap.add sub_exp_id exp H.StrMap.empty
        else H.StrMap.empty
    | Cil.Lval lval ->
        if H.StrMap.exists (fun k _ -> H.string_of_lval lval = k) exp_map then
          let sub_exp_id = H.StrMap.find (H.string_of_lval lval) exp_map in
          H.StrMap.add sub_exp_id exp H.StrMap.empty
        else H.StrMap.empty
    | Cil.CastE (_, sub_exp) -> parse_exp sub_exp
    | Cil.UnOp (_, sub_exp, _) -> parse_exp sub_exp
    | Cil.BinOp (_, sub_exp1, sub_exp2, _) ->
        H.StrMap.union
          (fun _ _ y -> Some y)
          (parse_exp sub_exp1) (parse_exp sub_exp2)
    | Cil.Question (sub_exp1, sub_exp2, sub_exp3, _) ->
        H.StrMap.union
          (fun _ _ y -> Some y)
          (H.StrMap.union
             (fun _ _ y -> Some y)
             (parse_exp sub_exp1) (parse_exp sub_exp2))
          (parse_exp sub_exp3)
    | _ -> H.StrMap.empty
  in
  parse_exp exp

let translate sparrow_path donee edit_function solution_path =
  let solution = H.make_str_map solution_path in
  let info_map = S.map_cil_to_cmd sparrow_path donee in
  let info_map_fliped =
    H.InfoMap.fold
      (fun k v acc ->
        H.StrMap.add v
          {
            H.stmt = k.stmt;
            exps = H.rev_expmap k.exps;
            lvals = H.rev_lvalmap k.lvals;
          }
          acc)
      info_map H.StrMap.empty
  in
  let emap =
    H.StrMap.fold
      (fun _ v acc ->
        H.StrMap.fold
          (fun a b ac ->
            H.StrMap.union
              (fun _ _ y -> Some y)
              (remove_cast sparrow_path b)
              (H.StrMap.add a b ac))
          v.H.exps acc)
      info_map_fliped H.StrMap.empty
  in
  let lmap =
    H.StrMap.fold
      (fun _ v acc ->
        H.StrMap.fold (fun a b ac -> H.StrMap.add a b ac) v.H.lvals acc)
      info_map_fliped H.StrMap.empty
  in
  let sym_diff = S.convert_diff solution edit_function in
  translate_diff info_map_fliped emap lmap sym_diff
