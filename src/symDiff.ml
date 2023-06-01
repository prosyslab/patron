module J = Yojson.Basic.Util
module H = TransformerHelper
module D = Diff

module SElement = struct
  type sym_typ = SVoid | SInt | SFloat | SPtr of sym_typ

  type sym_binop =
    | SPlusA
    | SPlusPI
    | SIndexPI
    | SMinusA
    | SMinusPI
    | SMinusPP
    | SMod
    | SShiftlt
    | SShiftrt
    | SAnd
    | SXor
    | SOr
    | SMult
    | SDiv
    | SEq
    | SNe
    | SLt
    | SLe
    | SGt
    | SGe
    | SLAnd
    | SLOr

  type sym_const =
    | SIntConst of int
    | SFloatConst of float
    | SCharConst of char
    | SStringConst of string

  type sym_lval =
    | SLLIT of string * string
    | LOriginal of string
    | SLID of string
    | SLNULL

  type sym_exp =
    | SENULL
    | SELit of string * string (* (id , literal) *)
    | EOriginal of string
    | SEID of string
    | SConst of sym_const
    | SELval of sym_lval
    | SSizeOf of sym_typ
    | SSizeOfE of sym_exp
    | SSizeOfStr of string
    | SBinOp of sym_binop * sym_exp * sym_exp * sym_typ
    | SUnOp of string * sym_exp
    | SQuestion of sym_exp * sym_exp * sym_exp
    | SCastE of sym_typ * sym_exp

  type sym_stmt =
    | SSNull
    | SSID of string (* (id , literal) *)
    | SIf of sym_exp * sym_stmt list * sym_stmt list
    | SSet of sym_lval * sym_exp
    | SCall of sym_lval option * sym_exp * sym_exp list
    | SReturn of sym_exp option

  type t = SNull | SStmt of sym_stmt | SExp of sym_exp | SLval of sym_lval

  let to_null = SNull

  let rec to_typ t =
    match t with
    | SVoid -> Cil.TVoid []
    | SInt -> Cil.TInt (Cil.IInt, [])
    | SFloat -> Cil.TFloat (Cil.FDouble, [])
    | SPtr t -> Cil.TPtr (to_typ t, [])

  let to_sbinop op =
    match op with
    | Cil.PlusA -> SPlusA
    | Cil.PlusPI -> SPlusPI
    | Cil.IndexPI -> SIndexPI
    | Cil.MinusA -> SMinusA
    | Cil.MinusPI -> SMinusPI
    | Cil.MinusPP -> SMinusPP
    | Cil.Mod -> SMod
    | Cil.Shiftlt -> SShiftlt
    | Cil.Shiftrt -> SShiftrt
    | Cil.BAnd -> SAnd
    | Cil.BXor -> SXor
    | Cil.BOr -> SOr
    | Cil.Mult -> SMult
    | Cil.Div -> SDiv
    | Cil.Eq -> SEq
    | Cil.Ne -> SNe
    | Cil.Lt -> SLt
    | Cil.Le -> SLe
    | Cil.Gt -> SGt
    | Cil.Ge -> SGe
    | Cil.LAnd -> SLAnd
    | Cil.LOr -> SLOr

  let to_binop sop =
    match sop with
    | SPlusA -> Cil.PlusA
    | SPlusPI -> Cil.PlusPI
    | SIndexPI -> Cil.IndexPI
    | SMinusA -> Cil.MinusA
    | SMinusPI -> Cil.MinusPI
    | SMinusPP -> Cil.MinusPP
    | SMod -> Cil.Mod
    | SShiftlt -> Cil.Shiftlt
    | SShiftrt -> Cil.Shiftrt
    | SAnd -> Cil.BAnd
    | SXor -> Cil.BXor
    | SOr -> Cil.BOr
    | SMult -> Cil.Mult
    | SDiv -> Cil.Div
    | SEq -> Cil.Eq
    | SNe -> Cil.Ne
    | SLt -> Cil.Lt
    | SLe -> Cil.Le
    | SGt -> Cil.Gt
    | SGe -> Cil.Ge
    | SLAnd -> Cil.LAnd
    | SLOr -> Cil.LOr

  let to_sconst c =
    match c with
    | Cil.CInt64 (i, _, _) -> SIntConst (Int64.to_int i)
    | Cil.CReal (f, _, _) -> SFloatConst f
    | Cil.CChr c -> SCharConst c
    | Cil.CStr s -> SStringConst s
    | _ -> failwith "not supported"

  let compare = compare
end

module SDiff = struct
  type sym_context = {
    s_parent : SElement.t;
    s_left_sibling : SElement.t;
    s_right_sibling : SElement.t;
  }

  type t =
    | SInsertStmt of sym_context * SElement.sym_stmt
    | SDeleteStmt of sym_context * SElement.sym_stmt
    | SInsertExp of sym_context * SElement.sym_exp
    | SDeleteExp of sym_context * SElement.sym_exp
    | SUpdateExp of sym_context * SElement.sym_exp * SElement.sym_exp
    | SInsertLval of sym_context * SElement.sym_lval
    | SDeleteLval of sym_context * SElement.sym_lval
    | SUpdateLval of sym_context * SElement.sym_lval * SElement.sym_lval
end

let rec match_stmt (cmd : H.cmd) stmts =
  match stmts with
  | hd :: tl -> (
      match (hd.Cil.skind, cmd) with
      | Cil.Instr i, Cset (_, _, cloc) -> (
          let instr = List.hd i in
          match instr with
          | Cil.Set (_, _, loc) ->
              if loc.line = cloc.line then hd else match_stmt cmd tl
          | _ -> match_stmt cmd tl)
      | Cil.Instr i, Calloc (_, _, loc) -> (
          let instr = List.hd i in
          match instr with
          | Cil.Set (_, _, cloc) ->
              if loc.line = cloc.line then hd else match_stmt cmd tl
          | _ -> match_stmt cmd tl)
      | Cil.Instr i, Cfalloc (_, _, loc) -> (
          let instr = List.hd i in
          match instr with
          | Cil.Set (_, _, cloc) ->
              if loc.line = cloc.line then hd else match_stmt cmd tl
          | _ -> match_stmt cmd tl)
      | Cil.Instr i, Csalloc (_, _, loc) -> (
          let instr = List.hd i in
          match instr with
          | Cil.Set (_, _, cloc) ->
              if loc.line = cloc.line then hd else match_stmt cmd tl
          | _ -> match_stmt cmd tl)
      | Cil.Instr i, Ccall1 (_, _, _, loc) -> (
          let instr = List.hd i in
          match instr with
          | Cil.Call (_, _, _, cloc) ->
              if loc.line = cloc.line then hd else match_stmt cmd tl
          | _ -> match_stmt cmd tl)
      | Cil.Instr i, Ccall2 (_, _, loc) -> (
          let instr = List.hd i in
          match instr with
          | Cil.Call (_, _, _, cloc) ->
              if loc.line = cloc.line then hd else match_stmt cmd tl
          | _ -> match_stmt cmd tl)
      | Cil.Return (_, loc), Creturn1 (_, cloc)
      | Cil.Return (_, loc), Creturn2 cloc ->
          if loc.line = cloc.line then hd else match_stmt cmd tl
      | Cil.If (_, _, _, loc), Cassume (_, cloc) ->
          if loc.line = cloc.line then hd else match_stmt cmd tl
      | _ -> match_stmt cmd tl)
  | [] -> Cil.mkEmptyStmt ()

let match_exps stmt (cmd : H.cmd) =
  match (stmt.Cil.skind, cmd) with
  | Cil.Instr [], _ -> H.ExpMap.empty
  | Cil.Instr i, Cset (_, e, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Set (_, exp, _) -> H.ExpMap.add exp e H.ExpMap.empty
      | _ -> H.ExpMap.empty)
  | Cil.Instr i, Calloc (_, e, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Set (_, exp, _) -> H.ExpMap.add exp e H.ExpMap.empty
      | _ -> H.ExpMap.empty)
  | Cil.Instr i, Cfalloc _ -> (
      let instr = List.hd i in
      match instr with Cil.Set _ -> H.ExpMap.empty | _ -> H.ExpMap.empty)
  | Cil.Instr i, Csalloc _ -> (
      let instr = List.hd i in
      match instr with Cil.Set _ -> H.ExpMap.empty | _ -> H.ExpMap.empty)
  | Cil.Instr i, Ccall1 (_, e, p, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Call (_, exp, param, _) ->
          if List.length param <> List.length p then H.ExpMap.empty
          else
            H.ExpMap.union
              (fun _ v1 _ -> Some v1)
              (List.fold_left2
                 (fun acc p e -> H.ExpMap.add p e acc)
                 H.ExpMap.empty param p)
              (H.ExpMap.add exp e H.ExpMap.empty)
      | _ -> H.ExpMap.empty)
  | Cil.Instr i, Ccall2 (e, p, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Call (_, exp, param, _) ->
          H.ExpMap.union
            (fun _ v1 _ -> Some v1)
            (List.fold_left2
               (fun acc p e -> H.ExpMap.add p e acc)
               H.ExpMap.empty param p)
            (H.ExpMap.add exp e H.ExpMap.empty)
      | _ -> H.ExpMap.empty)
  | Cil.Return (Some e, _), Creturn1 (e', _) -> H.ExpMap.add e e' H.ExpMap.empty
  | Cil.If (e, _, _, _), Cassume (e', _) -> H.ExpMap.add e e' H.ExpMap.empty
  | _ -> H.ExpMap.empty

let match_lvs stmt (cmd : H.cmd) =
  match (stmt.Cil.skind, cmd) with
  | Cil.Instr [], _ -> H.LvalMap.empty
  | Cil.Instr i, Cset (lv, _, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Set (lval, _, _) -> H.LvalMap.add lval lv H.LvalMap.empty
      | _ -> H.LvalMap.empty)
  | Cil.Instr i, Calloc (lv, _, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Set (lval, _, _) -> H.LvalMap.add lval lv H.LvalMap.empty
      | _ -> H.LvalMap.empty)
  | Cil.Instr i, Cfalloc _ -> (
      let instr = List.hd i in
      match instr with Cil.Set _ -> H.LvalMap.empty | _ -> H.LvalMap.empty)
  | Cil.Instr i, Csalloc _ -> (
      let instr = List.hd i in
      match instr with Cil.Set _ -> H.LvalMap.empty | _ -> H.LvalMap.empty)
  | Cil.Instr i, Ccall1 (lv, _, _, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Call (Some lval, _, _, _) -> H.LvalMap.add lval lv H.LvalMap.empty
      | _ -> H.LvalMap.empty)
  | _ -> H.LvalMap.empty

let map_cil stmts cmd_map =
  H.CmdMap.fold
    (fun cmd id acc ->
      let stmt_matched = match_stmt cmd stmts in
      H.InfoMap.add
        {
          stmt = stmt_matched;
          exps = match_exps stmt_matched cmd;
          lvals = match_lvs stmt_matched cmd;
        }
        id acc)
    cmd_map H.InfoMap.empty

let parse_op op =
  match op with
  | "PlusA" -> SElement.SPlusA
  | "MinusA" -> SMinusA
  | "Mult" -> SMult
  | "Div" -> SDiv
  | "Mod" -> SMod
  | "Shiftlt" -> SShiftlt
  | "Shiftrt" -> SShiftrt
  | "Lt" -> SLt
  | "Gt" -> SGt
  | "Le" -> SLe
  | "Ge" -> SGe
  | "Eq" -> SEq
  | "Ne" -> SNe
  | "BAnd" -> SAnd
  | "BXor" -> SXor
  | "BOr" -> SOr
  | "LAnd" -> SLAnd
  | "LOr" -> SLOr
  | _ -> failwith "parse_op: undefined behavior"

let rec parse_typ typ =
  match typ with
  | `String s -> (
      match s with
      | "int" -> SElement.SInt
      | "float" -> SFloat
      | "void" -> SVoid
      | _ -> failwith "parse_typ: undefined behavior")
  | `Assoc [ ("ptr", `Assoc [ ("typ", t) ]) ] -> SPtr (parse_typ t)
  | _ -> failwith "parse_typ: undefined behavior"

let parse_lval_json lval =
  match lval with
  | `Assoc [ ("sym", c1); ("lit", c2) ] ->
      let sym = c1 |> J.to_string in
      let lit = c2 |> J.to_string in
      if String.contains sym '-' then SElement.SLLIT (sym, lit)
      else LOriginal sym
  | _ -> failwith "parse_lval_json: undefined behavior"

let parse_const_json const =
  match const with
  | `Assoc [ ("type", typ); ("lit", lit) ] -> (
      let t = J.to_string typ in
      let l = J.to_string lit in
      match t with
      | "int" -> SElement.SConst (SIntConst (int_of_string l))
      | "float" -> SConst (SFloatConst (float_of_string l))
      | "char" -> SConst (SCharConst (List.hd (H.explode l)))
      | "string" -> SConst (SStringConst l)
      | _ -> failwith "parse_const_json: undefined behavior")
  | _ -> failwith "parse_const_json: undefined behavior"

let rec parse_exp_json exp =
  match exp with
  | `Assoc [ ("sym", c1); ("lit", c2) ] ->
      let s = c1 |> J.to_string in
      let lit = c2 |> J.to_string in
      if String.contains s '-' then SElement.SELit (s, lit) else EOriginal s
  | `Assoc [ ("const", contents) ] -> parse_const_json contents
  | `Assoc [ ("binop", contents) ] ->
      let op = parse_op (contents |> J.member "op" |> J.to_string) in
      let typ = parse_typ (contents |> J.member "typ") in
      let e1 = parse_exp_json (contents |> J.member "e1") in
      let e2 = parse_exp_json (contents |> J.member "e2") in
      SBinOp (op, e1, e2, typ)
  | `Assoc [ ("cast", contents) ] ->
      let typ = parse_typ (contents |> J.member "typ") in
      let e = parse_exp_json (contents |> J.member "e") in
      SCastE (typ, e)
  | `Assoc [ ("sizeof", contents) ] ->
      let e = parse_exp_json contents in
      SSizeOfE e
  | `Assoc [ ("lval", contents) ] ->
      let lv = parse_lval_json contents in
      SELval lv
  | _ -> failwith "parse_exp_json: undefined behavior"

let parse_return_json stmt =
  match stmt with
  | `Assoc [ ("exp", exp) ] -> (
      match exp with
      | `String s ->
          if s = "None" then SElement.SReturn None
          else SReturn (Some (parse_exp_json exp))
      | `Assoc _ -> SReturn (Some (parse_exp_json exp))
      | _ -> failwith "parse_return_json: undefined behavior")
  | _ -> failwith "parse_return_json: undefined behavior"

let rec parse_if_json stmt =
  match stmt with
  | `Assoc [ ("cond", cond); ("then", then_block); ("else", else_block) ] ->
      let cond = parse_exp_json cond in
      let then_block =
        let tb_lst = J.to_list then_block in
        List.fold_left (fun acc s -> parse_stmt_json s :: acc) [] tb_lst
      in
      let else_block =
        let es_block = J.to_list else_block in
        List.fold_left (fun acc s -> parse_stmt_json s :: acc) [] es_block
      in
      SElement.SIf (cond, then_block, else_block)
  | _ -> failwith "parse_if_json: undefined behavior"

and parse_stmt_json sym =
  match sym with
  | `Assoc [ (stmt_name, stmt) ] -> (
      match stmt_name with
      | "if" -> parse_if_json stmt
      | "return" -> parse_return_json stmt
      | _ -> failwith "parse_stmt_json: not implemented")
  | _ -> failwith "parse_stmt_json: undefined behavior"

let parse_context action context =
  match action with
  | "insert_stmt" | "delete_stmt" ->
      let parent = J.member "parent" context in
      let parent_sym = J.member "sym" parent |> J.to_string in
      let s_parent =
        if parent_sym = "Null" then SElement.SNull else SStmt (SSID parent_sym)
      in
      let left = J.member "left" context in
      let left_sym = J.member "sym" left |> J.to_string in
      let s_left_sibling =
        if left_sym = "Null" then SElement.SNull else SStmt (SSID left_sym)
      in
      let right = J.member "right" context in
      let right_sym = J.member "sym" right |> J.to_string in
      let s_right_sibling =
        if right_sym = "Null" then SElement.SNull else SStmt (SSID right_sym)
      in
      { SDiff.s_parent; s_left_sibling; s_right_sibling }
  | "insert_exp" | "delete_exp" | "update_exp" | "insert_lval" | "delete_lval"
  | "update_lval" ->
      let parent = J.member "parent" context in
      let parent_sym = J.member "sym" parent |> J.to_string in
      let s_parent =
        if parent_sym = "Null" then SElement.SNull
        else SElement.SStmt (SSID parent_sym)
      in
      let left = J.member "left" context in
      let left_sym = J.member "sym" left |> J.to_string in
      let s_left_sibling =
        if left_sym = "Null" then SElement.SNull
        else SElement.SExp (SEID left_sym)
      in
      let right = J.member "right" context in
      let right_sym = J.member "sym" right |> J.to_string in
      let s_right_sibling =
        if right_sym = "Null" then SElement.SNull
        else SElement.SExp (SEID right_sym)
      in
      { s_parent; s_left_sibling; s_right_sibling }
  | _ -> failwith "parse_sym_json: undefined behavior"

let parse_sym_json action context sym =
  let context = parse_context action context in
  match action with
  | "insert_stmt" -> SDiff.SInsertStmt (context, parse_stmt_json sym)
  | "delete_stmt" -> SDiff.SDeleteStmt (context, parse_stmt_json sym)
  | "insert_exp" -> SDiff.SInsertExp (context, parse_exp_json sym)
  | "delete_exp" -> SDiff.SDeleteExp (context, parse_exp_json sym)
  | "update_exp" -> (
      match sym with
      | `Assoc [ ("from", _from); ("to", _to) ] ->
          let _from = parse_exp_json _from in
          let _to = parse_exp_json _to in
          SUpdateExp (context, _from, _to)
      | `Assoc _ -> failwith "undefined action"
      | _ -> failwith "undefined action")
  | "insert_lval" -> SDiff.SInsertLval (context, parse_lval_json sym)
  | "delete_lval" -> SDiff.SDeleteLval (context, parse_lval_json sym)
  | "update_lval" -> (
      match sym with
      | `Assoc [ ("from", _from); ("to", _to) ] ->
          let _from = parse_lval_json _from in
          let _to = parse_lval_json _to in
          SUpdateLval (context, _from, _to)
      | `Assoc _ -> failwith "undefined action"
      | _ -> failwith "undefined action")
  | _ -> failwith "undefined action"

let parse_edit_function path_name =
  let json = Yojson.Basic.from_file path_name in
  let diffs = json |> J.member "diffs" in
  let key_list = diffs |> J.keys in
  let diffs =
    List.rev
      (List.fold_left
         (fun acc key ->
           let v = J.member key diffs in
           v :: acc)
         [] key_list)
  in
  List.rev
    (List.fold_left
       (fun acc diff ->
         let action = diff |> J.member "action" |> J.to_string in
         let context = diff |> J.member "context" in
         let sym = diff |> J.member "change" in
         parse_sym_json action context sym :: acc)
       [] diffs)

let match_lval sol lv =
  match lv with
  | SElement.SLLIT (sym, lit) -> (
      let opt = H.StrMap.find_opt sym sol in
      match opt with
      | Some new_id -> SElement.SLID new_id
      | None -> LOriginal lit)
  | SLID id -> (
      let opt = H.StrMap.find_opt id sol in
      match opt with Some id -> SLID id | None -> SLNULL)
  | LOriginal str -> LOriginal str
  | SLNULL -> SLNULL

let rec match_exp sol exp =
  match exp with
  | SElement.SELit (sym, lit) -> (
      let opt = H.StrMap.find_opt sym sol in
      match opt with
      | Some new_id -> SElement.SEID new_id
      | None -> EOriginal lit)
  | EOriginal c -> EOriginal c
  | SEID id -> (
      let opt = H.StrMap.find_opt id sol in
      match opt with Some new_id -> SEID new_id | _ -> SENULL)
  | SConst c -> SConst c
  | SSizeOf t -> SSizeOf t
  | SSizeOfE e -> SSizeOfE (match_exp sol e)
  | SSizeOfStr s -> SSizeOfStr s
  | SBinOp (b, e1, e2, t) -> SBinOp (b, match_exp sol e1, match_exp sol e2, t)
  | SUnOp (u, e) -> SUnOp (u, match_exp sol e)
  | SQuestion (e1, e2, e3) ->
      SQuestion (match_exp sol e1, match_exp sol e2, match_exp sol e3)
  | SCastE (t, e) -> SCastE (t, match_exp sol e)
  | SELval lv -> SELval (match_lval sol lv)
  | _ -> failwith "match_exp: undefined behavior"

let rec match_stmt sol stmt =
  match stmt with
  | SElement.SSID id -> (
      let opt = H.StrMap.find_opt id sol in
      match opt with Some new_id -> SElement.SSID new_id | _ -> SSNull)
  | SIf (cond, then_block, else_block) ->
      let new_cond = match_exp sol cond in
      let new_then_block = List.map (match_stmt sol) then_block in
      let new_else_block = List.map (match_stmt sol) else_block in
      SIf (new_cond, new_then_block, new_else_block)
  | SReturn (Some exp) -> SReturn (Some (match_exp sol exp))
  | SReturn None -> SReturn None
  | SSNull -> SSNull
  | SSet (lv, exp) -> SSet (match_lval sol lv, match_exp sol exp)
  | SCall (None, func, param) ->
      SCall (None, match_exp sol func, List.map (match_exp sol) param)
  | SCall (Some lv, func, param) ->
      SCall
        ( Some (match_lval sol lv),
          match_exp sol func,
          List.map (match_exp sol) param )

let match_selem sol (selem : SElement.t) =
  match selem with
  | SElement.SNull -> SElement.SNull
  | SStmt stmt -> SStmt (match_stmt sol stmt)
  | SExp exp -> SExp (match_exp sol exp)
  | SLval _ -> failwith "not implemented"

(* delete this *)
let print_setype (exp : SElement.sym_exp) =
  match exp with
  | SELit _ -> "SLiteral"
  | SENULL -> "SENULL"
  | EOriginal _ -> "EOriginal"
  | SEID _ -> "SEID"
  | SConst _ -> "SConst"
  | SSizeOf _ -> "SSizeOf"
  | SSizeOfE _ -> "SSizeOfE"
  | SSizeOfStr _ -> "SSizeOfStr"
  | SBinOp _ -> "SBinOp"
  | SUnOp _ -> "SUnOp"
  | SQuestion _ -> "SQuestion"
  | SCastE _ -> "SCastE"
  | _ -> failwith "print_setype: undefined behavior"

let match_sym sol (action : SDiff.t) =
  match action with
  | SInsertStmt (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_stmt sol sym in
      SDiff.SInsertStmt ({ s_parent; s_left_sibling; s_right_sibling }, sym)
  | SDeleteStmt (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_stmt sol sym in
      SDeleteStmt ({ s_parent; s_left_sibling; s_right_sibling }, sym)
  | SInsertExp (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_exp sol sym in
      SInsertExp ({ s_parent; s_left_sibling; s_right_sibling }, sym)
  | SDeleteExp (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_exp sol sym in
      SDeleteExp ({ s_parent; s_left_sibling; s_right_sibling }, sym)
  | SUpdateExp (context, from, to_) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let from = match_exp sol from in
      let to_ = match_exp sol to_ in
      SUpdateExp ({ s_parent; s_left_sibling; s_right_sibling }, from, to_)
  | _ -> failwith "not implemented"

let convert_diff sol ef =
  List.rev
    (List.fold_left (fun acc action -> match_sym sol action :: acc) [] ef)

let map_cil_to_cmd sparrow_dir file =
  let cmd_str_map = H.parse_sparrow sparrow_dir in
  let stmts = H.extract_stmt_lst file in
  map_cil stmts cmd_str_map

let rec cil_to_sym_typ typ =
  match typ with
  | Cil.TVoid _ -> SElement.SVoid
  | Cil.TInt _ -> SElement.SInt
  | Cil.TFloat _ -> SElement.SFloat
  | Cil.TPtr (t, _) -> SElement.SPtr (cil_to_sym_typ t)
  | _ -> failwith "cil_to_sym_typ: undefined type"

let get_lval_sym stmt lval cil_map =
  let info_key = H.get_info_key stmt cil_map in
  if
    H.LvalMap.exists
      (fun k _ -> H.string_of_lval k = H.string_of_lval lval)
      info_key.H.lvals
  then
    let result =
      H.LvalMap.fold
        (fun k v acc ->
          if H.string_of_lval k = H.string_of_lval lval then v :: acc else acc)
        info_key.H.lvals []
    in
    match List.rev result with
    | hd :: _ -> SElement.SLID hd
    | [] -> failwith "get_exp_sym: not found"
  else failwith "get_exp_sym: not found"

let find_lval_sym lval lval_map_lst =
  let rec find_lval_sym' lval map_lst =
    match map_lst with
    | [] -> SElement.LOriginal (H.string_of_lval lval)
    | hd :: tl ->
        if
          H.LvalMap.exists
            (fun k _ -> H.string_of_lval k = H.string_of_lval lval)
            hd
        then
          let result =
            H.LvalMap.fold
              (fun k v acc ->
                if H.string_of_lval k = H.string_of_lval lval then v :: acc
                else acc)
              hd []
          in
          match List.rev result with
          | hd :: _ -> SElement.SLID hd
          | [] -> failwith "get_exp_sym: not found"
        else find_lval_sym' lval tl
  in
  find_lval_sym' lval lval_map_lst

let make_lval_map_lst cil_map =
  H.InfoMap.fold (fun k _ acc -> k.lvals :: acc) cil_map []

let make_exp_sym exp cil_map =
  let exp_map_lst = H.InfoMap.fold (fun k _ acc -> k.exps :: acc) cil_map [] in
  let lval_map_lst =
    H.InfoMap.fold (fun k _ acc -> k.lvals :: acc) cil_map []
  in
  let rec find_exp_sym (exp : Cil.exp) map_lst =
    match map_lst with
    | [] -> (
        match exp with
        | Cil.SizeOfE e -> SElement.SSizeOfE (find_exp_sym e exp_map_lst)
        | Cil.CastE (typ, e) ->
            SElement.SCastE (cil_to_sym_typ typ, find_exp_sym e exp_map_lst)
        | Cil.BinOp (op, e1, e2, typ) ->
            SElement.SBinOp
              ( SElement.to_sbinop op,
                find_exp_sym e1 exp_map_lst,
                find_exp_sym e2 exp_map_lst,
                cil_to_sym_typ typ )
        | Cil.Lval lval -> SElement.SELval (find_lval_sym lval lval_map_lst)
        | Cil.Const c -> SElement.SConst (SElement.to_sconst c)
        | _ ->
            H.print_ekind exp;
            failwith "find_exp_sym: undefined expression")
    | hd :: tl -> (
        let result =
          H.ExpMap.fold
            (fun k v acc ->
              if H.string_of_exp k = H.string_of_exp exp then v :: acc else acc)
            hd []
        in
        match List.rev result with
        | hd :: _ -> SEID hd
        | [] -> find_exp_sym exp tl)
  in
  find_exp_sym exp exp_map_lst

let get_exp_sym stmt exp cil_map =
  let info_key = H.get_info_key stmt cil_map in
  if
    H.ExpMap.exists
      (fun k _ -> H.string_of_exp k = H.string_of_exp exp)
      info_key.H.exps
  then
    let result =
      H.ExpMap.fold
        (fun k v acc ->
          if H.string_of_exp k = H.string_of_exp exp then v :: acc else acc)
        info_key.H.exps []
    in
    match List.rev result with
    | hd :: _ -> SElement.SEID hd
    | [] -> failwith "get_exp_sym: not found"
  else make_exp_sym exp cil_map

let get_main_sym (stmt : Cil.stmt) (cil_map : string H.InfoMap.t) =
  let result =
    H.InfoMap.fold
      (fun info v acc ->
        match (info.stmt.skind, stmt.skind) with
        | Cil.Instr [], _ | _, Cil.Instr [] -> acc
        | Cil.Instr i1, Cil.Instr i2 -> (
            match (List.hd i1, List.hd i2) with
            | ( Cil.Call (_, Cil.Lval (Cil.Var v1, _), _, loc1),
                Cil.Call (_, Cil.Lval (Cil.Var v2, _), _, loc2) ) ->
                if v1.vname = v2.vname && loc1 = loc2 then v :: acc else acc
            | ( Cil.Set ((Cil.Var v1, _), _, loc1),
                Cil.Set ((Cil.Var v2, _), _, loc2) ) ->
                if v1.vname = v2.vname && loc1 = loc2 then v :: acc else acc
            | _ -> acc)
        | Cil.If (_, _, _, loc1), Cil.If (_, _, _, loc2) ->
            if loc1 = loc2 then v :: acc else acc
        | Cil.Return (_, loc1), Cil.Return (_, loc2) ->
            if loc1 = loc2 then v :: acc else acc
        | _ -> acc)
      cil_map []
  in
  match List.rev result with [] -> None | hd :: _ -> Some hd

let make_sym_context context cil_map =
  let parent_sym =
    match context.D.Diff.parent with
    | Null | EGlobal _ -> SElement.to_null
    | EStmt stmt -> (
        let sym = get_main_sym stmt cil_map in
        match sym with None -> SNull | Some s -> SStmt (SSID s))
    | _ -> failwith "make_sym_context: unexpected parent"
  in
  let left_sibling_sym =
    match context.left_sibling with
    | Null | EGlobal _ -> SElement.to_null
    | EStmt stmt -> (
        let sym = get_main_sym stmt cil_map in
        match sym with None -> SNull | Some s -> SStmt (SSID s))
    | EExp exp ->
        SExp
          (get_exp_sym (D.CilElement.elem_to_stmt context.parent) exp cil_map)
    | _ -> failwith "make_sym_context: unexpected left sibling"
  in
  let right_sibling_sym =
    match context.right_sibling with
    | Null | EGlobal _ -> SElement.to_null
    | EStmt stmt -> (
        let sym = get_main_sym stmt cil_map in
        match sym with None -> SNull | Some s -> SStmt (SSID s))
    | EExp exp ->
        SExp
          (get_exp_sym (D.CilElement.elem_to_stmt context.parent) exp cil_map)
    | _ -> failwith "make_sym_context: unexpected right sibling"
  in
  {
    SDiff.s_parent = parent_sym;
    s_left_sibling = left_sibling_sym;
    s_right_sibling = right_sibling_sym;
  }

let rec make_main_sym stmt cil_map =
  match stmt.Cil.skind with
  | Cil.Instr i -> (
      match List.hd i with
      | Cil.Call (None, f, exps, _) ->
          SElement.SCall
            ( None,
              make_exp_sym f cil_map,
              List.fold_left
                (fun acc exp -> make_exp_sym exp cil_map :: acc)
                [] exps )
      | Cil.Call (Some lv, f, exps, _) ->
          SElement.SCall
            ( Some (find_lval_sym lv (make_lval_map_lst cil_map)),
              make_exp_sym f cil_map,
              List.fold_left
                (fun acc exp -> make_exp_sym exp cil_map :: acc)
                [] exps )
      | Cil.Set (lv, exp, _) ->
          SElement.SSet
            ( find_lval_sym lv (make_lval_map_lst cil_map),
              make_exp_sym exp cil_map )
      | _ -> failwith "make_main_sym: undefined instruction")
  | Cil.If (cond, t_b, e_b, _) ->
      let cond_sym = make_exp_sym cond cil_map in
      let t_stmts = t_b.bstmts in
      let e_stmts = e_b.bstmts in
      let t_syms = List.map (fun stmt -> make_main_sym stmt cil_map) t_stmts in
      let e_syms = List.map (fun stmt -> make_main_sym stmt cil_map) e_stmts in
      SElement.SIf (cond_sym, t_syms, e_syms)
  | Cil.Return (Some exp, _) ->
      SElement.SReturn (Some (make_exp_sym exp cil_map))
  | Cil.Return (None, _) -> SElement.SReturn None
  | _ -> failwith "make_main_sym: undefined statement"

let make_sym_stmt_node stmt cil_map =
  match stmt.Cil.skind with
  | Cil.If (cond, t_b, e_b, _) ->
      let cond_sym = make_exp_sym cond cil_map in
      let t_stmts = t_b.bstmts in
      let e_stmts = e_b.bstmts in
      let t_syms = List.map (fun stmt -> make_main_sym stmt cil_map) t_stmts in
      let e_syms = List.map (fun stmt -> make_main_sym stmt cil_map) e_stmts in
      SElement.SIf (cond_sym, t_syms, e_syms)
  | _ -> failwith "make_sym_stmt_node: undefined statement"

let rec fold_diff cil_map ast_diff acc =
  match ast_diff with
  | [] -> acc
  | hd :: tl -> (
      match hd with
      | D.Diff.InsertStmt (context, stmt) ->
          SDiff.SInsertStmt
            (make_sym_context context cil_map, make_sym_stmt_node stmt cil_map)
          :: fold_diff cil_map tl acc
      | DeleteStmt (context, stmt) ->
          SDiff.SDeleteStmt
            ( make_sym_context context cil_map,
              let sym = get_main_sym stmt cil_map in
              match sym with None -> SSNull | Some s -> SSID s )
          :: fold_diff cil_map tl acc
      | InsertExp (context, exp) ->
          SDiff.SInsertExp
            ( make_sym_context context cil_map,
              get_exp_sym (D.CilElement.elem_to_stmt context.parent) exp cil_map
            )
          :: fold_diff cil_map tl acc
      | DeleteExp (context, exp) ->
          SDiff.SDeleteExp
            ( make_sym_context context cil_map,
              get_exp_sym (D.CilElement.elem_to_stmt context.parent) exp cil_map
            )
          :: fold_diff cil_map tl acc
      | UpdateExp (context, _from, _to) ->
          SDiff.SUpdateExp
            ( make_sym_context context cil_map,
              get_exp_sym
                (D.CilElement.elem_to_stmt context.parent)
                _from cil_map,
              SElement.EOriginal (H.string_of_exp _to) )
          :: fold_diff cil_map tl acc
      | InsertLval (context, lval) ->
          SDiff.SInsertLval
            ( make_sym_context context cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                lval cil_map )
          :: fold_diff cil_map tl acc
      | DeleteLval (context, lval) ->
          SDiff.SDeleteLval
            ( make_sym_context context cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                lval cil_map )
          :: fold_diff cil_map tl acc
      | UpdateLval (context, _from, _to) ->
          SDiff.SUpdateLval
            ( make_sym_context context cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                _from cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                _to cil_map )
          :: fold_diff cil_map tl acc
      | _ -> fold_diff cil_map tl acc)

let define_sym_diff cil_map ast_diff = fold_diff cil_map ast_diff []

let slval_to_sym (slval : SElement.sym_lval) =
  match slval with SLID id -> id | _ -> "Null"

let sbinop_to_sym (op : SElement.sym_binop) =
  match op with
  | SPlusA -> "PlusA"
  | SMinusA -> "MinusA"
  | SMult -> "Mult"
  | SDiv -> "Div"
  | SMod -> "Mod"
  | SLt -> "Lt"
  | SGt -> "Gt"
  | SLe -> "Le"
  | SGe -> "Ge"
  | SEq -> "Eq"
  | SNe -> "Ne"
  | SAnd -> "BAnd"
  | SXor -> "BXor"
  | SOr -> "BOr"
  | SLAnd -> "LAnd"
  | SLOr -> "LOr"
  | SShiftlt -> "Shiftlt"
  | SShiftrt -> "Shiftrt"
  | SPlusPI -> "PlusPI"
  | SIndexPI -> "IndexPI"
  | SMinusPI -> "MinusPI"
  | SMinusPP -> "MinusPP"

let rec styp_to_sym (styp : SElement.sym_typ) =
  match styp with
  | SVoid -> "void"
  | SInt -> "int"
  | SFloat -> "float"
  | SPtr t -> "ptr" ^ styp_to_sym t

let sexp_to_sym (sexp : SElement.sym_exp) =
  match sexp with SEID str -> str | _ -> "Null"

let slval_to_json (slval : SElement.sym_lval) diff =
  match (slval, diff) with
  | SLID id, _ ->
      `Assoc [ ("sym", `String id); ("lit", `String (H.string_of_lval diff)) ]
  | LOriginal str, _ -> `Assoc [ ("sym", `String "Null"); ("lit", `String str) ]
  | SLNULL, _ -> `Assoc [ ("sym", `String "Null"); ("lit", `String "Null") ]
  | _ -> failwith "slval_to_json: undefined slval"

let sconst_to_json (sconst : SElement.sym_const) diff =
  match (sconst, diff) with
  | SIntConst i, _ ->
      `Assoc [ ("type", `String "int"); ("lit", `String (Int.to_string i)) ]
  | SFloatConst f, _ ->
      `Assoc [ ("type", `String "float"); ("lit", `String (Float.to_string f)) ]
  | SStringConst s, _ -> `Assoc [ ("type", `String "str"); ("lit", `String s) ]
  | SCharConst c, _ ->
      `Assoc [ ("type", `String "char"); ("lit", `String (String.make 1 c)) ]

let rec sexp_to_json (sexp : SElement.sym_exp) diff =
  match (sexp, diff) with
  | EOriginal str, _ -> `Assoc [ ("sym", `String "Null"); ("lit", `String str) ]
  | SEID id, _ ->
      `Assoc [ ("sym", `String id); ("lit", `String (H.string_of_exp diff)) ]
  | SConst const, _ -> `Assoc [ ("const", sconst_to_json const diff) ]
  | SELval lv1, Cil.Lval lv2 -> `Assoc [ ("lval", slval_to_json lv1 lv2) ]
  | SSizeOfE e1, Cil.SizeOfE e2 -> `Assoc [ ("sizeof", sexp_to_json e1 e2) ]
  | SBinOp (op1, e1_1, e2_1, typ1), Cil.BinOp (_, e1_2, e2_2, _) ->
      `Assoc
        [
          ( "binop",
            `Assoc
              [
                ("op", `String (sbinop_to_sym op1));
                ("typ", `String (styp_to_sym typ1));
                ("e1", sexp_to_json e1_1 e1_2);
                ("e2", sexp_to_json e2_1 e2_2);
              ] );
        ]
  | SCastE (typ, e1), Cil.CastE (_, e2) ->
      `Assoc
        [
          ( "cast",
            `Assoc
              [ ("typ", `String (styp_to_sym typ)); ("e", sexp_to_json e1 e2) ]
          );
        ]
  | _ -> failwith "sexp_to_json: undefined sexp"

let rec sstmt_to_json (sstmt : SElement.sym_stmt) diff =
  match (sstmt, diff.Cil.skind) with
  | SSID ssid, _ ->
      `Assoc [ ("sym", `String ssid); ("lit", `String (H.string_of_stmt diff)) ]
  | SIf (exp1, tb1, eb1), Cil.If (exp2, tb2, eb2, _) ->
      `Assoc
        [
          ( "if",
            `Assoc
              [
                ("cond", sexp_to_json exp1 exp2);
                ( "then",
                  `List
                    (List.rev
                       (List.fold_left2
                          (fun acc x y -> sstmt_to_json x y :: acc)
                          [] tb1 tb2.bstmts)) );
                ( "else",
                  `List
                    (List.rev
                       (List.fold_left2
                          (fun acc x y -> sstmt_to_json x y :: acc)
                          [] eb1 eb2.bstmts)) );
              ] );
        ]
  | SSet (lv1, e1), Cil.Instr [ Cil.Set (lv2, e2, _) ] ->
      `Assoc
        [
          ("set", `Assoc [ ("lval", slval_to_json lv1 lv2) ]);
          ("exp", sexp_to_json e1 e2);
        ]
  | SCall (Some lv1, e1, es1), Cil.Instr [ Cil.Call (Some lv2, e2, es2, _) ] ->
      `Assoc
        [
          ("call", `Assoc [ ("lval", slval_to_json lv1 lv2) ]);
          ("exp", sexp_to_json e1 e2);
          ( "exps",
            `List
              (List.rev
                 (List.fold_left2
                    (fun acc x y -> sexp_to_json x y :: acc)
                    [] es1 es2)) );
        ]
  | SCall (None, e1, es1), Cil.Instr [ Cil.Call (None, e2, es2, _) ] ->
      `Assoc
        [
          ("call", `Assoc [ ("lval", `String "None") ]);
          ("exp", sexp_to_json e1 e2);
          ( "exps",
            `List
              (List.rev
                 (List.fold_left2
                    (fun acc x y -> sexp_to_json x y :: acc)
                    [] es1 es2)) );
        ]
  | SReturn (Some e1), Cil.Return (Some e2, _) ->
      `Assoc [ ("return", `Assoc [ ("exp", sexp_to_json e1 e2) ]) ]
  | SReturn None, Cil.Return (None, _) -> `Assoc [ ("return", `String "") ]
  | _ -> failwith "sstmt_to_json: undefined sstmt"

let sstmt_to_sym (sstmt : SElement.sym_stmt) =
  match sstmt with SSID ssid -> ssid | _ -> "Null"

let sym_to_lit sym =
  match sym with
  | SElement.SStmt sstmt -> sstmt_to_sym sstmt
  | SElement.SExp sexp -> sexp_to_sym sexp
  | SElement.SLval slval -> slval_to_sym slval
  | SElement.SNull -> "Null"

let get_json_obj (saction : SDiff.t) (caction : D.Diff.t) =
  let context_json (context1 : SDiff.sym_context) (context2 : D.Diff.context) =
    ( "context",
      `Assoc
        [
          ( "parent",
            `Assoc
              [
                ("sym", `String (sym_to_lit context1.s_parent));
                ("lit", `String (D.CilElement.string_of_element context2.parent));
              ] );
          ( "left",
            `Assoc
              [
                ("sym", `String (sym_to_lit context1.s_left_sibling));
                ( "lit",
                  `String (D.CilElement.string_of_element context2.left_sibling)
                );
              ] );
          ( "right",
            `Assoc
              [
                ("sym", `String (sym_to_lit context1.s_right_sibling));
                ( "lit",
                  `String
                    (D.CilElement.string_of_element context2.right_sibling) );
              ] );
        ] )
  in
  match (saction, caction) with
  | SInsertStmt (context1, sym), InsertStmt (context2, diff) ->
      `Assoc
        [
          ("action", `String "insert_stmt");
          context_json context1 context2;
          ("change", sstmt_to_json sym diff);
        ]
  | SDeleteStmt (context1, sym), DeleteStmt (context2, _) ->
      `Assoc
        [
          ("action", `String "delete_stmt");
          context_json context1 context2;
          ("change", `String (sstmt_to_sym sym));
        ]
  | SInsertExp (context1, sym), InsertExp (context2, diff) ->
      `Assoc
        [
          ("action", `String "insert_exp");
          context_json context1 context2;
          ("change", sexp_to_json sym diff);
        ]
  | SDeleteExp (context1, sym), DeleteExp (context2, diff) ->
      `Assoc
        [
          ("action", `String "delete_exp");
          context_json context1 context2;
          ( "change",
            `Assoc
              [
                ("sym", `String (sexp_to_sym sym));
                ("lit", `String (H.string_of_exp diff));
              ] );
        ]
  | SUpdateExp (context1, from1, to1), UpdateExp (context2, from2, to2) ->
      `Assoc
        [
          ("action", `String "update_exp");
          context_json context1 context2;
          ( "change",
            `Assoc
              [
                ( "from",
                  `Assoc
                    [
                      ("sym", `String (sexp_to_sym from1));
                      ("lit", `String (H.string_of_exp from2));
                    ] );
                ( "to",
                  `Assoc
                    [
                      ("sym", `String (sexp_to_sym to1));
                      ("lit", `String (H.string_of_exp to2));
                    ] );
              ] );
        ]
  | SInsertLval (context1, sym), InsertLval (context2, diff) ->
      `Assoc
        [
          ("action", `String "insert_lval");
          context_json context1 context2;
          ( "change",
            `Assoc
              [
                ("sym", `String (slval_to_sym sym));
                ("lit", `String (H.string_of_lval diff));
              ] );
        ]
  | SDeleteLval (context1, sym), DeleteLval (context2, diff) ->
      `Assoc
        [
          ("action", `String "delete_lval");
          context_json context1 context2;
          ( "change",
            `Assoc
              [
                ("sym", `String (slval_to_sym sym));
                ("lit", `String (H.string_of_lval diff));
              ] );
        ]
  | SUpdateLval (context1, from1, to1), UpdateLval (context2, from2, to2) ->
      `Assoc
        [
          ("action", `String "update_lval");
          context_json context1 context2;
          ( "sym",
            `Assoc
              [
                ( "from",
                  `Assoc
                    [
                      ("sym", `String (slval_to_sym from1));
                      ("lit", `String (H.string_of_lval from2));
                    ] );
                ( "to",
                  `Assoc
                    [
                      ("sym", `String (slval_to_sym to1));
                      ("lit", `String (H.string_of_lval to2));
                    ] );
              ] );
        ]
  | _ -> `Null

let to_json sym_list conc_list out_dir =
  let oc_diff_json = open_out (out_dir ^ "/diff.json") in
  let rec make_json (id : int) sym_list conc_list acc =
    match (sym_list, conc_list) with
    | [], [] -> acc
    | s_action :: s_rest, c_action :: c_rest ->
        let json_obj = get_json_obj s_action c_action in
        if json_obj = `Null then make_json id sym_list c_rest acc
        else
          let acc = ("diff-" ^ string_of_int id, json_obj) :: acc in
          make_json (id + 1) s_rest c_rest acc
    | _ -> failwith "to_json: sym_list and conc_list have different length"
  in
  let actions = `Assoc (List.rev (make_json 0 sym_list conc_list [])) in
  let json_obj = `Assoc [ ("diffs", actions) ] in
  Yojson.Safe.to_channel oc_diff_json json_obj;
  close_out oc_diff_json
