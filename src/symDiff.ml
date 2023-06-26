module J = Yojson.Basic.Util
module H = TransformerHelper
module D = Diff

module SElement = struct
  type sym_id =
    | IDNotAvailable of string
    | GlobID of string
    | StmtID of string
    | ExpID of string
    | LvalID of string
    | LvalIDSet of string * string

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

  type sym_lval = SLNULL | LID of sym_id

  type sym_exp =
    | SENULL
    | EID of sym_id
    | SConst of sym_const * sym_id
    | SELval of sym_lval * sym_id
    | SSizeOf of sym_typ * sym_id
    | SSizeOfE of sym_exp * sym_id
    | SSizeOfStr of string * sym_id
    | SBinOp of sym_binop * sym_exp * sym_exp * sym_typ * sym_id
    | SUnOp of string * sym_exp * sym_id
    | SQuestion of sym_exp * sym_exp * sym_exp * sym_id
    | SCastE of sym_typ * sym_exp * sym_id

  type sym_stmt =
    | SSNull
    | SID of sym_id
    | SIf of sym_exp * sym_stmt list * sym_stmt list * sym_id
    | SSet of sym_lval * sym_exp * sym_id
    | SCall of sym_lval option * sym_exp * sym_exp list * sym_id
    | SReturn of sym_exp option * sym_id

  type t = SNull | SStmt of sym_stmt | SExp of sym_exp | SLval of sym_lval

  let pp_id fmt id =
    match id with
    | GlobID s -> Format.fprintf fmt "ID: GlobID(%s)" s
    | StmtID s -> Format.fprintf fmt "ID: StmtID(%s)" s
    | ExpID s -> Format.fprintf fmt "ID: ExpID(%s)" s
    | LvalID s -> Format.fprintf fmt "ID: LvalID(%s)" s
    | IDNotAvailable s -> Format.fprintf fmt "ID: IDNotAvailable(%s)" s
    | LvalIDSet (s1, s2) -> Format.fprintf fmt "ID: LvalIDSet(%s, %s)" s1 s2

  let rec pp_selement fmt e =
    match e with
    | SNull -> Format.fprintf fmt "SNull"
    | SStmt s -> Format.fprintf fmt "SStmt(%a)" pp_sstmt s
    | SExp e -> Format.fprintf fmt "SExp(%a)" pp_sexp e
    | SLval l -> Format.fprintf fmt "SLval(%a)" pp_slval l

  and pp_sstmts fmt ss =
    List.iter (fun s -> Format.fprintf fmt "%a; " pp_sstmt s) ss

  and pp_sstmt fmt s =
    match s with
    | SSNull -> Format.fprintf fmt "SSNull"
    | SID id -> pp_id fmt id
    | SIf (e, s1, s2, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SIf(%a, %a, %a)" pp_sexp e pp_sstmts s1 pp_sstmts s2
    | SSet (l, e, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SSet(%a, %a)" pp_slval l pp_sexp e
    | SCall (l, e, es, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SCall(%a, %a, %a)" pp_soptlval l pp_sexp e pp_sexps
          es
    | SReturn (e, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SReturn(%a)" pp_soptexp e

  and pp_soptlval fmt l =
    match l with None -> Format.fprintf fmt "None" | Some l -> pp_slval fmt l

  and pp_slval fmt l =
    match l with
    | LID lid -> pp_id fmt lid
    | SLNULL -> Format.fprintf fmt "SLNULL"

  and pp_sexps fmt es =
    List.iter (fun e -> Format.fprintf fmt "%a, " pp_sexp e) es

  and pp_soptexp fmt e =
    match e with None -> Format.fprintf fmt "None" | Some e -> pp_sexp fmt e

  and pp_sexp fmt e =
    match e with
    | SENULL -> Format.fprintf fmt "SENULL"
    | EID id -> pp_id fmt id
    | SConst (c, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SConst(%a)" pp_sconst c
    | SELval (l, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SELval(%a)" pp_slval l
    | SSizeOf (t, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SSizeOf(%a)" pp_styp t
    | SSizeOfE (e, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SSizeOfE(%a)" pp_sexp e
    | SSizeOfStr (s, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SSizeOfStr(%s)" s
    | SBinOp (op, e1, e2, t, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SBinOp(%a, %a, %a, %a)" pp_sbinop op pp_sexp e1
          pp_sexp e2 pp_styp t
    | SUnOp (op, e, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SUnOp(%s, %a)" op pp_sexp e
    | SQuestion (e1, e2, e3, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SQuestion(%a, %a, %a)" pp_sexp e1 pp_sexp e2 pp_sexp
          e3
    | SCastE (t, e, id) ->
        pp_id fmt id;
        print_newline ();
        Format.fprintf fmt "SCastE(%a, %a)" pp_styp t pp_sexp e

  and pp_sconst fmt c =
    match c with
    | SIntConst i -> Format.fprintf fmt "SIntConst(%d)" i
    | SFloatConst f -> Format.fprintf fmt "SFloatConst(%f)" f
    | SCharConst c -> Format.fprintf fmt "SCharConst(%c)" c
    | SStringConst s -> Format.fprintf fmt "SStringConst(%s)" s

  and pp_styp fmt t =
    match t with
    | SVoid -> Format.fprintf fmt "SVoid"
    | SInt -> Format.fprintf fmt "SInt"
    | SFloat -> Format.fprintf fmt "SFloat"
    | SPtr t -> Format.fprintf fmt "SPtr(%a)" pp_styp t

  and pp_sbinop fmt op =
    match op with
    | SPlusA -> Format.fprintf fmt "SPlusA"
    | SPlusPI -> Format.fprintf fmt "SPlusPI"
    | SIndexPI -> Format.fprintf fmt "SIndexPI"
    | SMinusA -> Format.fprintf fmt "SMinusA"
    | SMinusPI -> Format.fprintf fmt "SMinusPI"
    | SMinusPP -> Format.fprintf fmt "SMinusPP"
    | SMod -> Format.fprintf fmt "SMod"
    | SShiftlt -> Format.fprintf fmt "SShiftlt"
    | SShiftrt -> Format.fprintf fmt "SShiftrt"
    | SAnd -> Format.fprintf fmt "SAnd"
    | SXor -> Format.fprintf fmt "SXor"
    | SOr -> Format.fprintf fmt "SOr"
    | SLt -> Format.fprintf fmt "SLt"
    | SGt -> Format.fprintf fmt "SGt"
    | SLe -> Format.fprintf fmt "SLe"
    | SGe -> Format.fprintf fmt "SGe"
    | SEq -> Format.fprintf fmt "SEq"
    | SNe -> Format.fprintf fmt "SNe"
    | SLAnd -> Format.fprintf fmt "SLAnd"
    | SLOr -> Format.fprintf fmt "SLOr"
    | _ -> Format.fprintf fmt "SUnknown"

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
    s_snk : SElement.t;
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
      | Cil.Instr i, Ccall (_, _, loc) -> (
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
  | Cil.Instr i, Ccall (_, ce, _) -> (
      let instr = List.hd i in
      match instr with
      | Cil.Call (_, exp, param, _) -> (
          match ce with
          | CcallExp (f, a, _) ->
              if List.length param <> List.length a then H.ExpMap.empty
              else
                H.ExpMap.union
                  (fun _ v1 _ -> Some v1)
                  (List.fold_left2
                     (fun acc p e -> H.ExpMap.add p e acc)
                     H.ExpMap.empty param a)
                  (H.ExpMap.add exp f H.ExpMap.empty)
          | _ -> failwith "wrong format of call statement")
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
  | Cil.Instr i, Ccall (_, ce, _) -> (
      match ce with
      | CcallExp (f, _, _) -> (
          let instr = List.hd i in
          match instr with
          | Cil.Call (Some lval, _, _, _) ->
              H.LvalMap.add lval f H.LvalMap.empty
          | _ -> H.LvalMap.empty)
      | _ -> failwith "wrong format of call statement")
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
  | `Assoc [ ("lval_id", lid); ("exp_id", eid) ] ->
      let lval_id = lid |> J.to_string in
      let exp_id = eid |> J.to_string in
      SElement.LID (SElement.LvalIDSet (lval_id, exp_id))
  | `Assoc [ ("id", lid) ] ->
      let id = lid |> J.to_string in
      SElement.LID (SElement.LvalID id)
  | `Assoc [ ("literal", str) ] ->
      let literal = str |> J.to_string in
      SElement.LID (SElement.IDNotAvailable literal)
  | _ -> failwith "parse_lval_json: undefined behavior"

let extract_exp_id is_id id_or_lit =
  if is_id then SElement.ExpID id_or_lit else IDNotAvailable id_or_lit

let parse_const_json const is_id id_or_lit =
  match const with
  | `Assoc [ ("type", typ); ("literal", lit) ] -> (
      let t = J.to_string typ in
      let l = J.to_string lit in
      match t with
      | "int" ->
          SElement.SConst
            (SIntConst (int_of_string l), extract_exp_id is_id id_or_lit)
      | "float" ->
          SConst
            (SFloatConst (float_of_string l), extract_exp_id is_id id_or_lit)
      | "char" ->
          SConst
            (SCharConst (List.hd (H.explode l)), extract_exp_id is_id id_or_lit)
      | "string" -> SConst (SStringConst l, extract_exp_id is_id id_or_lit)
      | _ -> failwith "parse_const_json: undefined behavior")
  | _ -> failwith "parse_const_json: undefined behavior"

let rec parse_exp_json contents =
  let sub = J.member "sub" contents in
  let is_id = not (Yojson.Basic.Util.member "id" contents = `Null) in
  let id_or_lit =
    if is_id then J.member "id" contents else J.member "literal" contents
  in
  let id_or_lit = id_or_lit |> J.to_string in
  if sub <> `Null then
    match sub with
    | `Assoc [ ("const", contents) ] ->
        parse_const_json contents is_id id_or_lit
    | `Assoc [ ("binop", contents) ] ->
        let op = parse_op (contents |> J.member "op" |> J.to_string) in
        let typ = parse_typ (contents |> J.member "typ") in
        let e1 = parse_exp_json (contents |> J.member "e1") in
        let e2 = parse_exp_json (contents |> J.member "e2") in
        if is_id then SElement.SBinOp (op, e1, e2, typ, ExpID id_or_lit)
        else SBinOp (op, e1, e2, typ, IDNotAvailable id_or_lit)
    | `Assoc [ ("cast", contents) ] ->
        let typ = parse_typ (contents |> J.member "typ") in
        let e = parse_exp_json (contents |> J.member "e") in
        if is_id then SElement.SCastE (typ, e, ExpID id_or_lit)
        else SCastE (typ, e, IDNotAvailable id_or_lit)
    | `Assoc [ ("sizeof", contents) ] ->
        let e = parse_exp_json contents in
        if is_id then SElement.SSizeOfE (e, ExpID id_or_lit)
        else SSizeOfE (e, IDNotAvailable id_or_lit)
    | `Assoc [ ("lval", contents) ] ->
        let lv = parse_lval_json contents in
        if is_id then SElement.SELval (lv, ExpID id_or_lit)
        else SELval (lv, IDNotAvailable id_or_lit)
    | _ -> failwith "parse_exp_json: undefined behavior"
  else if is_id then SElement.EID (ExpID id_or_lit)
  else SElement.EID (IDNotAvailable id_or_lit)

let parse_return_json contents =
  let sub = J.member "sub" contents in
  let is_id = not (Yojson.Basic.Util.member "id" contents = `Null) in
  let id_or_lit =
    if is_id then J.member "id" contents else J.member "literal" contents
  in
  let id_or_lit = id_or_lit |> J.to_string in
  match sub with
  | `Assoc [ ("exp", exp) ] -> (
      match exp with
      | `String s ->
          if is_id then
            if s = "None" then SElement.SReturn (None, SElement.StmtID id_or_lit)
            else SReturn (Some (parse_exp_json exp), SElement.StmtID id_or_lit)
          else if s = "None" then
            SReturn (None, SElement.IDNotAvailable id_or_lit)
          else
            SReturn
              (Some (parse_exp_json exp), SElement.IDNotAvailable id_or_lit)
      | `Assoc _ ->
          if is_id then
            SReturn (Some (parse_exp_json exp), SElement.StmtID id_or_lit)
          else
            SReturn
              (Some (parse_exp_json exp), SElement.IDNotAvailable id_or_lit)
      | _ -> failwith "parse_return_json: undefined behavior")
  | _ -> failwith "parse_return_json: undefined behavior"

let rec parse_if_json contents =
  let sub = J.member "sub" contents in
  let is_id = not (Yojson.Basic.Util.member "id" contents = `Null) in
  let id_or_lit =
    if is_id then J.member "id" contents else J.member "literal" contents
  in
  let id_or_lit = id_or_lit |> J.to_string in
  match sub with
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
      if is_id then
        SElement.SIf (cond, then_block, else_block, SElement.StmtID id_or_lit)
      else SIf (cond, then_block, else_block, IDNotAvailable id_or_lit)
  | _ -> failwith "parse_if_json: undefined behavior"

and parse_stmt_json sym =
  match sym with
  | `Assoc [ (stmt_name, contents) ] -> (
      match stmt_name with
      | "if" -> parse_if_json contents
      | "return" -> parse_return_json contents
      | _ -> failwith "parse_stmt_json: not implemented")
  | _ -> failwith "parse_stmt_json: undefined behavior"

let parse_context sink_node action context =
  match action with
  | "insert_stmt" | "delete_stmt" ->
      let parent = J.member "parent" context in
      let parent_sym = J.member "id" parent |> J.to_string in
      let s_parent =
        if parent_sym = "Null" then SElement.SNull
        else SStmt (SID (StmtID parent_sym))
      in
      let left = J.member "left" context in
      let left_sym = J.member "id" left |> J.to_string in
      let s_left_sibling =
        if left_sym = "Null" then SElement.SNull
        else SStmt (SID (StmtID left_sym))
      in
      let right = J.member "right" context in
      let right_sym = J.member "id" right |> J.to_string in
      let s_right_sibling =
        if right_sym = "Null" then SElement.SNull
        else SStmt (SID (StmtID right_sym))
      in
      {
        SDiff.s_parent;
        s_left_sibling;
        s_right_sibling;
        s_snk = SElement.SStmt (SElement.SID sink_node);
      }
  | "insert_exp" | "delete_exp" | "update_exp" | "insert_lval" | "delete_lval"
  | "update_lval" ->
      let parent = J.member "parent" context in
      let parent_sym = J.member "id" parent |> J.to_string in
      let s_parent =
        if parent_sym = "Null" then SElement.SNull
        else SElement.SStmt (SID (StmtID parent_sym))
      in
      let left = J.member "left" context in
      let left_sym = J.member "id" left |> J.to_string in
      let s_left_sibling =
        if left_sym = "Null" then SElement.SNull
        else SElement.SExp (EID (ExpID left_sym))
      in
      let right = J.member "right" context in
      let right_sym = J.member "id" right |> J.to_string in
      let s_right_sibling =
        if right_sym = "Null" then SElement.SNull
        else SElement.SExp (EID (ExpID right_sym))
      in
      {
        s_parent;
        s_left_sibling;
        s_right_sibling;
        s_snk = SElement.SStmt (SElement.SID sink_node);
      }
  | _ -> failwith "parse_sym_json: undefined behavior"

let parse_sym_json sink_node action context sym =
  let context = parse_context sink_node action context in
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

let parse_edit_function (sink_node : string) path_name =
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
         parse_sym_json (StmtID sink_node) action context sym :: acc)
       [] diffs)

let match_lval (sol : string H.StrMap.t) lv =
  match lv with
  | SElement.LID (LvalID id) -> (
      let opt = H.StrMap.find_opt id sol in
      match opt with
      | Some id -> SElement.SLval (LID (LvalID id))
      | None -> failwith "lval id not found")
  | SElement.LID (LvalIDSet (lid, eid)) -> (
      let opt = H.StrMap.find_opt lid sol in
      match opt with
      | Some id -> SElement.SLval (LID (LvalID id))
      | None ->
          let id = H.StrMap.find eid sol in
          SElement.SExp (EID (ExpID id)))
  | SLNULL -> SNull
  | _ -> failwith "undefined behavior"

let check_exp_id id (sol : string H.StrMap.t) =
  print_endline id;
  let opt = H.StrMap.find_opt id sol in
  match opt with Some new_id -> SElement.EID (ExpID new_id) | _ -> SENULL

let rec match_exp (sol : string H.StrMap.t) exp =
  match exp with
  | SElement.EID (ExpID id) -> check_exp_id id sol
  | SConst (c, id) -> (
      match id with ExpID id -> check_exp_id id sol | _ -> SConst (c, id))
  | SSizeOf (t, id) -> (
      match id with ExpID id -> check_exp_id id sol | _ -> SSizeOf (t, id))
  | SSizeOfE (e, id) -> (
      match id with
      | ExpID id -> check_exp_id id sol
      | _ -> SSizeOfE (match_exp sol e, id))
  | SSizeOfStr (s, id) -> (
      match id with ExpID id -> check_exp_id id sol | _ -> SSizeOfStr (s, id))
  | SBinOp (b, e1, e2, t, id) -> (
      match id with
      | ExpID id -> check_exp_id id sol
      | _ -> SBinOp (b, match_exp sol e1, match_exp sol e2, t, id))
  | SUnOp (u, e, id) -> (
      match id with
      | ExpID id -> check_exp_id id sol
      | _ -> SUnOp (u, match_exp sol e, id))
  | SQuestion (e1, e2, e3, id) -> (
      match id with
      | ExpID id -> check_exp_id id sol
      | _ -> SQuestion (match_exp sol e1, match_exp sol e2, match_exp sol e3, id)
      )
  | SCastE (t, e, id) -> (
      match id with
      | ExpID id -> check_exp_id id sol
      | _ -> SCastE (t, match_exp sol e, id))
  | SELval (lv, id) -> (
      match id with
      | ExpID id -> check_exp_id id sol
      | _ -> (
          let return = match_lval sol lv in
          match return with
          | SElement.SLval lv -> SElement.SELval (lv, id)
          | SElement.SExp (EID e) -> SElement.EID e
          | _ -> failwith "undefined behavior"))
  | _ -> failwith "match_exp: undefined behavior"

let extract_lval sol lv =
  let return = match_lval sol lv in
  match return with
  | SElement.SLval lv -> lv
  | _ -> failwith "undefined behavior"

let check_stmt_id id (sol : string H.StrMap.t) =
  let opt = H.StrMap.find_opt id sol in
  match opt with Some new_id -> SElement.SID (StmtID new_id) | _ -> SSNull

let rec match_stmt (sol : string H.StrMap.t) stmt =
  match stmt with
  | SElement.SID (StmtID id) -> check_stmt_id id sol
  | SIf (cond, then_block, else_block, id) -> (
      match id with
      | StmtID id -> check_stmt_id id sol
      | _ ->
          let new_cond = match_exp sol cond in
          let new_then_block = List.map (match_stmt sol) then_block in
          let new_else_block = List.map (match_stmt sol) else_block in
          SIf (new_cond, new_then_block, new_else_block, id))
  | SReturn (Some exp, id) -> (
      match id with
      | StmtID id -> check_stmt_id id sol
      | _ -> SReturn (Some (match_exp sol exp), id))
  | SReturn (None, id) -> (
      match id with StmtID id -> check_stmt_id id sol | _ -> SReturn (None, id))
  | SSNull -> SSNull
  | SSet (lv, exp, id) -> (
      match id with
      | StmtID id -> check_stmt_id id sol
      | _ -> SSet (extract_lval sol lv, match_exp sol exp, id))
  | SCall (None, func, param, id) -> (
      match id with
      | StmtID id -> check_stmt_id id sol
      | _ -> SCall (None, match_exp sol func, List.map (match_exp sol) param, id)
      )
  | SCall (Some lv, func, param, id) -> (
      match id with
      | StmtID id -> check_stmt_id id sol
      | _ ->
          SCall
            ( Some (extract_lval sol lv),
              match_exp sol func,
              List.map (match_exp sol) param,
              id ))
  | _ -> failwith "match_stmt: undefined behavior"

let match_selem (sol : string H.StrMap.t) (selem : SElement.t) =
  match selem with
  | SElement.SNull -> SElement.SNull
  | SStmt stmt -> SStmt (match_stmt sol stmt)
  | SExp exp -> SExp (match_exp sol exp)
  | SLval _ -> failwith "not implemented"

(* delete this *)
let print_setype (exp : SElement.sym_exp) =
  match exp with
  | SENULL -> "SENULL"
  | SConst _ -> "SConst"
  | SSizeOf _ -> "SSizeOf"
  | SSizeOfE _ -> "SSizeOfE"
  | SSizeOfStr _ -> "SSizeOfStr"
  | SBinOp _ -> "SBinOp"
  | SUnOp _ -> "SUnOp"
  | SQuestion _ -> "SQuestion"
  | SCastE _ -> "SCastE"
  | _ -> failwith "print_setype: undefined behavior"

let match_sym (sol : string H.StrMap.t) (action : SDiff.t) =
  match action with
  | SInsertStmt (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_stmt sol sym in
      SDiff.SInsertStmt
        ( { s_parent; s_left_sibling; s_right_sibling; s_snk = context.s_snk },
          sym )
  | SDeleteStmt (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_stmt sol sym in
      SDeleteStmt
        ( { s_parent; s_left_sibling; s_right_sibling; s_snk = context.s_snk },
          sym )
  | SInsertExp (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_exp sol sym in
      SInsertExp
        ( { s_parent; s_left_sibling; s_right_sibling; s_snk = context.s_snk },
          sym )
  | SDeleteExp (context, sym) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let sym = match_exp sol sym in
      SDeleteExp
        ( { s_parent; s_left_sibling; s_right_sibling; s_snk = context.s_snk },
          sym )
  | SUpdateExp (context, from, to_) ->
      let s_parent = match_selem sol context.s_parent in
      let s_left_sibling = match_selem sol context.s_left_sibling in
      let s_right_sibling = match_selem sol context.s_right_sibling in
      let from = match_exp sol from in
      let to_ = match_exp sol to_ in
      SUpdateExp
        ( { s_parent; s_left_sibling; s_right_sibling; s_snk = context.s_snk },
          from,
          to_ )
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

let find_lval_sym l_to_e_map lval lval_map =
  let matched_id =
    H.LvalMap.fold
      (fun k v acc -> if H.eq_lval_conc k lval then v :: acc else acc)
      lval_map []
  in
  let exp_id =
    H.StrMap.fold
      (fun k v acc -> if k = List.hd matched_id then v :: acc else acc)
      l_to_e_map []
  in
  if List.length matched_id <> 0 then
    if List.length exp_id <> 0 then
      SElement.LvalIDSet (List.hd matched_id, List.hd exp_id)
    else SElement.LvalID (List.hd matched_id)
  else IDNotAvailable (H.string_of_lval lval)

let get_lval_sym stmt lval cil_map =
  let info_key = H.get_info_key stmt cil_map in
  if H.LvalMap.exists (fun k _ -> H.eq_lval_conc k lval) info_key.H.lvals then
    let result =
      H.LvalMap.fold
        (fun k v acc -> if H.eq_lval_conc k lval then v :: acc else acc)
        info_key.H.lvals []
    in
    match List.rev result with
    | hd :: _ -> SElement.LID (LvalID hd)
    | [] -> failwith "get_lval_sym: not found"
  else SElement.LID (IDNotAvailable (H.string_of_lval lval))

let make_lval_map stmt cil_map =
  let map =
    H.InfoMap.fold
      (fun k _ acc ->
        if H.eq_stmt_conc k.stmt stmt then k.lvals :: acc else acc)
      cil_map []
  in
  if List.length map <> 0 then List.hd map
  else
    H.InfoMap.fold
      (fun k _ acc -> H.LvalMap.union (fun _ _ y -> Some y) k.lvals acc)
      cil_map H.LvalMap.empty

let make_exp_map stmt cil_map =
  let map =
    H.InfoMap.fold
      (fun k _ acc -> if H.eq_stmt_conc k.stmt stmt then k.exps :: acc else acc)
      cil_map []
  in
  if List.length map <> 0 then List.hd map
  else
    H.InfoMap.fold
      (fun k _ acc -> H.ExpMap.union (fun _ _ y -> Some y) k.exps acc)
      cil_map H.ExpMap.empty

let make_exp_sym l_to_e_map p_stmt exp cil_map =
  let exp_map = make_exp_map p_stmt cil_map in
  let lval_map = make_lval_map p_stmt cil_map in
  let rec find_exp_sym (exp : Cil.exp) =
    let e_id =
      let matched_id =
        H.ExpMap.fold
          (fun k v acc -> if H.eq_exp_conc k exp then v :: acc else acc)
          exp_map []
      in
      if List.length matched_id = 0 then
        SElement.IDNotAvailable (H.string_of_exp exp)
      else SElement.ExpID (List.hd matched_id)
    in
    match exp with
    | Cil.SizeOfE e -> SElement.SSizeOfE (find_exp_sym e, e_id)
    | Cil.CastE (typ, e) ->
        SElement.SCastE (cil_to_sym_typ typ, find_exp_sym e, e_id)
    | Cil.BinOp (op, e1, e2, typ) ->
        SElement.SBinOp
          ( SElement.to_sbinop op,
            find_exp_sym e1,
            find_exp_sym e2,
            cil_to_sym_typ typ,
            e_id )
    | Cil.Lval lval ->
        SElement.SELval
          (SElement.LID (find_lval_sym l_to_e_map lval lval_map), e_id)
    | Cil.Const c -> SElement.SConst (SElement.to_sconst c, e_id)
    | _ -> SElement.EID e_id
  in
  find_exp_sym exp

let get_exp_sym l_to_e_map stmt exp cil_map =
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
    | hd :: _ -> SElement.EID (SElement.ExpID hd)
    | [] -> failwith "get_exp_sym: not found"
  else make_exp_sym l_to_e_map stmt exp cil_map

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

let make_sym_context l_to_e_map context cil_map =
  let parent_sym =
    match context.D.Diff.parent with
    | Null | EGlobal _ -> SElement.to_null
    | EStmt stmt -> (
        let sym = get_main_sym stmt cil_map in
        match sym with None -> SNull | Some s -> SStmt (SID (StmtID s)))
    | _ -> failwith "make_sym_context: unexpected parent"
  in
  let left_sibling_sym =
    match context.left_sibling with
    | Null | EGlobal _ -> SElement.to_null
    | EStmt stmt -> (
        let sym = get_main_sym stmt cil_map in
        match sym with None -> SNull | Some s -> SStmt (SID (StmtID s)))
    | EExp exp ->
        SExp
          (get_exp_sym l_to_e_map
             (D.CilElement.elem_to_stmt context.parent)
             exp cil_map)
    | _ -> failwith "make_sym_context: unexpected left sibling"
  in
  let right_sibling_sym =
    match context.right_sibling with
    | Null | EGlobal _ -> SElement.to_null
    | EStmt stmt -> (
        let sym = get_main_sym stmt cil_map in
        match sym with None -> SNull | Some s -> SStmt (SID (StmtID s)))
    | EExp exp ->
        SExp
          (get_exp_sym l_to_e_map
             (D.CilElement.elem_to_stmt context.parent)
             exp cil_map)
    | _ -> failwith "make_sym_context: unexpected right sibling"
  in
  {
    SDiff.s_parent = parent_sym;
    s_left_sibling = left_sibling_sym;
    s_right_sibling = right_sibling_sym;
    s_snk = SElement.to_null;
  }

let find_stmt_sym stmt cil_map =
  let matched =
    H.InfoMap.fold
      (fun k v acc ->
        if H.string_of_stmt k.stmt = H.string_of_stmt stmt then v :: acc
        else acc)
      cil_map []
  in
  if List.length matched = 1 then SElement.StmtID (List.hd matched)
  else SElement.IDNotAvailable (H.string_of_stmt stmt)

let rec make_main_sym l_to_e_map stmt cil_map =
  let stmt_id = find_stmt_sym stmt cil_map in
  let lval_map = make_lval_map stmt cil_map in
  match stmt.Cil.skind with
  | Cil.Instr i -> (
      match List.hd i with
      | Cil.Call (None, f, exps, _) ->
          SElement.SCall
            ( None,
              make_exp_sym l_to_e_map stmt f cil_map,
              List.fold_left
                (fun acc exp -> make_exp_sym l_to_e_map stmt exp cil_map :: acc)
                [] exps,
              stmt_id )
      | Cil.Call (Some lv, f, exps, _) ->
          SElement.SCall
            ( Some (SElement.LID (find_lval_sym l_to_e_map lv lval_map)),
              make_exp_sym l_to_e_map stmt f cil_map,
              List.fold_left
                (fun acc exp -> make_exp_sym l_to_e_map stmt exp cil_map :: acc)
                [] exps,
              stmt_id )
      | Cil.Set (lv, exp, _) ->
          SElement.SSet
            ( SElement.LID (find_lval_sym l_to_e_map lv lval_map),
              make_exp_sym l_to_e_map stmt exp cil_map,
              stmt_id )
      | _ -> failwith "make_main_sym: undefined instruction")
  | Cil.If (cond, t_b, e_b, _) ->
      let cond_sym = make_exp_sym l_to_e_map stmt cond cil_map in
      let t_stmts = t_b.bstmts in
      let e_stmts = e_b.bstmts in
      let t_syms =
        List.map (fun stmt -> make_main_sym l_to_e_map stmt cil_map) t_stmts
      in
      let e_syms =
        List.map (fun stmt -> make_main_sym l_to_e_map stmt cil_map) e_stmts
      in
      SElement.SIf (cond_sym, t_syms, e_syms, stmt_id)
  | Cil.Return (Some exp, _) ->
      SElement.SReturn (Some (make_exp_sym l_to_e_map stmt exp cil_map), stmt_id)
  | Cil.Return (None, _) -> SElement.SReturn (None, stmt_id)
  | _ -> failwith "make_main_sym: undefined statement"

let rec fold_diff l_to_e_map cil_map ast_diff acc =
  match ast_diff with
  | [] -> acc
  | hd :: tl -> (
      match hd with
      | D.Diff.InsertStmt (context, stmt) ->
          SDiff.SInsertStmt
            ( make_sym_context l_to_e_map context cil_map,
              make_main_sym l_to_e_map stmt cil_map )
          :: fold_diff l_to_e_map cil_map tl acc
      | DeleteStmt (context, stmt) ->
          SDiff.SDeleteStmt
            ( make_sym_context l_to_e_map context cil_map,
              let sym = get_main_sym stmt cil_map in
              match sym with
              | None -> SID (IDNotAvailable (H.string_of_stmt stmt))
              | Some s -> SID (StmtID s) )
          :: fold_diff l_to_e_map cil_map tl acc
      | InsertExp (context, exp) ->
          SDiff.SInsertExp
            ( make_sym_context l_to_e_map context cil_map,
              make_exp_sym l_to_e_map
                (D.CilElement.elem_to_stmt context.parent)
                exp cil_map )
          :: fold_diff l_to_e_map cil_map tl acc
      | DeleteExp (context, exp) ->
          SDiff.SDeleteExp
            ( make_sym_context l_to_e_map context cil_map,
              make_exp_sym l_to_e_map
                (D.CilElement.elem_to_stmt context.parent)
                exp cil_map )
          :: fold_diff l_to_e_map cil_map tl acc
      | UpdateExp (context, _from, _to) ->
          SDiff.SUpdateExp
            ( make_sym_context l_to_e_map context cil_map,
              make_exp_sym l_to_e_map
                (D.CilElement.elem_to_stmt context.parent)
                _from cil_map,
              SElement.EID (SElement.IDNotAvailable (H.string_of_exp _to)) )
          :: fold_diff l_to_e_map cil_map tl acc
      | InsertLval (context, lval) ->
          SDiff.SInsertLval
            ( make_sym_context l_to_e_map context cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                lval cil_map )
          :: fold_diff l_to_e_map cil_map tl acc
      | DeleteLval (context, lval) ->
          SDiff.SDeleteLval
            ( make_sym_context l_to_e_map context cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                lval cil_map )
          :: fold_diff l_to_e_map cil_map tl acc
      | UpdateLval (context, _from, _to) ->
          SDiff.SUpdateLval
            ( make_sym_context l_to_e_map context cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                _from cil_map,
              get_lval_sym
                (D.CilElement.elem_to_stmt context.parent)
                _to cil_map )
          :: fold_diff l_to_e_map cil_map tl acc
      | _ -> fold_diff l_to_e_map cil_map tl acc)

let define_sym_diff sparrow_path cil_map ast_diff =
  let l_to_e_map =
    H.make_str_map_rev
      (Filename.concat sparrow_path "taint/datalog/LvalExp.facts")
  in
  fold_diff l_to_e_map cil_map ast_diff []

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

let slval_to_json (slval : SElement.sym_lval) diff =
  match (slval, diff) with
  | LID (LvalID id), _ -> `Assoc [ ("id", `String id) ]
  | LID (LvalIDSet (lid, eid)), _ ->
      `Assoc [ ("lval_id", `String lid); ("exp_id", `String eid) ]
  | LID (IDNotAvailable str), _ -> `Assoc [ ("literal", `String str) ]
  | SLNULL, _ -> `Assoc [ ("id", `String "Null") ]
  | _ -> failwith "slval_to_json: undefined slval"

let sconst_to_json (sconst : SElement.sym_const) diff =
  match (sconst, diff) with
  | SIntConst i, _ ->
      `Assoc [ ("type", `String "int"); ("literal", `String (Int.to_string i)) ]
  | SFloatConst f, _ ->
      `Assoc
        [ ("type", `String "float"); ("literal", `String (Float.to_string f)) ]
  | SStringConst s, _ ->
      `Assoc [ ("type", `String "str"); ("literal", `String s) ]
  | SCharConst c, _ ->
      `Assoc
        [ ("type", `String "char"); ("literal", `String (String.make 1 c)) ]

let extract_exp_id id =
  match id with
  | SElement.ExpID id -> ("id", `String id)
  | SElement.IDNotAvailable str -> ("literal", `String str)
  | _ -> failwith "extract_exp_id: undefined id"

let rec sexp_to_json (sexp : SElement.sym_exp) diff =
  match (sexp, diff) with
  | EID (ExpID id), _ -> `Assoc [ ("id", `String id) ]
  | EID (IDNotAvailable str), _ -> `Assoc [ ("literal", `String str) ]
  | SConst (const, id), _ ->
      `Assoc
        [
          ("sub", `Assoc [ ("const", sconst_to_json const diff) ]);
          extract_exp_id id;
        ]
  | SELval (lv1, id), Cil.Lval lv2 ->
      `Assoc
        [
          ("sub", `Assoc [ ("lval", slval_to_json lv1 lv2) ]); extract_exp_id id;
        ]
  | SSizeOfE (e1, id), Cil.SizeOfE e2 ->
      `Assoc
        [
          ("sub", `Assoc [ ("sizeof", `Assoc [ ("e", sexp_to_json e1 e2) ]) ]);
          extract_exp_id id;
        ]
  | SBinOp (op1, e1_1, e2_1, typ1, id), Cil.BinOp (_, e1_2, e2_2, _) ->
      `Assoc
        [
          ( "sub",
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
              ] );
          extract_exp_id id;
        ]
  | SCastE (typ, e1, id), Cil.CastE (_, e2) ->
      `Assoc
        [
          ( "sub",
            `Assoc
              [
                ( "cast",
                  `Assoc
                    [
                      ("typ", `String (styp_to_sym typ));
                      ("e", sexp_to_json e1 e2);
                    ] );
              ] );
          extract_exp_id id;
        ]
  | _ -> failwith "sexp_to_json: undefined sexp"

let extract_stmt_id id =
  match id with
  | SElement.StmtID id -> ("id", `String id)
  | SElement.IDNotAvailable str -> ("literal", `String str)
  | _ -> failwith "extract_stmt_id: undefined id"

let rec sstmt_to_json (sstmt : SElement.sym_stmt) diff =
  match (sstmt, diff.Cil.skind) with
  | SID ssid, _ -> (
      match ssid with
      | StmtID id -> `Assoc [ ("id", `String id) ]
      | IDNotAvailable lit -> `Assoc [ ("literal", `String lit) ]
      | _ -> failwith "sstmt_to_json: undefined ssid type")
  | SIf (exp1, tb1, eb1, id), Cil.If (exp2, tb2, eb2, _) ->
      `Assoc
        [
          ( "if",
            `Assoc
              [
                ( "sub",
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
                extract_stmt_id id;
              ] );
        ]
  | SSet (lv1, e1, id), Cil.Instr [ Cil.Set (lv2, e2, _) ] ->
      `Assoc
        [
          ( "set",
            `Assoc
              [
                ( "sub",
                  `Assoc
                    [
                      ("lval", slval_to_json lv1 lv2);
                      ("exp", sexp_to_json e1 e2);
                    ] );
                extract_stmt_id id;
              ] );
        ]
  | SCall (Some lv1, e1, es1, id), Cil.Instr [ Cil.Call (Some lv2, e2, es2, _) ]
    ->
      `Assoc
        [
          ( "call",
            `Assoc
              [
                ( "sub",
                  `Assoc
                    [
                      ("lval", slval_to_json lv1 lv2);
                      ("exp", sexp_to_json e1 e2);
                      ( "exps",
                        `List
                          (List.rev
                             (List.fold_left2
                                (fun acc x y -> sexp_to_json x y :: acc)
                                [] es1 es2)) );
                    ] );
                extract_stmt_id id;
              ] );
        ]
  | SCall (None, e1, es1, id), Cil.Instr [ Cil.Call (None, e2, es2, _) ] ->
      `Assoc
        [
          ( "call",
            `Assoc
              [
                ( "sub",
                  `Assoc
                    [
                      ("lval", `String "None");
                      ("exp", sexp_to_json e1 e2);
                      ( "exps",
                        `List
                          (List.rev
                             (List.fold_left2
                                (fun acc x y -> sexp_to_json x y :: acc)
                                [] es1 es2)) );
                    ] );
                extract_stmt_id id;
              ] );
        ]
  | SReturn (Some e1, id), Cil.Return (Some e2, _) ->
      `Assoc
        [
          ( "return",
            `Assoc
              [
                ("sub", `Assoc [ ("exp", sexp_to_json e1 e2) ]);
                extract_stmt_id id;
              ] );
        ]
  | SReturn (None, id), Cil.Return (None, _) ->
      `Assoc
        [
          ( "return",
            `Assoc
              [
                ("sub", `Assoc [ ("exp", `String "None") ]); extract_stmt_id id;
              ] );
        ]
  | _ ->
      SElement.pp_sstmt Format.std_formatter sstmt;
      failwith "sstmt_to_json: undefined sstmt"

let slval_to_sym (slval : SElement.sym_lval) =
  match slval with
  | LID (LvalID id) -> `Assoc [ ("id", `String id) ]
  | LID (IDNotAvailable s) -> `Assoc [ ("literal", `String s) ]
  | _ -> failwith "slval_to_sym: undefined slval"

let sexp_to_sym (sexp : SElement.sym_exp) =
  match sexp with
  | EID (ExpID str) -> `Assoc [ ("id", `String str) ]
  | EID (IDNotAvailable s) -> `Assoc [ ("literal", `String s) ]
  | _ -> failwith "sexp_to_sym: undefined sexp"

let sstmt_to_sym (sstmt : SElement.sym_stmt) =
  match sstmt with
  | SID (StmtID id) -> `Assoc [ ("id", `String id) ]
  | SID (IDNotAvailable s) -> `Assoc [ ("literal", `String s) ]
  | _ -> failwith "sstmt_to_sym: undefined sstmt"

let sym_to_lit sym =
  match sym with
  | SElement.SStmt sstmt -> sstmt_to_sym sstmt
  | SElement.SExp sexp -> sexp_to_sym sexp
  | SElement.SLval slval -> slval_to_sym slval
  | SElement.SNull -> `Assoc [ ("id", `String "Null") ]

let get_json_obj (saction : SDiff.t) (caction : D.Diff.t) =
  let context_json (context : SDiff.sym_context) =
    ( "context",
      `Assoc
        [
          ("parent", sym_to_lit context.s_parent);
          ("left", sym_to_lit context.s_left_sibling);
          ("right", sym_to_lit context.s_right_sibling);
        ] )
  in
  match (saction, caction) with
  | SInsertStmt (context1, sym), InsertStmt (_, diff) ->
      `Assoc
        [
          ("action", `String "insert_stmt");
          context_json context1;
          ("change", sstmt_to_json sym diff);
        ]
  | SDeleteStmt (context1, sym), DeleteStmt (_, _) ->
      `Assoc
        [
          ("action", `String "delete_stmt");
          context_json context1;
          ("change", sstmt_to_sym sym);
        ]
  | SInsertExp (context1, sym), InsertExp (_, diff) ->
      `Assoc
        [
          ("action", `String "insert_exp");
          context_json context1;
          ("change", sexp_to_json sym diff);
        ]
  | SDeleteExp (context1, sym), DeleteExp (_, _) ->
      `Assoc
        [
          ("action", `String "delete_exp");
          context_json context1;
          ("change", sexp_to_sym sym);
        ]
  | SUpdateExp (context1, from1, to1), UpdateExp (_, _, _) ->
      `Assoc
        [
          ("action", `String "update_exp");
          context_json context1;
          ( "change",
            `Assoc [ ("from", sexp_to_sym from1); ("to", sexp_to_sym to1) ] );
        ]
  | SInsertLval (context1, sym), InsertLval (_, _) ->
      `Assoc
        [
          ("action", `String "insert_lval");
          context_json context1;
          ("change", slval_to_sym sym);
        ]
  | SDeleteLval (context1, sym), DeleteLval (_, _) ->
      `Assoc
        [
          ("action", `String "delete_lval");
          context_json context1;
          ("change", slval_to_sym sym);
        ]
  | SUpdateLval (context1, from1, to1), UpdateLval (_, _, _) ->
      `Assoc
        [
          ("action", `String "update_lval");
          context_json context1;
          ( "change",
            `Assoc [ ("from", slval_to_sym from1); ("to", slval_to_sym to1) ] );
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
  Yojson.Safe.pretty_to_channel oc_diff_json json_obj;
  close_out oc_diff_json
