module J = Yojson.Basic.Util
module H = TransformerHelper
module D = Diff

module SElement = struct
  (* type sym_id =
     | IDNotAvailable of string
     | GlobID of string
     | StmtID of string
     | ExpID of string
     | LvalID of string
     | LvalIDSet of string * string *)

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

  type sym_unop = SNot | SNeg

  type sym_const =
    | SIntConst of int
    | SFloatConst of float
    | SCharConst of char
    | SStringConst of string

  type sym_lval = SLNULL | LID of string

  type sym_exp =
    | SENULL
    | EID of string
    | SConst of sym_const * string
    | SELval of string
    | SSizeOf of sym_typ * string
    | SSizeOfE of sym_exp * string
    | SSizeOfStr of string * string
    | SBinOp of sym_binop * sym_exp * sym_exp * sym_typ * string
    | SUnOp of sym_unop * sym_exp * sym_typ * string
    | SQuestion of sym_exp * sym_exp * sym_exp * sym_typ * string
    | SCastE of sym_typ * sym_exp * string

  type sym_stmt =
    | SSNull
    | SID of string
    | SIf of sym_exp * sym_stmt list * sym_stmt list * string
    | SSet of sym_exp * sym_exp * string
    | SCall of sym_exp option * sym_exp * sym_exp list * string
    | SReturn of sym_exp option * string
    | SBlock of sym_stmt list

  type sym_global =
    | SGNull
    | SGID of string
    | SGFun of string * string
    | GVar of string * string

  type t =
    | SNull
    | SGlob of sym_global
    | SStmt of sym_stmt
    | SExp of sym_exp
    | SLval of sym_lval

  (* let pp_id fmt id =
     match id with
     | GlobID s -> Format.fprintf fmt "ID: GlobID(%s)" s
     | StmtID s -> Format.fprintf fmt "ID: StmtID(%s)" s
     | ExpID s -> Format.fprintf fmt "ID: ExpID(%s)" s
     | LvalID s -> Format.fprintf fmt "ID: LvalID(%s)" s
     | IDNotAvailable s -> Format.fprintf fmt "ID: IDNotAvailable(%s)" s
     | LvalIDSet (s1, s2) -> Format.fprintf fmt "ID: LvalIDSet(%s, %s)" s1 s2 *)

  let rec pp_selement fmt e =
    match e with
    | SNull -> Format.fprintf fmt "SNull"
    | SStmt s -> Format.fprintf fmt "SStmt(%a)" pp_sstmt s
    | SExp e -> Format.fprintf fmt "SExp(%a)" pp_sexp e
    | SLval l -> Format.fprintf fmt "SLval(%a)" pp_slval l
    | _ -> failwith "not implemented"

  and pp_sstmts fmt ss =
    List.iter (fun s -> Format.fprintf fmt "%a; " pp_sstmt s) ss

  and pp_sstmt fmt s =
    match s with
    | SSNull -> Format.fprintf fmt "SSNull"
    | SID id -> print_string id
    | SIf (e, s1, s2, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SIf(%a, %a, %a)" pp_sexp e pp_sstmts s1 pp_sstmts s2
    | SSet (l, e, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SSet(%a, %a)" pp_sexp l pp_sexp e
    | SCall (l, e, es, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SCall(%a, %a, %a)" pp_soptlval l pp_sexp e pp_sexps
          es
    | SReturn (e, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SReturn(%a)" pp_soptexp e
    | SBlock b ->
        Format.fprintf fmt "SBlock(";
        List.iter (fun s -> Format.fprintf fmt "%a\n " pp_sstmt s) b;
        Format.fprintf fmt ")"

  and pp_soptlval fmt l =
    match l with None -> Format.fprintf fmt "None" | Some l -> pp_sexp fmt l

  and pp_slval fmt l =
    match l with
    | LID lid -> print_string lid
    | SLNULL -> Format.fprintf fmt "SLNULL"

  and pp_sexps fmt es =
    List.iter (fun e -> Format.fprintf fmt "%a, " pp_sexp e) es

  and pp_soptexp fmt e =
    match e with None -> Format.fprintf fmt "None" | Some e -> pp_sexp fmt e

  and pp_sexp fmt e =
    match e with
    | SENULL -> Format.fprintf fmt "SENULL"
    | EID id -> print_string id
    | SConst (c, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SConst(%a)" pp_sconst c
    | SELval id ->
        print_string id;
        print_newline ()
    | SSizeOf (t, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SSizeOf(%a)" pp_styp t
    | SSizeOfE (e, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SSizeOfE(%a)" pp_sexp e
    | SSizeOfStr (s, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SSizeOfStr(%s)" s
    | SBinOp (op, e1, e2, t, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SBinOp(%a, %a, %a, %a)" pp_sbinop op pp_sexp e1
          pp_sexp e2 pp_styp t
    | SUnOp (op, e, t, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SUnOp(%a, %a, %a)" pp_sunop op pp_sexp e pp_styp t
    | SQuestion (e1, e2, e3, t, id) ->
        print_string id;
        print_newline ();
        Format.fprintf fmt "SQuestion(%a, %a, %a, %a)" pp_sexp e1 pp_sexp e2
          pp_styp t pp_sexp e3
    | SCastE (t, e, id) ->
        print_string id;
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

  and pp_sunop fmt op =
    match op with
    | SNot -> Format.fprintf fmt "SNot"
    | SNeg -> Format.fprintf fmt "SNeg"

  let to_null = SNull

  let rec to_typ t =
    match t with
    | SVoid -> Cil.TVoid []
    | SInt -> Cil.TInt (Cil.IInt, [])
    | SFloat -> Cil.TFloat (Cil.FDouble, [])
    | SPtr t -> Cil.TPtr (to_typ t, [])

  let rec to_styp t =
    match t with
    | Cil.TVoid _ -> SVoid
    | Cil.TInt _ -> SInt
    | Cil.TFloat _ -> SFloat
    | Cil.TPtr (t', _) -> SPtr (to_styp t')
    | _ -> failwith "not supported"

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

  let to_unop sop = match sop with SNot -> Cil.LNot | SNeg -> Cil.Neg

  let to_sunop op =
    match op with
    | Cil.LNot -> SNot
    | Cil.Neg -> SNeg
    | _ -> failwith "not supported"

  let to_sconst c =
    match c with
    | Cil.CInt64 (i, _, _) -> SIntConst (Int64.to_int i)
    | Cil.CReal (f, _, _) -> SFloatConst f
    | Cil.CChr c -> SCharConst c
    | Cil.CStr s -> SStringConst s
    | _ -> failwith "not supported"

  let sbinop_to_sym op =
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

  let rec styp_to_sym styp =
    match styp with
    | SVoid -> "void"
    | SInt -> "int"
    | SFloat -> "float"
    | SPtr t -> "ptr" ^ styp_to_sym t

  let sunop_to_sym op = match op with SNot -> "LNot" | SNeg -> "Neg"
  let compare = compare
end

module SDiff = struct
  type sym_context = { parent : string list }

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

module Matcher = struct end

let get_parent_lst diff =
  match diff with
  | D.Diff.InsertGlobal (ctx, _)
  | DeleteGlobal (ctx, _)
  | InsertStmt (ctx, _)
  | DeleteStmt (ctx, _)
  | InsertExp (ctx, _)
  | DeleteExp (ctx, _)
  | UpdateExp (ctx, _, _)
  | InsertLval (ctx, _)
  | DeleteLval (ctx, _)
  | UpdateLval (ctx, _, _) ->
      ctx.parent

let get_parent_fun parent_lst =
  let check_fun g = match g with Cil.GFun _ -> true | _ -> false in
  let get_fun g =
    match g with
    | Cil.GFun (f, _) -> f.svar
    | _ -> failwith "get_parent_fun: not a function"
  in
  let parent_fun_cand =
    List.fold_left
      (fun acc e ->
        match e with
        | D.CilElement.EGlobal g ->
            if check_fun g then get_fun g :: acc else acc
        | _ -> acc)
      [] parent_lst
  in
  if parent_fun_cand = [] then failwith "get_parent_fun: diff source not found"
  else List.hd parent_fun_cand

let global_vars = ref []

class globVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vglob g =
      match g with
      | Cil.GVar _ ->
          global_vars := g :: !global_vars;
          Cil.DoChildren
      | _ -> Cil.DoChildren
  end

let get_gvars ast =
  let gv = new globVisitor in
  Cil.visitCilFile gv ast

let reduce_cfg cfg func_name =
  H.CfgMap.fold
    (fun k v acc ->
      let vname = Str.split (Str.regexp_string "-") v |> List.hd in
      if vname = func_name then H.CfgMap.add k v acc else acc)
    cfg H.CfgMap.empty

let match_set_id cfg loc =
  let file_name = loc.Cil.file |> Filename.basename in
  H.CfgMap.fold
    (fun k v acc ->
      match k with
      | H.CSet (_, _, cloc)
      | H.CAlloc (_, _, cloc)
      | H.CFalloc (_, _, cloc)
      | H.CSalloc (_, _, cloc) ->
          if loc.Cil.line = cloc.line && file_name = cloc.file then v :: acc
          else acc
      | _ -> acc)
    cfg []

let match_call_id cfg loc =
  let file_name = loc.Cil.file |> Filename.basename in
  H.CfgMap.fold
    (fun k v acc ->
      match k with
      | H.CCall (_, _, cloc) ->
          if loc.Cil.line = cloc.line && file_name = cloc.file then v :: acc
          else acc
      | _ -> acc)
    cfg []

let match_return_id cfg loc =
  let file_name = loc.Cil.file |> Filename.basename in
  H.CfgMap.fold
    (fun k v acc ->
      match k with
      | H.CReturn1 (_, cloc) | H.CReturn2 cloc ->
          if loc.Cil.line = cloc.line && file_name = cloc.file then v :: acc
          else acc
      | _ -> acc)
    cfg []

let match_assume_id cfg loc =
  let file_name = loc.Cil.file |> Filename.basename in
  H.CfgMap.fold
    (fun k v acc ->
      match k with
      | H.CAssume (_, cloc) ->
          if loc.Cil.line = cloc.line && file_name = cloc.file then v :: acc
          else acc
      | _ -> acc)
    cfg []

let match_stmt_id cfg s =
  match s with
  | Cil.Instr i -> (
      let instr = List.hd i in
      match instr with
      | Cil.Set (_, _, loc) ->
          let matched = match_set_id cfg loc in
          if List.length matched = 1 then List.hd matched else "None"
      | Cil.Call (_, _, _, loc) ->
          let matched = match_call_id cfg loc in
          if List.length matched = 1 then List.hd matched else "None"
      | _ -> failwith "unexpected")
  | Cil.Return (_, loc) ->
      let matched = match_return_id cfg loc in
      if List.length matched = 1 then List.hd matched else "None"
  | Cil.If (_, _, _, loc) | Cil.Loop (_, loc, _, _) ->
      let matched = match_assume_id cfg loc in
      if List.length matched = 1 then List.hd matched else "None"
  | _ -> "None"

let match_const c exp_map =
  match c with
  | Cil.CInt64 (i, _, _) ->
      H.StrMap.filter (fun _ v -> Int64.to_string i |> H.subset v) exp_map
  | Cil.CStr s -> H.StrMap.filter (fun _ v -> s |> H.subset v) exp_map
  | Cil.CChr c ->
      H.StrMap.filter (fun _ v -> String.make 1 c |> H.subset v) exp_map
  | Cil.CReal (f, _, _) ->
      H.StrMap.filter (fun _ v -> string_of_float f |> H.subset v) exp_map
  | _ -> failwith "match_const: not implemented"

let match_lval l exp_map =
  let candidate =
    H.StrMap.filter (fun _ v -> H.string_of_lval l |> H.subset v) exp_map
  in
  let id, _ =
    let outmap =
      H.StrMap.fold
        (fun k v acc ->
          if acc = [] then (k, v) :: acc
          else if
            let _, prev = List.hd acc in
            String.length prev >= String.length v
          then (k, v) :: List.tl acc
          else acc)
        candidate []
    in
    if outmap = [] then ("", "") else List.hd outmap
  in
  SElement.SELval id

let match_sizeof t exp_map =
  H.StrMap.filter (fun _ v -> H.string_of_typ t |> H.subset v) exp_map

let match_exp_id exp_map e =
  let candidate =
    match e with
    | Cil.Const c -> match_const c exp_map
    | Cil.Lval l ->
        H.StrMap.filter (fun _ v -> H.string_of_lval l |> H.subset v) exp_map
    | Cil.SizeOf t -> match_sizeof t exp_map
    | Cil.BinOp _ ->
        H.StrMap.filter (fun _ v -> H.string_of_exp e |> H.subset v) exp_map
    | _ ->
        H.print_ekind e;
        failwith "match_exp: not implemented"
  in
  let id, _ =
    let outmap =
      H.StrMap.fold
        (fun k v acc ->
          if acc = [] then (k, v) :: acc
          else if
            let _, prev = List.hd acc in
            String.length prev >= String.length v
          then (k, v) :: List.tl acc
          else acc)
        candidate []
    in
    if outmap = [] then ("", "") else List.hd outmap
  in
  id

let match_lval_id cfg e = failwith "match_lval: not implemented"

let rec match_context cfg exp_map lst =
  match lst with
  | [] -> []
  | hd :: tl -> (
      match hd with
      | D.CilElement.EStmt s ->
          match_stmt_id cfg s.Cil.skind :: match_context cfg exp_map tl
      | D.CilElement.EExp e ->
          match_exp_id exp_map e :: match_context cfg exp_map tl
      | D.CilElement.ELval l ->
          match_lval_id cfg l :: match_context cfg exp_map tl
      | D.CilElement.EGlobal _ -> match_context cfg exp_map tl
      | _ -> failwith "match_context: not implemented")

(* lval = exp(lval) for now *)

let rec match_exp exp_map e =
  match e with
  | Cil.Const c -> SElement.SConst (SElement.to_sconst c, match_exp_id exp_map e)
  | Cil.Lval _ -> SELval (match_exp_id exp_map e)
  | Cil.SizeOf t -> SSizeOf (SElement.to_styp t, match_exp_id exp_map e)
  | Cil.SizeOfE e' -> SSizeOfE (match_exp exp_map e', match_exp_id exp_map e)
  | Cil.SizeOfStr s -> SSizeOfStr (s, match_exp_id exp_map e)
  | Cil.BinOp (op, e1, e2, t) ->
      SBinOp
        ( SElement.to_sbinop op,
          match_exp exp_map e1,
          match_exp exp_map e2,
          SElement.to_styp t,
          match_exp_id exp_map e )
  | Cil.UnOp (op, e, t) ->
      SUnOp
        ( SElement.to_sunop op,
          match_exp exp_map e,
          SElement.to_styp t,
          match_exp_id exp_map e )
  | Cil.CastE (t, e) ->
      SCastE (SElement.to_styp t, match_exp exp_map e, match_exp_id exp_map e)
  | Cil.Question (e1, e2, e3, t) ->
      SQuestion
        ( match_exp exp_map e1,
          match_exp exp_map e2,
          match_exp exp_map e3,
          SElement.to_styp t,
          match_exp_id exp_map e )
  | _ -> failwith "match_exp: not implemented"

let rec match_stmt cfg exp_map s =
  match s with
  | Cil.If (e, s1, s2, _) ->
      SElement.SIf
        ( match_exp exp_map e,
          List.map (fun s -> match_stmt cfg exp_map s.Cil.skind) s1.bstmts,
          List.map (fun s -> match_stmt cfg exp_map s.Cil.skind) s2.bstmts,
          match_stmt_id cfg s )
  | Cil.Instr i -> (
      let i = List.hd i in
      match i with
      | Cil.Set (l, e, _) ->
          SElement.SSet
            (match_lval l exp_map, match_exp exp_map e, match_stmt_id cfg s)
      | Cil.Call (Some l, e, es, _) ->
          SElement.SCall
            ( Some (match_lval l exp_map),
              match_exp exp_map e,
              List.map (fun e -> match_exp exp_map e) es,
              match_stmt_id cfg s )
      | Cil.Call (None, e, es, _) ->
          SElement.SCall
            ( None,
              match_exp exp_map e,
              List.map (fun e -> match_exp exp_map e) es,
              match_stmt_id cfg s )
      | _ -> failwith "match_stmt: not supported")
  | Cil.Block b ->
      let bl =
        List.fold_left
          (fun acc s -> match_stmt cfg exp_map s.Cil.skind :: acc)
          [] b.bstmts
        |> List.rev
      in
      SElement.SBlock bl
  | Cil.Return (Some e, _) ->
      SElement.SReturn (Some (match_exp exp_map e), match_stmt_id cfg s)
  | Cil.Return (None, _) -> SElement.SReturn (None, match_stmt_id cfg s)
  | Cil.Goto _ -> SElement.SSNull
  | _ -> failwith "match_stmt: not implemented"

let mk_sdiff ctx cfg exp_map diff =
  match diff with
  | D.Diff.InsertStmt (_, s) ->
      SDiff.SInsertStmt (ctx, match_stmt cfg exp_map s.Cil.skind)
  | _ -> failwith "mk_sdiff: not implemented"

let define_sym_diff donor_dir donor diff =
  get_gvars donor;
  let sparrow_dir = Filename.concat donor_dir "sparrow-out" in
  let cfg, exp_map = H.parse_sparrow sparrow_dir in
  List.fold_left
    (fun acc d ->
      let root_path = get_parent_lst d in
      let s_root_path = List.rev root_path |> match_context cfg exp_map in
      let parent_fun = get_parent_fun root_path in
      let cfg_reduced = reduce_cfg cfg parent_fun.vname in
      let s_context : SDiff.sym_context = { parent = s_root_path } in
      mk_sdiff s_context cfg_reduced exp_map d :: acc)
    [] diff

let slval_to_json slval =
  match slval with
  | SElement.EID s -> `Assoc [ ("id", `String s) ]
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

let rec sexp_to_json (sexp : SElement.sym_exp) diff =
  match (sexp, diff) with
  | EID id, _ -> `Assoc [ ("id", `String id) ]
  | SConst (const, id), _ ->
      `Assoc
        [
          ("sub", `Assoc [ ("const", sconst_to_json const diff) ]);
          ("id", `String id);
        ]
  | SELval id, Cil.Lval _ -> `Assoc [ ("id", `String id) ]
  | SSizeOfE (e1, id), Cil.SizeOfE e2 ->
      `Assoc
        [
          ("sub", `Assoc [ ("sizeof", `Assoc [ ("e", sexp_to_json e1 e2) ]) ]);
          ("id", `String id);
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
                      ("op", `String (SElement.sbinop_to_sym op1));
                      ("typ", `String (SElement.styp_to_sym typ1));
                      ("e1", sexp_to_json e1_1 e1_2);
                      ("e2", sexp_to_json e2_1 e2_2);
                    ] );
              ] );
          ("id", `String id);
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
                      ("typ", `String (SElement.styp_to_sym typ));
                      ("e", sexp_to_json e1 e2);
                    ] );
              ] );
          ("id", `String id);
        ]
  | _ -> failwith "sexp_to_json: undefined sexp"

let rec sstmt_to_json (sstmt : SElement.sym_stmt) diff =
  match (sstmt, diff.Cil.skind) with
  | SID ssid, _ -> `Assoc [ ("id", `String ssid) ]
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
                ("id", `String id);
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
                    [ ("lval", slval_to_json lv1); ("exp", sexp_to_json e1 e2) ]
                );
                ("id", `String id);
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
                      ("lval", slval_to_json lv1);
                      ("exp", sexp_to_json e1 e2);
                      ( "exps",
                        `List
                          (List.rev
                             (List.fold_left2
                                (fun acc x y -> sexp_to_json x y :: acc)
                                [] es1 es2)) );
                    ] );
                ("id", `String id);
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
                ("id", `String id);
              ] );
        ]
  | SReturn (Some e1, id), Cil.Return (Some e2, _) ->
      `Assoc
        [
          ( "return",
            `Assoc
              [
                ("sub", `Assoc [ ("exp", sexp_to_json e1 e2) ]);
                ("id", `String id);
              ] );
        ]
  | SReturn (None, id), Cil.Return (None, _) ->
      `Assoc
        [
          ( "return",
            `Assoc
              [
                ("sub", `Assoc [ ("exp", `String "None") ]); ("id", `String id);
              ] );
        ]
  | _ ->
      (* SElement.pp_sstmt Format.std_formatter sstmt; *)
      `Null

(* let slval_to_sym (slval : SElement.sym_lval) =
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
     | _ -> failwith "sstmt_to_sym: undefined sstmt" *)

let get_json_obj (saction : SDiff.t) (caction : D.Diff.t) =
  let context_json (context : SDiff.sym_context) =
    ( "context",
      `List (List.fold_left (fun acc id -> `String id :: acc) [] context.parent)
    )
  in
  match (saction, caction) with
  | SInsertStmt (context1, id), InsertStmt (_, diff) ->
      `Assoc
        [
          ("action", `String "insert_stmt");
          context_json context1;
          ("change", sstmt_to_json id diff);
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
