module J = Yojson.Basic.Util
module H = Utils
module D = Diff

module SymAst = struct
  type t =
    | SNull
    | SGlob of sym_global * Cil.global
    | SStmt of sym_stmt * Cil.stmt
    | SExp of sym_exp * Cil.exp
    | SLval of sym_lval * Cil.lval

  and sym_typeinfo = { sym_tname : string; sym_ttype : sym_typ }
  and sym_enuminfo = { ename : string; eitems : (string * sym_node) list }

  and sym_typ =
    | SVoid
    | SInt
    | SFloat
    | SPtr of sym_typ
    | SArray of sym_typ
    | SNamed of sym_typeinfo
    | SComp of sym_compinfo
    | SEnum of sym_enuminfo
    | SFun of sym_typ * (string * sym_typ) list option * bool

  and sym_binop =
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

  and sym_unop = SNot | SNeg

  and sym_const =
    | SIntConst of int
    | SFloatConst of float
    | SCharConst of char
    | SStringConst of string

  and sym_offset =
    | SNoOffset
    | SField of sym_fieldinfo * sym_offset
    | SIndex of sym_node * sym_offset

  and sym_compinfo = { cname : string; cstruct : bool }
  and sym_fieldinfo = { fcomp : sym_compinfo; fname : string; ftype : sym_typ }
  and sym_varinfo = { vname : string; vtype : sym_typ }

  and sym_exp =
    | SENULL
    | SConst of sym_const
    | SELval of sym_node
    | SSizeOf of sym_typ
    | SSizeOfE of sym_node
    | SSizeOfStr of string
    | SBinOp of sym_binop * sym_node * sym_node * sym_typ
    | SUnOp of sym_unop * sym_node * sym_typ
    | SQuestion of sym_node * sym_node * sym_node * sym_typ
    | SCastE of sym_typ * sym_node
    | SAddrOf of sym_node
    | SStartOf of sym_node
    | SAddrOfLabel of sym_node

  and sym_lhost = SVar of sym_varinfo | SMem of sym_node
  and sym_lval = SLNull | Lval of sym_lhost * sym_offset

  and sym_stmt =
    | SSNull
    | SIf of sym_node * sym_node list * sym_node list
    | SSet of sym_node * sym_node
    | SCall of sym_node option * sym_node * sym_node list
    | SReturn of sym_node option
    | SBlock of sym_node list
    | SGoto of sym_node
    | SBreak
    | SContinue

  and sym_global = SGNull | SGFun | GVar of string * string
  and sym_node = { node : t; id : string; literal : string }

  let rec pp_node fmt e =
    match e.node with
    | SNull -> Format.fprintf fmt "SNull"
    | SStmt (s, _) -> Format.fprintf fmt "SStmt(%a)" pp_sstmt s
    | SExp (e, _) -> Format.fprintf fmt "SExp(%a)" pp_sexp e
    | SLval (l, _) -> Format.fprintf fmt "SLval(%a)" pp_slval l
    | _ -> failwith "not implemented"

  and pp_node_lst fmt lst =
    Format.fprintf fmt "[";
    List.iter (fun e -> Format.fprintf fmt "%a, " pp_node e) lst;
    Format.fprintf fmt "]"

  and pp_sstmts fmt ss =
    List.iter (fun s -> Format.fprintf fmt "%a; " pp_sstmt s) ss

  and pp_sstmt fmt s =
    match s with
    | SSNull -> Format.fprintf fmt "SSNull"
    | SIf (e, s1, s2) ->
        Format.fprintf fmt "SIf(%a, %a, %a)" pp_node e pp_node_lst s1
          pp_node_lst s2
    | SSet (l, e) -> Format.fprintf fmt "SSet(%a, %a)" pp_node l pp_node e
    | SCall (l, e, es) ->
        Format.fprintf fmt "SCall(%a, %a, %a)" pp_soptlval l pp_node e
          pp_node_lst es
    | SReturn e -> Format.fprintf fmt "SReturn(%a)" pp_soptexp e
    | SBlock b ->
        Format.fprintf fmt "SBlock";
        pp_node_lst fmt b
    | SGoto s -> Format.fprintf fmt "SGoto(%a)" pp_node s
    | SBreak -> Format.fprintf fmt "SBreak"
    | SContinue -> Format.fprintf fmt "SContinue"

  and pp_soptlval fmt l =
    match l with None -> Format.fprintf fmt "None" | Some l -> pp_node fmt l

  and pp_svarinfo fmt v =
    Format.fprintf fmt "SVarInfo(%s, %a)" v.vname pp_styp v.vtype

  and pp_slval fmt l =
    match l with
    | SLNull -> Format.fprintf fmt "SLNull"
    | Lval (lhost, _) -> (
        match lhost with
        | SVar v -> Format.fprintf fmt "LVar(%a)" pp_svarinfo v
        | SMem e -> Format.fprintf fmt "LMem(%a)" pp_node e)

  and pp_soptexp fmt e =
    match e with None -> Format.fprintf fmt "None" | Some e -> pp_node fmt e

  and pp_sexp fmt e =
    match e with
    | SENULL -> Format.fprintf fmt "SENULL"
    | SConst c -> Format.fprintf fmt "SConst(%a)" pp_sconst c
    | SELval l -> Format.fprintf fmt "SELval(%a)" pp_node l
    | SSizeOf t -> Format.fprintf fmt "SSizeOf(%a)" pp_styp t
    | SSizeOfE e -> Format.fprintf fmt "SSizeOfE(%a)" pp_node e
    | SSizeOfStr s -> Format.fprintf fmt "SSizeOfStr(%s)" s
    | SBinOp (op, e1, e2, t) ->
        Format.fprintf fmt "SBinOp(%a, %a, %a, %a)" pp_sbinop op pp_node e1
          pp_node e2 pp_styp t
    | SUnOp (op, e, t) ->
        Format.fprintf fmt "SUnOp(%a, %a, %a)" pp_sunop op pp_node e pp_styp t
    | SQuestion (e1, e2, e3, t) ->
        Format.fprintf fmt "SQuestion(%a, %a, %a, %a)" pp_node e1 pp_node e2
          pp_styp t pp_node e3
    | SCastE (t, e) -> Format.fprintf fmt "SCastE(%a, %a)" pp_styp t pp_node e
    | SAddrOf e -> Format.fprintf fmt "SAddrOf(%a)" pp_node e
    | SStartOf e -> Format.fprintf fmt "SStartOf(%a)" pp_node e
    | SAddrOfLabel e -> Format.fprintf fmt "SAddrOfLabel(%a)" pp_node e

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
    | SArray t -> Format.fprintf fmt "SArray(%a)" pp_styp t
    | SNamed t -> Format.fprintf fmt "SNamed(%a)" pp_styp t.sym_ttype
    | SComp c -> Format.fprintf fmt "SComp(%a)" pp_scompinfo c
    | SEnum e -> Format.fprintf fmt "SEnum(%a)" pp_senuminfo e
    | SFun (t, lst, b) ->
        Format.fprintf fmt "SFun(%a, %a, %b)" pp_styp t pp_sfunargs lst b

  and pp_sfunargs fmt lst =
    match lst with
    | None -> Format.fprintf fmt "None"
    | Some lst ->
        Format.fprintf fmt "[";
        List.iter
          (fun (s, t) -> Format.fprintf fmt "(%s, %a), " s pp_styp t)
          lst;
        Format.fprintf fmt "]"

  and pp_senuminfo fmt e =
    Format.fprintf fmt "SEnumInfo(%s, %a)" e.ename pp_senumitem_lst e.eitems

  and pp_senumitem_lst fmt lst =
    Format.fprintf fmt "[";
    List.iter (fun (s, n) -> Format.fprintf fmt "(%s, %a), " s pp_node n) lst;
    Format.fprintf fmt "]"

  and pp_scompinfo fmt c =
    Format.fprintf fmt "SCompInfo(%s, %b)" c.cname c.cstruct

  and pp_sfieldinfo_lst fmt lst =
    Format.fprintf fmt "[";
    List.iter (fun f -> Format.fprintf fmt "%a, " pp_sfieldinfo f) lst;
    Format.fprintf fmt "]"

  and pp_sfieldinfo fmt f =
    Format.fprintf fmt "SFieldInfo(%a, %s, %a)" pp_scompinfo f.fcomp f.fname
      pp_styp f.ftype

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
  let compare = compare
end

include SymAst

type sym_context = {
  root_path : sym_node list;
  parent_of_patch : sym_node;
  patch_between : string list * string list;
  func_name : string;
  sibling_idx : int;
}

type t =
  | SInsertStmt of sym_context * sym_node
  | SDeleteStmt of sym_context * sym_node
  | SInsertExp of sym_context * sym_node
  | SDeleteExp of sym_context * sym_node
  | SUpdateExp of sym_context * sym_node * sym_node
  | SInsertLval of sym_context * sym_node
  | SDeleteLval of sym_context * sym_node
  | SUpdateLval of sym_context * sym_node * sym_node

let get_ctx = function
  | SInsertStmt (ctx, _)
  | SDeleteStmt (ctx, _)
  | SInsertExp (ctx, _)
  | SDeleteExp (ctx, _)
  | SUpdateExp (ctx, _, _)
  | SInsertLval (ctx, _)
  | SDeleteLval (ctx, _)
  | SUpdateLval (ctx, _, _) ->
      ctx

let extract_func_name sdiff =
  match sdiff with
  | SInsertStmt (ctx, _) | SDeleteStmt (ctx, _) -> ctx.func_name
  | SInsertExp (ctx, _) | SDeleteExp (ctx, _) | SUpdateExp (ctx, _, _) ->
      ctx.func_name
  | SInsertLval (ctx, _) | SDeleteLval (ctx, _) | SUpdateLval (ctx, _, _) ->
      ctx.func_name

let extract_context sdiff =
  match sdiff with
  | SInsertStmt (ctx, _) | SDeleteStmt (ctx, _) -> ctx
  | SInsertExp (ctx, _) | SDeleteExp (ctx, _) | SUpdateExp (ctx, _, _) -> ctx
  | SInsertLval (ctx, _) | SDeleteLval (ctx, _) | SUpdateLval (ctx, _, _) -> ctx

let rec mk_sdiff ctx maps diff =
  let exp_map = maps.Maps.exp_map |> Utils.reverse_hashtbl in
  let cfg = maps.cfg_map in
  match diff with
  | D.InsertStmt (_, s) -> SInsertStmt (ctx, mk_stmt cfg exp_map s)
  | D.DeleteStmt (_, s) -> SDeleteStmt (ctx, mk_stmt cfg exp_map s)
  | D.UpdateExp (_, e1, e2) ->
      SUpdateExp (ctx, mk_exp cfg exp_map e1, mk_exp cfg exp_map e2)
  | _ -> failwith "mk_sdiff: not implemented"

and mk_exp cfg exp_map e =
  {
    node = SExp (match_exp cfg exp_map e, e);
    id = match_exp_id exp_map e;
    literal = Ast.s_exp e;
  }

and mk_lval cfg exp_map l =
  {
    node = SLval (match_lval cfg exp_map l, l);
    id = match_lval_id exp_map l;
    literal = Ast.s_lv l;
  }

and mk_exps cfg exp_map exps = List.map (fun e -> mk_exp cfg exp_map e) exps

and mk_stmt cfg exp_map s =
  {
    node = SStmt (match_stmt cfg exp_map s, s);
    id = match_stmt_id cfg s.Cil.skind;
    literal = Ast.s_stmt s;
  }

and mk_stmts cfg exp_map stmts = List.map (fun s -> mk_stmt cfg exp_map s) stmts

and match_instr cfg exp_map i =
  let i = List.hd i in
  match i with
  | Cil.Set (l, e, _) ->
      SymAst.SSet (mk_lval cfg exp_map l, mk_exp cfg exp_map e)
  | Cil.Call (Some l, e, es, _) ->
      SymAst.SCall
        ( Some (mk_lval cfg exp_map l),
          mk_exp cfg exp_map e,
          mk_exps cfg exp_map es )
  | Cil.Call (None, e, es, _) ->
      SymAst.SCall (None, mk_exp cfg exp_map e, mk_exps cfg exp_map es)
  | _ -> failwith "match_stmt: not supported"

and match_stmt cfg exp_map s =
  match s.Cil.skind with
  | Cil.If (e, s1, s2, _) ->
      let node = SExp (match_exp cfg exp_map e, e) in
      let id = match_exp_id exp_map e in
      let literal = Ast.s_exp e in
      SymAst.SIf
        ( { node; id; literal },
          mk_stmts cfg exp_map s1.Cil.bstmts,
          mk_stmts cfg exp_map s2.Cil.bstmts )
  | Cil.Instr i -> match_instr cfg exp_map i
  | Cil.Block b ->
      let bl =
        List.fold_left
          (fun (acc : SymAst.sym_node list) s -> mk_stmt cfg exp_map s :: acc)
          [] b.bstmts
        |> List.rev
      in
      SymAst.SBlock bl
  | Cil.Return (Some e, _) ->
      let node = SExp (match_exp cfg exp_map e, e) in
      let id = match_exp_id exp_map e in
      let literal = Ast.s_exp e in
      SymAst.SReturn (Some { node; id; literal })
  | Cil.Return (None, _) -> SymAst.SReturn None
  | Cil.Goto (s, _) ->
      let node = SStmt (SSNull, !s) in
      let id = "GOTO_DST" in
      let literal = Ast.s_stmt !s in
      SymAst.SGoto { node; id; literal }
  | Cil.Break _ -> SymAst.SBreak
  | Cil.Continue _ -> SymAst.SContinue
  | _ -> failwith "match_stmt: not implemented"

and mk_sexp cfg exp_map e =
  let node = SExp (match_exp cfg exp_map e, e) in
  let id = match_exp_id exp_map e in
  let literal = Ast.s_exp e in
  { node; id; literal }

and match_exp cfg exp_map e =
  match e with
  | Cil.Const c -> SymAst.SConst (to_sconst c)
  | Cil.Lval l ->
      let node = SLval (match_lval cfg exp_map l, l) in
      let id = match_lval_id exp_map l in
      let literal = Ast.s_lv l in
      SELval { node; id; literal }
  | Cil.SizeOf t -> SSizeOf (to_styp t)
  | Cil.SizeOfE e' ->
      let node = SExp (match_exp cfg exp_map e', e') in
      let id = match_exp_id exp_map e' in
      let literal = Ast.s_exp e' in
      SSizeOfE { node; id; literal }
  | Cil.SizeOfStr s -> SSizeOfStr s
  | Cil.BinOp (op, e1, e2, t) ->
      SBinOp
        (to_sbinop op, mk_sexp cfg exp_map e1, mk_sexp cfg exp_map e2, to_styp t)
  | Cil.UnOp (op, e, t) ->
      let node = SExp (match_exp cfg exp_map e, e) in
      let id = match_exp_id exp_map e in
      let literal = Ast.s_exp e in
      SUnOp (to_sunop op, { node; id; literal }, to_styp t)
  | Cil.CastE (t, e) ->
      let node = SExp (match_exp cfg exp_map e, e) in
      let id = match_exp_id exp_map e in
      let literal = Ast.s_exp e in
      SCastE (to_styp t, { node; id; literal })
  | Cil.Question (e1, e2, e3, t) ->
      SQuestion
        ( mk_sexp cfg exp_map e1,
          mk_sexp cfg exp_map e2,
          mk_sexp cfg exp_map e3,
          to_styp t )
  | Cil.AddrOf l ->
      let node = SLval (match_lval cfg exp_map l, l) in
      let id = match_lval_id exp_map l in
      let literal = Ast.s_lv l in
      SAddrOf { node; id; literal }
  | Cil.StartOf l ->
      let node = SLval (match_lval cfg exp_map l, l) in
      let id = match_lval_id exp_map l in
      let literal = Ast.s_lv l in
      SStartOf { node; id; literal }
  | Cil.AddrOfLabel stmt ->
      let node = SStmt (match_stmt cfg exp_map !stmt, !stmt) in
      let id = match_stmt_id cfg !stmt.Cil.skind in
      let literal = Ast.s_stmt !stmt in
      SAddrOfLabel { node; id; literal }
  | _ -> failwith "match_exp: not implemented"

and match_lval cfg exp_map l =
  let lhost, offset = l in
  let slhost =
    match lhost with
    | Cil.Var v -> SymAst.SVar { vname = v.vname; vtype = to_styp v.vtype }
    | Cil.Mem e ->
        let node = SExp (match_exp cfg exp_map e, e) in
        let id = match_exp_id exp_map e in
        let literal = Ast.s_exp e in
        SymAst.SMem { node; id; literal }
  in
  let soffset = match_offset cfg exp_map offset in
  Lval (slhost, soffset)

and match_offset cfg exp_map o =
  match o with
  | Cil.NoOffset -> SymAst.SNoOffset
  | Cil.Field (f, o) ->
      let fcomp = { cname = f.fcomp.cname; cstruct = true } in
      let fname = f.fname in
      let ftype = to_styp f.ftype in
      SymAst.SField ({ fcomp; fname; ftype }, match_offset cfg exp_map o)
  | Cil.Index (e, o) ->
      let node = SExp (match_exp cfg exp_map e, e) in
      let id = match_exp_id exp_map e in
      let literal = Ast.s_exp e in
      SymAst.SIndex ({ node; id; literal }, match_offset cfg exp_map o)

and match_fieldinfo f =
  {
    SymAst.fcomp = match_compinfo f.Cil.fcomp;
    SymAst.fname = f.Cil.fname;
    SymAst.ftype = to_styp f.Cil.ftype;
  }

and match_compinfo c =
  { SymAst.cname = c.Cil.cname; SymAst.cstruct = c.Cil.cstruct }

and extract_fun_name g =
  match g with
  | Cil.GFun (f, _) -> f.Cil.svar.Cil.vname
  | _ -> failwith "extract_fun_name: not a function"

and match_ast_path cfg exp_map lst =
  match lst with
  | [] -> []
  | hd :: tl -> (
      match hd with
      | Ast.Stmt s ->
          let id = match_stmt_id cfg s.Cil.skind in
          let node = SStmt (SSNull, s) in
          let literal = Ast.s_stmt s in
          { id; node; literal } :: match_ast_path cfg exp_map tl
      | Ast.Exp e ->
          let id = match_exp_id exp_map e in
          let node = SExp (SENULL, e) in
          let literal = Ast.s_exp e in
          { id; node; literal } :: match_ast_path cfg exp_map tl
      | Ast.Lval l ->
          let id = match_lval_id exp_map l in
          let node = SLval (SLNull, l) in
          let literal = Ast.s_lv l in
          { id; node; literal } :: match_ast_path cfg exp_map tl
      | Ast.Global g ->
          let id = extract_fun_name g in
          let node = SGlob (SGNull, g) in
          let literal = Ast.s_glob g in
          { id; node; literal } :: match_ast_path cfg exp_map tl
      | _ -> failwith "match_context: context failed to be read")

and match_exp_id exp_map e =
  let candidate =
    match e with
    | Cil.Const c -> match_const c exp_map
    | Cil.Lval l -> Ast.s_lv l |> Hashtbl.find_opt exp_map
    | Cil.SizeOf t -> match_sizeof t exp_map
    | Cil.SizeOfE _ | Cil.BinOp _ | Cil.UnOp _ | Cil.CastE _ | Cil.Question _ ->
        Ast.s_exp e |> Hashtbl.find_opt exp_map
    | _ -> failwith "match_exp: not implemented"
  in
  if Option.is_none candidate then "None" else Option.get candidate

and match_sizeof t exp_map = Ast.s_type t |> Hashtbl.find_opt exp_map

and match_lval_id exp_map l =
  let candidate = Hashtbl.find_opt exp_map (Ast.s_lv l) in
  if Option.is_none candidate then "None" else Option.get candidate

and eq_line loc cloc =
  let file_name = loc.Cil.file |> Filename.basename in
  if loc.Cil.line = cloc.Maps.CfgNode.line && file_name = cloc.file then true
  else false

and match_set_id cfg loc =
  Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CSet (_, _, cloc, _)
      | Maps.CfgNode.CAlloc (_, _, cloc, _)
      | Maps.CfgNode.CFalloc (_, _, cloc, _)
      | Maps.CfgNode.CSalloc (_, _, cloc, _) ->
          if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

and match_call_id cfg loc =
  Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CCall (_, _, cloc, _) ->
          if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

and match_return_id cfg loc =
  Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CReturn1 (_, cloc, _) ->
          if eq_line loc cloc then v :: acc else acc
      | Maps.CfgNode.CReturn2 cloc -> if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

and match_assume_id cfg loc cond =
  Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CAssume (_, ccond, cloc) ->
          if eq_line loc cloc && Ast.s_exp cond |> H.subset ccond then v :: acc
          else acc
      | _ -> acc)
    cfg []

and match_loop_id cfg loc =
  Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CSkip cloc -> if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

and match_stmt_id cfg s =
  (*TODO: tighten the string match of stmt by subset*)
  match s with
  | Cil.Instr i -> (
      let instr = List.hd i in
      match instr with
      | Cil.Set (_, _, loc) ->
          let matched = match_set_id cfg loc in
          if List.length matched >= 1 then List.hd matched else "None"
      | Cil.Call (_, _, _, loc) ->
          let matched = match_call_id cfg loc in
          if List.length matched >= 1 then List.hd matched else "None"
      | _ -> failwith "unexpected")
  | Cil.Return (_, loc) ->
      let matched = match_return_id cfg loc in
      if List.length matched >= 1 then List.hd matched else "None"
  | Cil.If (cond, _, _, loc) ->
      let matched = match_assume_id cfg loc cond in
      if List.length matched >= 1 then List.hd matched else "None"
  | Cil.Loop (_, loc, _, _) ->
      let matched = match_loop_id cfg loc in
      if List.length matched >= 1 then List.hd matched else "None"
  | _ -> "None"

and match_const c exp_map = Ast.s_const c |> Hashtbl.find_opt exp_map

and to_styp t =
  match t with
  | Cil.TVoid _ -> SVoid
  | Cil.TInt _ -> SInt
  | Cil.TFloat _ -> SFloat
  | Cil.TPtr (t', _) -> SPtr (to_styp t')
  | Cil.TArray (t', _, _) -> SArray (to_styp t')
  | Cil.TNamed (t', _) ->
      SNamed { sym_tname = t'.Cil.tname; sym_ttype = to_styp t'.ttype }
  | Cil.TFun (t, lst, b, _) ->
      let slist =
        match lst with
        | Some lst -> Some (List.map (fun (s, ty, _) -> (s, to_styp ty)) lst)
        | None -> None
      in
      SFun (to_styp t, slist, b)
  | Cil.TComp (c, _) -> SComp (to_scompinfo c)
  | Cil.TEnum _ -> failwith "TEnum: not implemented"
  | Cil.TBuiltin_va_list _ -> failwith "not supported"

and to_scompinfo c = { cname = c.Cil.cname; cstruct = c.cstruct }

and to_sfieldinfo f =
  { fcomp = to_scompinfo f.Cil.fcomp; fname = f.fname; ftype = to_styp f.ftype }

and to_sbinop op =
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

and to_binop sop =
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

and to_unop sop = match sop with SNot -> Cil.LNot | SNeg -> Cil.Neg

and to_sunop op =
  match op with
  | Cil.LNot -> SNot
  | Cil.Neg -> SNeg
  | _ -> failwith "not supported"

and to_sconst c =
  match c with
  | Cil.CInt64 (i, _, _) -> SIntConst (Int64.to_int i)
  | Cil.CReal (f, _, _) -> SFloatConst f
  | Cil.CChr c -> SCharConst c
  | Cil.CStr s -> SStringConst s
  | _ -> failwith "not supported"

let get_parent_fun parent_lst =
  let check_fun g = match g with Cil.GFun _ -> true | _ -> false in
  let get_fun g =
    match g with
    | Cil.GFun _ -> g
    | _ -> failwith "get_parent_fun: not a function"
  in
  let parent_fun_cand =
    List.fold_left
      (fun acc e ->
        match e with
        | Ast.Global g -> if check_fun g then get_fun g :: acc else acc
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

let get_patch_range siblings patch_loc node_map ast_map =
  if patch_loc = -1 then ([], [])
  else
    let before, after =
      List.fold_left
        (fun ((bf, af), cnt) s ->
          if cnt < patch_loc then ((s :: bf, af), cnt + 1)
          else ((bf, s :: af), cnt + 1))
        (([], []), 0)
        siblings
      |> fst
    in
    let left_lim =
      if patch_loc = 0 then []
      else
        List.fold_left
          (fun acc s ->
            try (Hashtbl.find ast_map s |> string_of_int) :: acc with _ -> acc)
          [] before
        |> List.fold_left
             (fun acc s -> try Hashtbl.find node_map s :: acc with _ -> acc)
             []
    in
    let right_lim =
      List.fold_left
        (fun acc s ->
          try (Hashtbl.find ast_map s |> string_of_int) :: acc with _ -> acc)
        [] after
      |> List.fold_left
           (fun acc s -> try Hashtbl.find node_map s :: acc with _ -> acc)
           []
    in
    (left_lim, right_lim)

let get_sibling_lst patch_node parent_branch =
  match patch_node.node with
  | SStmt (_, s) -> (
      match s.Cil.skind with
      | Cil.Block lst -> lst.bstmts
      | Cil.Loop (b, _, _, _) -> b.bstmts
      | Cil.If (_, tb, eb, _) -> (
          match parent_branch with
          | D.TrueBranch -> tb.bstmts
          | FalseBranch -> eb.bstmts
          | _ -> failwith "get_sibling_lst: if statment without branch")
      | _ -> [])
  | SGlob (_, g) -> (
      match g with
      | Cil.GFun (f, _) -> f.sbody.bstmts
      | _ -> failwith "define_sym_diff: not implemented")
  | _ -> failwith "define_sym_diff: not implemented"

let rec extract_node_ids node =
  match node.node with
  | SStmt (s, _) -> node.id :: extract_stmt_ids s
  | SGlob _ -> [ node.id ]
  | SExp (e, _) -> node.id :: extract_exp_ids e
  | SLval (l, _) -> node.id :: extract_lval_ids l
  | _ -> []

and extract_stmt_ids (stmt : sym_stmt) =
  match stmt with
  | SBlock lst -> List.fold_left (fun acc s -> extract_node_ids s @ acc) [] lst
  | SSet (l, e) -> extract_node_ids l @ extract_node_ids e
  | SCall (Some l, e, es) ->
      extract_node_ids l @ extract_node_ids e
      @ List.fold_left (fun acc e -> extract_node_ids e @ acc) [] es
  | SCall (None, e, es) ->
      extract_node_ids e
      @ List.fold_left (fun acc e -> extract_node_ids e @ acc) [] es
  | SReturn (Some e) -> extract_node_ids e
  | SReturn None -> []
  | SIf (e, s1, s2) ->
      extract_node_ids e
      @ List.fold_left (fun acc s -> extract_node_ids s @ acc) [] s1
      @ List.fold_left (fun acc s -> extract_node_ids s @ acc) [] s2
  | SGoto s -> extract_node_ids s
  | _ -> []

and extract_exp_ids (exp : sym_exp) =
  match exp with
  | SELval l -> extract_node_ids l
  | SConst _ -> []
  | SSizeOf _ -> []
  | SSizeOfE e -> extract_node_ids e
  | SBinOp (_, e1, e2, _) -> extract_node_ids e1 @ extract_node_ids e2
  | SUnOp (_, e, _) -> extract_node_ids e
  | SCastE (_, e) -> extract_node_ids e
  | SQuestion (e1, e2, e3, _) ->
      extract_node_ids e1 @ extract_node_ids e2 @ extract_node_ids e3
  | SAddrOf l -> extract_node_ids l
  | SStartOf l -> extract_node_ids l
  | SAddrOfLabel s -> extract_node_ids s
  | _ -> []

and extract_lval_ids (lval : sym_lval) =
  match lval with
  | Lval (l, o) -> extract_lhost_ids l @ extract_offset_ids o
  | _ -> []

and extract_lhost_ids (lhost : sym_lhost) =
  match lhost with SVar _ -> [] | SMem e -> extract_node_ids e

and extract_offset_ids (offset : sym_offset) =
  match offset with
  | SNoOffset -> []
  | SField (_, o) -> extract_offset_ids o
  | SIndex (e, o) -> extract_node_ids e @ extract_offset_ids o

let extract_diff_ids sdiff =
  match sdiff with
  | SInsertStmt (_, n)
  | SDeleteStmt (_, n)
  | SInsertExp (_, n)
  | SDeleteExp (_, n)
  | SInsertLval (_, n)
  | SDeleteLval (_, n) ->
      extract_node_ids n
  | SUpdateExp (_, n1, n2) | SUpdateLval (_, n1, n2) ->
      extract_node_ids n1 @ extract_node_ids n2

let symbolize_sibs sibs =
  List.fold_left (fun acc s -> s.id :: acc) [] sibs |> List.rev

let filter_nodes du_facts nodes =
  List.fold_left
    (fun acc n -> if List.mem n du_facts then n :: acc else acc)
    [] nodes
  |> List.rev

let mk_s_sibs maps exp_map path facts =
  let facts_lst = Chc.to_list facts in
  match_ast_path maps.cfg_map exp_map path
  |> symbolize_sibs
  |> filter_nodes (Chc.extract_nodes_in_facts facts_lst maps.Maps.node_map)

let mk_sym_ctx ctx env maps cf_facts =
  let exp_map = maps.Maps.exp_map |> Utils.reverse_hashtbl in
  let cfg_map = maps.cfg_map in
  let root_path = List.rev ctx.D.root_path in
  let s_root_path = match_ast_path cfg_map exp_map root_path in
  let left_sibs, right_sibs = ctx.patch_between in
  let s_left_sibs = mk_s_sibs maps exp_map left_sibs cf_facts in
  let s_right_sibs = mk_s_sibs maps exp_map right_sibs cf_facts in
  let rest_path = List.tl s_root_path in
  let prnt_fun = get_parent_fun root_path in
  let patch_node =
    try List.rev rest_path |> List.hd
    with Failure _ ->
      { node = SGlob (SGFun, prnt_fun); id = "None"; literal = "None" }
  in
  {
    root_path = rest_path;
    parent_of_patch = patch_node;
    patch_between = (s_left_sibs, s_right_sibs);
    func_name = env.D.top_func_name;
    sibling_idx = ctx.D.sibling_idx;
  }

let extract_ctx_nodes sdiff =
  List.fold_left
    (fun acc sd ->
      let ctx = get_ctx sd in
      let b, a = ctx.patch_between in
      b @ a @ acc)
    [] sdiff

let define_sym_diff (maps : Maps.t) buggy diff cf_facts =
  get_gvars buggy;
  let sdiff =
    List.fold_left
      (fun acc (action, env) ->
        let ctx = D.get_ctx action in
        let s_context = mk_sym_ctx ctx env maps cf_facts in
        mk_sdiff s_context maps action :: acc)
      [] diff
  in
  let patch_comp =
    extract_ctx_nodes sdiff
    |> List.append
         (List.fold_left (fun acc d -> extract_diff_ids d @ acc) [] sdiff)
    |> List.sort_uniq Stdlib.compare
    |> List.filter (fun x -> x <> "None")
  in
  (sdiff, patch_comp)

module DiffJson = struct
  open SymAst

  type t = Yojson.Safe.t

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
    | SVoid -> `String "void"
    | SInt -> `String "int"
    | SFloat -> `String "float"
    | SPtr t -> `Assoc [ ("ptr", styp_to_sym t) ]
    | SArray t -> `Assoc [ ("array", styp_to_sym t) ]
    | SNamed t ->
        let tname_json = ("tname", `String t.sym_tname) in
        let typ_json = ("typ", styp_to_sym t.sym_ttype) in
        `Assoc [ ("named", `Assoc [ tname_json; typ_json ]) ]
    | SFun (t, lst, b) ->
        let slist = match lst with Some lst -> lst | None -> [] in
        let typ_json = ("typ", styp_to_sym t) in
        let args_lst =
          List.fold_left
            (fun acc (s, ty) -> `String s :: styp_to_sym ty :: acc)
            [] slist
          |> List.rev
        in
        let args_json = ("args", `List args_lst) in
        let body_json = ("body", `Bool b) in
        `Assoc [ ("fun", `Assoc [ typ_json; args_json; body_json ]) ]
    | SComp c ->
        let cname_json = ("cname", `String c.cname) in
        let struct_json = ("struct", `Bool c.cstruct) in
        let comp_json = ("comp", `Assoc [ cname_json; struct_json ]) in
        `Assoc [ comp_json ]
    | _ -> failwith "styp_to_sym: not implemented"

  let sunop_to_sym op = match op with SNot -> "LNot" | SNeg -> "Neg"

  let rec mk_json_obj saction =
    let context_json (context : sym_context) =
      let func_name_json = ("func_name", `String context.func_name) in
      let sid_lst =
        `List
          (List.fold_left
             (fun acc node -> `String node.id :: acc)
             [] context.root_path)
      in
      let parent_json = ("parent", sid_lst) in
      ("context", `Assoc [ func_name_json; parent_json ])
    in
    match saction with
    | SInsertStmt (context1, snode) ->
        let action_json = ("action", `String "insert_stmt") in
        let ctx_json = context_json context1 in
        let change_json = ("change", sstmt_to_json snode) in
        `Assoc [ action_json; ctx_json; change_json ]
    | SDeleteStmt (context1, snode) ->
        let action_json = ("action", `String "delete_stmt") in
        let ctx_json = context_json context1 in
        let change_json = ("change", sstmt_to_json snode) in
        `Assoc [ action_json; ctx_json; change_json ]
    | SUpdateExp (context1, e1, e2) ->
        let action_json = ("action", `String "update_exp") in
        let ctx_json = context_json context1 in
        let change_json =
          ( "change",
            `Assoc [ ("before", sexp_to_json e1); ("after", sexp_to_json e2) ]
          )
        in
        `Assoc [ action_json; ctx_json; change_json ]
    | _ -> failwith "mk_json_obj: not implemented"

  and sexps_to_json lst =
    `List
      (List.fold_left (fun acc x -> sexp_to_json x :: acc) [] lst |> List.rev)

  and sstmts_to_json lst =
    `List
      (List.fold_left (fun acc x -> sstmt_to_json x :: acc) [] lst |> List.rev)

  and sstmt_to_json (sstmt : sym_node) =
    let node = sstmt.node in
    let stmt =
      match node with
      | SStmt (s, _) -> s
      | _ -> failwith "sstmt_to_json: undefined sstmt"
    in
    match stmt with
    | SIf (exp1, tb1, eb1) ->
        let cond_json = ("cond", sexp_to_json exp1) in
        let then_json = ("then", sstmts_to_json tb1) in
        let else_json = ("else", sstmts_to_json eb1) in
        let node_json = ("node", `Assoc [ cond_json; then_json; else_json ]) in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let if_json = ("if", `Assoc [ node_json; id_json; literal_json ]) in
        `Assoc [ if_json ]
    | SSet (lv1, e1) ->
        let lval_json = ("lval", slval_to_json lv1) in
        let exp_json = ("exp", sexp_to_json e1) in
        let node_json = ("node", `Assoc [ lval_json; exp_json ]) in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let set_json = ("set", `Assoc [ node_json; id_json; literal_json ]) in
        `Assoc [ set_json ]
    | SCall (Some lv1, e1, es1) ->
        let lval_json = ("lval", slval_to_json lv1) in
        let exp_json = ("exp", sexp_to_json e1) in
        let exps_json = ("exps", sexps_to_json es1) in
        let node_json = ("node", `Assoc [ lval_json; exp_json; exps_json ]) in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let call_json = ("call", `Assoc [ node_json; id_json; literal_json ]) in
        `Assoc [ call_json ]
    | SCall (None, e1, es1) ->
        let lval_json = ("lval", `String "None") in
        let exp_json = ("exp", sexp_to_json e1) in
        let exps_json = ("exps", sexps_to_json es1) in
        let node_json = ("node", `Assoc [ lval_json; exp_json; exps_json ]) in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let call_json = ("call", `Assoc [ node_json; id_json; literal_json ]) in
        `Assoc [ call_json ]
    | SReturn (Some e1) ->
        let exp_json = ("exp", sexp_to_json e1) in
        let node_json = ("node", `Assoc [ exp_json ]) in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let return_json =
          ("return", `Assoc [ node_json; id_json; literal_json ])
        in
        `Assoc [ return_json ]
    | SReturn None ->
        let exp_json = ("exp", `String "None") in
        let node_json = ("node", `Assoc [ exp_json ]) in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let return_json =
          ("return", `Assoc [ node_json; id_json; literal_json ])
        in
        `Assoc [ return_json ]
    | SGoto s1 ->
        let stmt_json = ("stmt", sstmt_to_json s1) in
        let node_json = ("node", `Assoc [ stmt_json ]) in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let goto_json = ("goto", `Assoc [ node_json; id_json; literal_json ]) in
        `Assoc [ goto_json ]
    | SBreak ->
        let node_json = ("node", `String "break") in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let break_json =
          ("break", `Assoc [ node_json; id_json; literal_json ])
        in
        `Assoc [ break_json ]
    | SContinue ->
        let node_json = ("node", `String "continue") in
        let id_json = ("id", `String sstmt.id) in
        let literal_json = ("literal", `String sstmt.literal) in
        let continue_json =
          ("continue", `Assoc [ node_json; id_json; literal_json ])
        in
        `Assoc [ continue_json ]
    | _ -> `Null

  and sexp_to_json (sexp : SymAst.sym_node) =
    let node = sexp.node in
    let exp =
      match node with
      | SExp (e, _) -> e
      | _ -> failwith "sexp_to_json: undefined sexp"
    in
    match exp with
    | SConst const ->
        let const_json = ("const", sconst_to_json const) in
        let node_json = ("node", `Assoc [ const_json ]) in
        let id_json = ("id", `String sexp.id) in
        let literal_json = ("literal", `String sexp.literal) in
        `Assoc [ node_json; id_json; literal_json ]
    | SELval l -> `Assoc [ ("lval", slval_to_json l) ]
    | SSizeOfE e1 ->
        let e_json = ("exp", sexp_to_json e1) in
        let sizeof_json = ("sizeof", `Assoc [ e_json ]) in
        let node_json = ("node", `Assoc [ sizeof_json ]) in
        let id_json = ("id", `String sexp.id) in
        let literal_json = ("literal", `String sexp.literal) in
        `Assoc [ node_json; id_json; literal_json ]
    | SBinOp (op1, e1_1, e2_1, typ1) ->
        let op_json = ("op", `String (sbinop_to_sym op1)) in
        let typ_json = ("typ", styp_to_sym typ1) in
        let e1_json = ("e1", sexp_to_json e1_1) in
        let e2_json = ("e2", sexp_to_json e2_1) in
        let binop_json =
          ("binop", `Assoc [ op_json; typ_json; e1_json; e2_json ])
        in
        let node_json = ("node", `Assoc [ binop_json ]) in
        let id_json = ("id", `String sexp.id) in
        let literal_json = ("literal", `String sexp.literal) in
        `Assoc [ node_json; id_json; literal_json ]
    | SCastE (typ, e1) ->
        let typ_json = ("typ", styp_to_sym typ) in
        let e_json = ("e", sexp_to_json e1) in
        let cast_json = ("cast", `Assoc [ typ_json; e_json ]) in
        let node_json = ("node", `Assoc [ cast_json ]) in
        let id_json = ("id", `String sexp.id) in
        let literal_json = ("literal", `String sexp.literal) in
        `Assoc [ node_json; id_json; literal_json ]
    | SUnOp (op1, e1_1, typ1) ->
        let op_json = ("op", `String (sunop_to_sym op1)) in
        let typ_json = ("typ", styp_to_sym typ1) in
        let e_json = ("e", sexp_to_json e1_1) in
        let unop_json = ("unop", `Assoc [ op_json; typ_json; e_json ]) in
        let node_json = ("node", `Assoc [ unop_json ]) in
        let id_json = ("id", `String sexp.id) in
        let literal_json = ("literal", `String sexp.literal) in
        `Assoc [ node_json; id_json; literal_json ]
    | _ ->
        SymAst.pp_sexp Format.std_formatter exp;
        failwith "sexp_to_json: undefined sexp"

  and slval_to_json (slval : SymAst.sym_node) =
    let node = slval.node in
    let lval =
      match node with
      | SLval (l, _) -> l
      | _ -> failwith "slval_to_json: undefined slval"
    in
    match lval with
    | SLNull -> `Null
    | Lval (lhost, offset) ->
        let lhost_json = ("lhost", slhost_to_json lhost) in
        let offset_json = ("offset", soffset_to_json offset) in
        let lval_json = ("lval", `Assoc [ lhost_json; offset_json ]) in
        let node_json = ("node", `Assoc [ lval_json ]) in
        let id_json = ("id", `String slval.id) in
        let literal_json = ("literal", `String slval.literal) in
        `Assoc [ node_json; id_json; literal_json ]

  and slhost_to_json lhost =
    match lhost with
    | SVar v ->
        let name_json = ("name", `String v.vname) in
        let typ_json = ("typ", styp_to_sym v.vtype) in
        `Assoc [ ("var", `Assoc [ name_json; typ_json ]) ]
    | SMem e -> `Assoc [ ("mem", `Assoc [ ("exp", sexp_to_json e) ]) ]

  and soffset_to_json offset =
    match offset with
    | SNoOffset -> `String "nooffset"
    | SField (f, o) ->
        let field_json = ("field", sfield_to_json f) in
        let offset_json = ("offset", soffset_to_json o) in
        `Assoc [ ("field", `Assoc [ field_json; offset_json ]) ]
    | SIndex (e, o) ->
        let exp_json = ("exp", sexp_to_json e) in
        let offset_json = ("offset", soffset_to_json o) in
        `Assoc [ ("index", `Assoc [ exp_json; offset_json ]) ]

  and sfield_to_json f =
    let comp_json = ("comp", scomp_to_json f.fcomp) in
    let name_json = ("name", `String f.fname) in
    let typ_json = ("typ", styp_to_sym f.ftype) in
    `Assoc [ ("field", `Assoc [ comp_json; name_json; typ_json ]) ]

  and scomp_to_json c =
    let name_json = ("name", `String c.cname) in
    let struct_json = ("struct", `Bool c.cstruct) in
    `Assoc [ ("comp", `Assoc [ name_json; struct_json ]) ]

  and sconst_to_json (sconst : SymAst.sym_const) =
    match sconst with
    | SIntConst i ->
        let type_json = ("type", `String "int") in
        let literal_json = ("literal", `String (Int.to_string i)) in
        `Assoc [ type_json; literal_json ]
    | SFloatConst f ->
        let type_json = ("type", `String "float") in
        let literal_json = ("literal", `String (Float.to_string f)) in
        `Assoc [ type_json; literal_json ]
    | SStringConst s ->
        let type_json = ("type", `String "str") in
        let literal_json = ("literal", `String s) in
        `Assoc [ type_json; literal_json ]
    | SCharConst c ->
        let type_json = ("type", `String "char") in
        let literal_json = ("literal", `String (String.make 1 c)) in
        `Assoc [ type_json; literal_json ]
end

let to_json sym_list out_dir =
  let oc_diff_json = open_out (out_dir ^ "/diff.json") in
  let rec make_json (id : int) sym_list acc =
    match sym_list with
    | [] -> acc
    | s_action :: s_rest ->
        let json_obj = DiffJson.mk_json_obj s_action in
        if json_obj = `Null then make_json id sym_list acc
        else
          let acc = ("diff-" ^ string_of_int id, json_obj) :: acc in
          make_json (id + 1) s_rest acc
  in
  let actions = `Assoc (List.rev (make_json 0 sym_list [])) in
  let json_obj = `Assoc [ ("diffs", actions) ] in
  Yojson.Safe.pretty_to_channel oc_diff_json json_obj;
  close_out oc_diff_json
