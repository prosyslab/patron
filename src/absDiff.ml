open Core
module Hashtbl = Stdlib.Hashtbl
module J = Yojson.Basic.Util
module H = Utils
module D = Diff

module AbsAst = struct
  type t =
    | Null
    | AbsGlob of abs_global * Cil.global
    | AbsStmt of abs_stmt * Cil.stmt
    | AbsExp of abs_exp * Cil.exp
    | AbsLval of abs_lval * Cil.lval

  and abs_typeinfo = { abs_tname : string; abs_ttype : abs_typ }
  and abs_enuminfo = { ename : string; eitems : (string * abs_node) list }

  and abs_typ =
    | SVoid
    | SInt
    | SFloat
    | SPtr of abs_typ
    | SArray of abs_typ
    | SNamed of abs_typeinfo
    | SComp of abs_compinfo
    | SEnum of abs_enuminfo
    | SFun of abs_typ * (string * abs_typ) list option * bool

  and abs_binop =
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

  and abs_unop = SNot | SNeg

  and abs_const =
    | SIntConst of int
    | SFloatConst of float
    | SCharConst of char
    | SStringConst of string

  and abs_offset =
    | SNoOffset
    | SField of abs_fieldinfo * abs_offset
    | SIndex of abs_node * abs_offset

  and abs_compinfo = { cname : string; cstruct : bool }
  and abs_fieldinfo = { fcomp : abs_compinfo; fname : string; ftype : abs_typ }
  and abs_varinfo = { vname : string; vtype : abs_typ }

  and abs_exp =
    | SENULL
    | SConst of abs_const
    | SELval of abs_node
    | SSizeOf of abs_typ
    | SSizeOfE of abs_node
    | SSizeOfStr of string
    | SBinOp of abs_binop * abs_node * abs_node * abs_typ
    | SUnOp of abs_unop * abs_node * abs_typ
    | SQuestion of abs_node * abs_node * abs_node * abs_typ
    | SCastE of abs_typ * abs_node
    | SAddrOf of abs_node
    | SStartOf of abs_node
    | SAddrOfLabel of abs_node

  and abs_lhost = SVar of abs_varinfo | SMem of abs_node
  and abs_lval = SLNull | Lval of abs_lhost * abs_offset

  and abs_stmt =
    | SSNull
    | SIf of abs_node * abs_node list * abs_node list
    | SSet of abs_node * abs_node
    | SCall of abs_node option * abs_node * abs_node list
    | SReturn of abs_node option
    | SBlock of abs_node list
    | SGoto of abs_node
    | SBreak
    | SContinue

  and abs_global = SGNull | SGFun | GVar of string * string
  and abs_node = { node : t; id : string; literal : string }

  let get_original_exp node =
    match node.node with
    | AbsExp (_, e) -> e
    | _ -> failwith "get_original_exp: not an expression"

  let get_original_lv node =
    match node.node with
    | AbsLval (_, l) -> l
    | _ -> failwith "get_original_lv: not a lval"

  let get_original_stmt node =
    match node.node with
    | AbsStmt (_, s) -> s
    | _ -> failwith "get_original_stmt: not a statement"

  let rec pp_node fmt e =
    match e.node with
    | Null -> Format.fprintf fmt "SNull"
    | AbsStmt (s, _) -> Format.fprintf fmt "AbsStmt(%a)" pp_absstmt s
    | AbsExp (e, _) -> Format.fprintf fmt "AbsExp(%a)" pp_absExp e
    | AbsLval (l, _) -> Format.fprintf fmt "AbsLval(%a)" pp_absLval l
    | _ -> failwith "not implemented"

  and pp_node_lst fmt lst =
    Format.fprintf fmt "[";
    List.iter ~f:(fun e -> Format.fprintf fmt "%a, " pp_node e) lst;
    Format.fprintf fmt "]"

  and pp_absstmts fmt ss =
    List.iter ~f:(fun s -> Format.fprintf fmt "%a; " pp_absstmt s) ss

  and pp_absstmt fmt s =
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

  and pp_absLval fmt l =
    match l with
    | SLNull -> Format.fprintf fmt "SLNull"
    | Lval (lhost, _) -> (
        match lhost with
        | SVar v -> Format.fprintf fmt "LVar(%a)" pp_svarinfo v
        | SMem e -> Format.fprintf fmt "LMem(%a)" pp_node e)

  and pp_soptexp fmt e =
    match e with None -> Format.fprintf fmt "None" | Some e -> pp_node fmt e

  and pp_absExp fmt e =
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
    | SNamed t -> Format.fprintf fmt "SNamed(%a)" pp_styp t.abs_ttype
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
          ~f:(fun (s, t) -> Format.fprintf fmt "(%s, %a), " s pp_styp t)
          lst;
        Format.fprintf fmt "]"

  and pp_senuminfo fmt e =
    Format.fprintf fmt "SEnumInfo(%s, %a)" e.ename pp_senumitem_lst e.eitems

  and pp_senumitem_lst fmt lst =
    Format.fprintf fmt "[";
    List.iter ~f:(fun (s, n) -> Format.fprintf fmt "(%s, %a), " s pp_node n) lst;
    Format.fprintf fmt "]"

  and pp_scompinfo fmt c =
    Format.fprintf fmt "SCompInfo(%s, %b)" c.cname c.cstruct

  and pp_sfieldinfo_lst fmt lst =
    Format.fprintf fmt "[";
    List.iter ~f:(fun f -> Format.fprintf fmt "%a, " pp_sfieldinfo f) lst;
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

  let to_null = Null
  let compare = compare
end

include AbsAst

type abs_context = {
  root_path : abs_node list;
  parent_of_patch : abs_node;
  patch_bound : string list * string list;
  func_name : string;
  sibling_idx : int;
}

type t =
  | SInsertStmt of abs_context * abs_node
  | SDeleteStmt of abs_context * abs_node
  | SInsertExp of abs_context * abs_node
  | SDeleteExp of abs_context * abs_node
  | SUpdateExp of abs_context * abs_node * abs_node
  | SInsertLval of abs_context * abs_node
  | SDeleteLval of abs_context * abs_node
  | SUpdateLval of abs_context * abs_node * abs_node

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

let match_exp2du (cfg_rev : (string, Maps.CfgNode.t) Stdlib.Hashtbl.t) exp_map
    du_node exp_str =
  let cfg_node = Stdlib.Hashtbl.find_opt cfg_rev du_node in
  if Option.is_none cfg_node then "None"
  else
    (* TODO: change it to lval *)
    let exps = [] in
    (* extract_exps_from_cfg du_node cfg_rev in *)
    let candidate =
      Stdlib.Hashtbl.fold
        (fun k v acc -> if String.equal exp_str k then v :: acc else acc)
        exp_map []
    in
    if List.is_empty candidate then "None"
    else
      try
        List.find_exn
          ~f:(fun x -> List.exists ~f:(fun y -> String.equal x y) exps)
          candidate
      with _ -> "None"

let find_closest_exp (before, after)
    (cfg_rev : (string, Maps.CfgNode.t) Stdlib.Hashtbl.t) exp_map exp_str =
  let rec aux b a acc =
    match (List.rev b, a) with
    | [], [] -> "None"
    | hd :: tl, _ ->
        let exp = match_exp2du cfg_rev exp_map hd exp_str in
        if String.equal exp "None" then aux tl a acc else exp
    | [], hd :: tl ->
        let exp = match_exp2du cfg_rev exp_map hd exp_str in
        if String.equal exp "None" then aux [] tl acc else exp
  in
  aux before after []

let find_exp_id func cfg_rev lval_map exp =
  let lval_syms =
    Stdlib.Hashtbl.fold
      (fun k v acc -> if String.equal k exp then v :: acc else acc)
      lval_map []
  in
  Stdlib.Hashtbl.fold
    (fun key data acc ->
      if String.is_prefix ~prefix:func key then
        match data with
        | Maps.CfgNode.CSet (_, _, _, lvs)
        | Maps.CfgNode.CCall (_, _, _, _, lvs)
        | Maps.CfgNode.CAssume (_, _, _, lvs)
        | Maps.CfgNode.CReturn1 (_, _, lvs)
        | Maps.CfgNode.CAlloc (_, _, _, lvs) -> (
            try
              List.find_exn
                ~f:(fun y ->
                  List.exists ~f:(fun sym -> String.equal sym y) lval_syms)
                lvs
              :: acc
            with _ -> acc)
        | _ -> acc
      else acc)
    cfg_rev []
  |> fun out -> try List.hd_exn out with _ -> "None"

let eq_line loc cloc =
  let file_name = loc.Cil.file |> Filename.basename in
  if loc.Cil.line = cloc.Maps.CfgNode.line && String.equal file_name cloc.file
  then true
  else false

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
  | Cil.CInt64 (i, _, _) -> SIntConst (Int64.to_int_exn i)
  | Cil.CReal (f, _, _) -> SFloatConst f
  | Cil.CChr c -> SCharConst c
  | Cil.CStr s -> SStringConst s
  | _ -> failwith "not supported"

let rec mk_sdiff func ctx maps diff =
  let lval_map = maps.Maps.lval_map |> Utils.reverse_hashtbl in
  let cfg = maps.cfg_map in
  let cfg_rev = maps.cfg_map |> Utils.reverse_hashtbl in
  match diff with
  | D.InsertStmt (_, s) -> SInsertStmt (ctx, mk_stmt func cfg cfg_rev lval_map s)
  | D.DeleteStmt (_, s) -> SDeleteStmt (ctx, mk_stmt func cfg cfg_rev lval_map s)
  | D.UpdateExp (_, e1, e2) ->
      SUpdateExp
        (ctx, mk_exp func cfg_rev lval_map e1, mk_exp func cfg_rev lval_map e2)
  | _ -> failwith "mk_sdiff: not implemented"

and mk_exp func cfg lval_map e =
  {
    node = AbsExp (match_exp func cfg lval_map e, e);
    id = match_exp_id func cfg lval_map e;
    literal = Ast.s_exp e;
  }

and mk_lval func cfg_rev lval_map l =
  {
    node = AbsLval (match_lval func cfg_rev lval_map l, l);
    id = match_lval_id func cfg_rev lval_map l;
    literal = Ast.s_lv l;
  }

and mk_exps func cfg_rev lval_map exps =
  List.map ~f:(fun e -> mk_exp func cfg_rev lval_map e) exps

and mk_stmt func cfg cfg_rev lval_map s =
  let id = match_stmt_id cfg s.Cil.skind in
  {
    node = AbsStmt (match_stmt func cfg cfg_rev lval_map s, s);
    id;
    literal = Ast.s_stmt s;
  }

and mk_stmts func cfg cfg_rev lval_map stmts =
  List.map ~f:(fun s -> mk_stmt func cfg cfg_rev lval_map s) stmts

and match_instr func cfg lval_map i =
  let i = List.hd_exn i in
  match i with
  | Cil.Set (l, e, _) ->
      AbsAst.SSet (mk_lval func cfg lval_map l, mk_exp func cfg lval_map e)
  | Cil.Call (Some l, e, es, _) ->
      AbsAst.SCall
        ( Some (mk_lval func cfg lval_map l),
          mk_exp func cfg lval_map e,
          mk_exps func cfg lval_map es )
  | Cil.Call (None, e, es, _) ->
      AbsAst.SCall
        (None, mk_exp func cfg lval_map e, mk_exps func cfg lval_map es)
  | _ -> failwith "match_stmt: not supported"

and match_stmt func cfg cfg_rev lval_map s =
  match s.Cil.skind with
  | Cil.If (e, s1, s2, _) ->
      let node = AbsExp (match_exp func cfg_rev lval_map e, e) in
      let id = match_exp_id func cfg_rev lval_map e in
      let literal = Ast.s_exp e in
      AbsAst.SIf
        ( { node; id; literal },
          mk_stmts func cfg cfg_rev lval_map s1.Cil.bstmts,
          mk_stmts func cfg cfg_rev lval_map s2.Cil.bstmts )
  | Cil.Instr i -> match_instr func cfg_rev lval_map i
  | Cil.Block b ->
      let bl =
        List.fold_left
          ~f:(fun (acc : AbsAst.abs_node list) s ->
            mk_stmt func cfg cfg_rev lval_map s :: acc)
          ~init:[] b.bstmts
        |> List.rev
      in
      AbsAst.SBlock bl
  | Cil.Return (Some e, _) ->
      let node = AbsExp (match_exp func cfg_rev lval_map e, e) in
      let id = match_exp_id func cfg_rev lval_map e in
      let literal = Ast.s_exp e in
      AbsAst.SReturn (Some { node; id; literal })
  | Cil.Return (None, _) -> AbsAst.SReturn None
  | Cil.Goto (s, _) ->
      let node = AbsStmt (SSNull, !s) in
      let id = "GOTO_DST" in
      let literal = Ast.s_stmt !s in
      AbsAst.SGoto { node; id; literal }
  | Cil.Break _ -> AbsAst.SBreak
  | Cil.Continue _ -> AbsAst.SContinue
  | _ -> failwith "match_stmt: not implemented"

and mk_absexp func cfg_rev lval_map e =
  let node = AbsExp (match_exp func cfg_rev lval_map e, e) in
  let id = match_exp_id func cfg_rev lval_map e in
  let literal = Ast.s_exp e in
  { node; id; literal }

and match_exp func cfg_rev lval_map (e : Cil.exp) =
  match e with
  | Cil.Const c -> AbsAst.SConst (to_sconst c)
  | Cil.Lval l ->
      let node = AbsLval (match_lval func cfg_rev lval_map l, l) in
      let id = match_lval_id func cfg_rev lval_map l in
      let literal = Ast.s_lv l in
      SELval { node; id; literal }
  | Cil.SizeOf t -> SSizeOf (to_styp t)
  | Cil.SizeOfE e' ->
      let node = AbsExp (match_exp func cfg_rev lval_map e', e') in
      let id = match_exp_id func cfg_rev lval_map e' in
      let literal = Ast.s_exp e' in
      SSizeOfE { node; id; literal }
  | Cil.SizeOfStr s -> SSizeOfStr s
  | Cil.BinOp (op, e1, e2, t) ->
      SBinOp
        ( to_sbinop op,
          mk_absexp func cfg_rev lval_map e1,
          mk_absexp func cfg_rev lval_map e2,
          to_styp t )
  | Cil.UnOp (op, e, t) ->
      let node = AbsExp (match_exp func cfg_rev lval_map e, e) in
      let id = match_exp_id func cfg_rev lval_map e in
      let literal = Ast.s_exp e in
      SUnOp (to_sunop op, { node; id; literal }, to_styp t)
  | Cil.CastE (t, e) ->
      let node = AbsExp (match_exp func cfg_rev lval_map e, e) in
      let id = match_exp_id func cfg_rev lval_map e in
      let literal = Ast.s_exp e in
      SCastE (to_styp t, { node; id; literal })
  | Cil.Question (e1, e2, e3, t) ->
      SQuestion
        ( mk_absexp func cfg_rev lval_map e1,
          mk_absexp func cfg_rev lval_map e2,
          mk_absexp func cfg_rev lval_map e3,
          to_styp t )
  | Cil.AddrOf l ->
      let node = AbsLval (match_lval func cfg_rev lval_map l, l) in
      let id = match_lval_id func cfg_rev lval_map l in
      let literal = Ast.s_lv l in
      SAddrOf { node; id; literal }
  | Cil.StartOf l ->
      let node = AbsLval (match_lval func cfg_rev lval_map l, l) in
      let id = match_lval_id func cfg_rev lval_map l in
      let literal = Ast.s_lv l in
      SStartOf { node; id; literal }
  | _ -> failwith "match_exp: not implemented"

and match_lval func cfg lval_map l =
  let lhost, offset = l in
  let slhost =
    match lhost with
    | Cil.Var v -> AbsAst.SVar { vname = v.vname; vtype = to_styp v.vtype }
    | Cil.Mem e ->
        let node = AbsExp (match_exp func cfg lval_map e, e) in
        let id = match_exp_id func cfg lval_map e in
        let literal = Ast.s_exp e in
        AbsAst.SMem { node; id; literal }
  in
  let soffset = match_offset func cfg lval_map offset in
  Lval (slhost, soffset)

and match_offset func cfg lval_map o =
  match o with
  | Cil.NoOffset -> AbsAst.SNoOffset
  | Cil.Field (f, o) ->
      let fcomp = { cname = f.fcomp.cname; cstruct = true } in
      let fname = f.fname in
      let ftype = to_styp f.ftype in
      AbsAst.SField ({ fcomp; fname; ftype }, match_offset func cfg lval_map o)
  | Cil.Index (e, o) ->
      let node = AbsExp (match_exp func cfg lval_map e, e) in
      let id = match_exp_id func cfg lval_map e in
      let literal = Ast.s_exp e in
      AbsAst.SIndex ({ node; id; literal }, match_offset func cfg lval_map o)

and match_fieldinfo f =
  {
    AbsAst.fcomp = match_compinfo f.Cil.fcomp;
    AbsAst.fname = f.Cil.fname;
    AbsAst.ftype = to_styp f.Cil.ftype;
  }

and match_compinfo c =
  { AbsAst.cname = c.Cil.cname; AbsAst.cstruct = c.Cil.cstruct }

and extract_fun_name g =
  match g with
  | Cil.GFun (f, _) -> f.Cil.svar.Cil.vname
  | _ -> failwith "extract_fun_name: not a function"

and match_ast_path func cfg cfg_rev lval_map lst acc =
  match lst with
  | [] -> []
  | hd :: tl -> (
      match hd with
      | Ast.Stmt s ->
          let id = match_stmt_id cfg s.Cil.skind in
          let node = AbsStmt (SSNull, s) in
          let literal = Ast.s_stmt s in
          { id; node; literal }
          :: match_ast_path func cfg cfg_rev lval_map tl (id :: acc)
      | Ast.Exp e ->
          let id = match_exp_id func cfg_rev lval_map e in
          let node = AbsExp (SENULL, e) in
          let literal = Ast.s_exp e in
          { id; node; literal }
          :: match_ast_path func cfg cfg_rev lval_map tl acc
      | Ast.Lval l ->
          let id = match_lval_id func cfg_rev lval_map l in
          let node = AbsLval (SLNull, l) in
          let literal = Ast.s_lv l in
          { id; node; literal }
          :: match_ast_path func cfg cfg_rev lval_map tl acc
      | Ast.Global g ->
          let id = extract_fun_name g in
          let node = AbsGlob (SGNull, g) in
          let literal = Ast.s_glob g in
          { id; node; literal }
          :: match_ast_path func cfg cfg_rev lval_map tl acc
      | _ -> failwith "match_ast_path: context failed to be read")

and match_stmt_path cfg lst =
  match lst with
  | [] -> []
  | hd :: tl -> (
      match hd with
      | Ast.Stmt s ->
          let id = match_stmt_id cfg s.Cil.skind in
          let node = AbsStmt (SSNull, s) in
          let literal = Ast.s_stmt s in
          { id; node; literal } :: match_stmt_path cfg tl
      | _ -> failwith "match_stmt_path: context failed to be read")

and find_lval_id func cfg_rev lval_map (l_str : string) =
  let lval_syms =
    Stdlib.Hashtbl.fold
      (fun k v acc -> if String.equal k l_str then v :: acc else acc)
      lval_map []
  in
  Stdlib.Hashtbl.fold
    (fun key data acc ->
      if String.is_prefix ~prefix:func key then
        match data with
        | Maps.CfgNode.CSet (_, _, _, lvs)
        | Maps.CfgNode.CCall (_, _, _, _, lvs)
        | Maps.CfgNode.CAssume (_, _, _, lvs)
        | Maps.CfgNode.CReturn1 (_, _, lvs)
        | Maps.CfgNode.CAlloc (_, _, _, lvs) -> (
            try
              List.find_exn
                ~f:(fun y ->
                  List.exists ~f:(fun sym -> String.equal sym y) lval_syms)
                lvs
              :: acc
            with _ -> acc)
        | _ -> acc
      else acc)
    cfg_rev []
  |> fun out -> try List.hd_exn out with _ -> "None"

and match_exp_id func cfg_rev lval_map e =
  let exp_str = Ast.s_exp e in
  let exp_id = find_exp_id func cfg_rev lval_map exp_str in
  if String.equal exp_id "None" then
    match e with
    | Cil.Const c -> match_const func cfg_rev lval_map c
    | Cil.Lval l | Cil.StartOf l | Cil.AddrOf l ->
        find_lval_id func cfg_rev lval_map (Ast.s_lv l)
    | Cil.SizeOf _ | Cil.SizeOfE _ | Cil.BinOp _ | Cil.UnOp _ | Cil.CastE _
    | Cil.Question _ ->
        "None"
    | _ -> failwith "match_exp: not implemented"
  else exp_id

and match_sizeof t exp_map = Ast.s_type t |> Stdlib.Hashtbl.find exp_map

and match_lval_id func cfg_rev lval_map (l : Cil.lval) =
  let l_str = Ast.s_lv l in
  find_lval_id func cfg_rev lval_map l_str

and match_set_id _ cfg loc =
  Stdlib.Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CSet (_, _, cloc, _)
      | Maps.CfgNode.CAlloc (_, _, cloc, _)
      | Maps.CfgNode.CFalloc (_, _, cloc, _)
      | Maps.CfgNode.CSalloc (_, _, cloc, _) ->
          if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

(* TODO: check func name to tighten *)
and match_call_id cfg loc =
  Stdlib.Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CCall (_, _, _, cloc, _) ->
          if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

and match_return_id cfg loc =
  Stdlib.Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CReturn1 (_, cloc, _) ->
          if eq_line loc cloc then v :: acc else acc
      | Maps.CfgNode.CReturn2 cloc -> if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

and match_assume_id cfg loc cond =
  Stdlib.Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CAssume (_, ccond, cloc, _) ->
          if eq_line loc cloc && Ast.s_exp cond |> String.equal ccond then
            v :: acc
          else acc
      | _ -> acc)
    cfg []

and match_loop_id cfg loc =
  Stdlib.Hashtbl.fold
    (fun k v acc ->
      match k with
      | Maps.CfgNode.CSkip cloc -> if eq_line loc cloc then v :: acc else acc
      | _ -> acc)
    cfg []

and match_stmt_id cfg s =
  (*TODO: tighten the string match of stmt by subset*)
  match s with
  | Cil.Instr i -> (
      let instr = List.hd_exn i in
      match instr with
      | Cil.Set (lv, _, loc) ->
          let matched = match_set_id lv cfg loc in
          if List.length matched >= 1 then List.hd_exn matched else "None"
      | Cil.Call (_, _, _, loc) ->
          let matched = match_call_id cfg loc in
          if List.length matched >= 1 then List.hd_exn matched else "None"
      | _ -> failwith "unexpected")
  | Cil.Return (_, loc) ->
      let matched = match_return_id cfg loc in
      if List.length matched >= 1 then List.hd_exn matched else "None"
  | Cil.If (cond, _, _, loc) ->
      let matched = match_assume_id cfg loc cond in
      if List.length matched >= 1 then List.hd_exn matched else "None"
  | Cil.Loop (_, loc, _, _) ->
      let matched = match_loop_id cfg loc in
      if List.length matched >= 1 then List.hd_exn matched else "None"
  | _ -> "None"

and match_const func cfg_rev lval_map c =
  let const_str = Ast.s_const c in
  find_exp_id func cfg_rev lval_map const_str

and to_styp t =
  match t with
  | Cil.TVoid _ -> SVoid
  | Cil.TInt _ -> SInt
  | Cil.TFloat _ -> SFloat
  | Cil.TPtr (t', _) -> SPtr (to_styp t')
  | Cil.TArray (t', _, _) -> SArray (to_styp t')
  | Cil.TNamed (t', _) ->
      SNamed { abs_tname = t'.Cil.tname; abs_ttype = to_styp t'.ttype }
  | Cil.TFun (t, lst, b, _) ->
      let slist =
        match lst with
        | Some lst -> Some (List.map ~f:(fun (s, ty, _) -> (s, to_styp ty)) lst)
        | None -> None
      in
      SFun (to_styp t, slist, b)
  | Cil.TComp (c, _) -> SComp (to_scompinfo c)
  | Cil.TEnum _ -> failwith "TEnum: not implemented"
  | Cil.TBuiltin_va_list _ -> failwith "not supported"

and to_scompinfo c = { cname = c.Cil.cname; cstruct = c.cstruct }

and to_sfieldinfo f =
  { fcomp = to_scompinfo f.Cil.fcomp; fname = f.fname; ftype = to_styp f.ftype }

let get_parent_fun parent_lst =
  let check_fun g = match g with Cil.GFun _ -> true | _ -> false in
  let get_fun g =
    match g with
    | Cil.GFun _ -> g
    | _ -> failwith "get_parent_fun: not a function"
  in
  let parent_fun_cand =
    List.fold_left
      ~f:(fun acc e ->
        match e with
        | Ast.Global g -> if check_fun g then get_fun g :: acc else acc
        | _ -> acc)
      ~init:[] parent_lst
  in
  if List.is_empty parent_fun_cand then
    failwith "get_parent_fun: diff source not found"
  else List.hd_exn parent_fun_cand

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

let get_sibling_lst patch_node parent_branch =
  match patch_node.node with
  | AbsStmt (_, s) -> (
      match s.Cil.skind with
      | Cil.Block lst -> lst.bstmts
      | Cil.Loop (b, _, _, _) -> b.bstmts
      | Cil.If (_, tb, eb, _) -> (
          match parent_branch with
          | D.TrueBranch -> tb.bstmts
          | FalseBranch -> eb.bstmts
          | _ -> failwith "get_sibling_lst: if statment without branch")
      | _ -> [])
  | AbsGlob (_, g) -> (
      match g with
      | Cil.GFun (f, _) -> f.sbody.bstmts
      | _ -> failwith "define_abs_diff: not implemented")
  | _ -> failwith "define_abs_diff: not implemented"

let rec extract_node_ids node =
  match node.node with
  | AbsStmt (s, _) -> node.id :: extract_stmt_ids s
  | AbsGlob _ -> [ node.id ]
  | AbsExp (e, _) ->
      if String.equal node.id "None" then extract_exp_ids e else [ node.id ]
  | AbsLval (l, _) ->
      if String.equal node.id "None" then extract_lval_ids l else [ node.id ]
  | _ -> []

and extract_stmt_ids (stmt : abs_stmt) =
  match stmt with
  | SBlock lst ->
      List.fold_left ~f:(fun acc s -> extract_node_ids s @ acc) ~init:[] lst
  | SSet (l, e) -> extract_node_ids l @ extract_node_ids e
  | SCall (Some l, e, es) ->
      extract_node_ids l @ extract_node_ids e
      @ List.fold_left ~f:(fun acc e -> extract_node_ids e @ acc) ~init:[] es
  | SCall (None, e, es) ->
      extract_node_ids e
      @ List.fold_left ~f:(fun acc e -> extract_node_ids e @ acc) ~init:[] es
  | SReturn (Some e) -> extract_node_ids e
  | SReturn None -> []
  | SIf (e, s1, s2) ->
      extract_node_ids e
      @ List.fold_left ~f:(fun acc s -> extract_node_ids s @ acc) ~init:[] s1
      @ List.fold_left ~f:(fun acc s -> extract_node_ids s @ acc) ~init:[] s2
  | SGoto s -> extract_node_ids s
  | _ -> []

and extract_exp_ids (exp : abs_exp) =
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

and extract_lval_ids (lval : abs_lval) =
  match lval with
  | Lval (l, o) -> extract_lhost_ids l @ extract_offset_ids o
  | _ -> []

and extract_lhost_ids (lhost : abs_lhost) =
  match lhost with SVar _ -> [] | SMem e -> extract_node_ids e

and extract_offset_ids (offset : abs_offset) =
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
  List.fold_left ~f:(fun acc s -> s.id :: acc) ~init:[] sibs |> List.rev

let filter_nodes du_facts nodes =
  List.fold_left
    ~f:(fun acc n -> if Stdlib.List.mem n du_facts then n :: acc else acc)
    ~init:[] nodes
  |> List.rev

let mk_s_sibs patch_bw cfg_rev maps exp_map path facts acc =
  let facts_lst = Chc.to_list facts in
  match_ast_path patch_bw maps.cfg_map cfg_rev exp_map path acc
  |> symbolize_sibs
  |> filter_nodes (Chc.extract_nodes_in_facts facts_lst maps.Maps.node_map)

let get_parent_of_exp_sibs (left_sibs, right_sibs) patch_node =
  if List.is_empty left_sibs && List.is_empty right_sibs then []
  else if
    try List.hd_exn left_sibs |> fun hd -> Ast.is_exp hd || Ast.is_lv hd
    with _ ->
      List.hd_exn right_sibs |> fun hd -> Ast.is_exp hd || Ast.is_lv hd
  then if String.equal patch_node.id "None" then [] else [ patch_node.id ]
  else []

let mk_abs_ctx ctx maps du_facts =
  let exp_map = maps.Maps.exp_map |> Utils.reverse_hashtbl in
  let cfg_map = maps.cfg_map in
  let cfg_map_rev = maps.cfg_map |> Utils.reverse_hashtbl in
  let root_path = List.rev ctx.D.root_path in
  let parent_func = ctx.top_func_name in
  let s_root_path =
    match_ast_path parent_func cfg_map cfg_map_rev exp_map root_path []
  in
  let left_sibs, right_sibs = ctx.patch_bound in
  let prnt_fun = get_parent_fun root_path in
  let patch_node =
    try List.rev s_root_path |> List.hd_exn
    with Failure _ ->
      { node = AbsGlob (SGFun, prnt_fun); id = "None"; literal = "None" }
  in
  let parent_of_exp_sibs = get_parent_of_exp_sibs ctx.patch_bound patch_node in
  let s_left_sibs =
    mk_s_sibs parent_func cfg_map_rev maps exp_map left_sibs du_facts
      parent_of_exp_sibs
  in
  let s_right_sibs =
    mk_s_sibs parent_func cfg_map_rev maps exp_map right_sibs du_facts
      parent_of_exp_sibs
  in
  {
    root_path = s_root_path;
    parent_of_patch = patch_node;
    patch_bound = (s_left_sibs, s_right_sibs);
    (* patch_between = patch_bw; *)
    func_name = ctx.D.top_func_name;
    sibling_idx = ctx.D.sibling_idx;
  }

(* let extract_ctx_nodes sdiff =
   List.fold_left
     ~f:(fun acc sd ->
       let ctx = get_ctx sd in
       let b, a = ctx.patch_between in
       let right_before =
         try Some (List.rev b |> List.hd_exn) with _ -> None
       in
       let right_after = try Some (List.hd_exn a) with _ -> None in
       ([ right_before; right_after ]
       |> List.fold_left
            ~f:(fun acc x ->
              if Option.is_none x then acc else Option.value_exn x :: acc)
            ~init:[])
       @ acc)
     ~init:[] sdiff *)

let extract_patch_related_lvals sdiff =
  List.fold_left ~f:(fun acc d -> extract_diff_ids d @ acc) ~init:[] sdiff

let map_ast2cf_nodes ast_lst maps =
  match_stmt_path maps.Maps.cfg_map ast_lst |> symbolize_sibs

let map_cf2du_nodes cf_lst du_lst =
  List.fold_left
    ~f:(fun acc v ->
      try List.find_exn ~f:(fun v' -> String.equal v v') du_lst :: acc
      with _ -> acc)
    ~init:[] cf_lst

let mk_du_patch_bw dug (src, snk) (ast_before, ast_after) maps =
  let du_nodes = Dug.fold_vertex (fun v acc -> v :: acc) dug [] in
  let before, after =
    let cfg_before = map_ast2cf_nodes ast_before maps in
    let cfg_after = map_ast2cf_nodes ast_after maps in
    if List.is_empty cfg_before && List.is_empty cfg_after then
      failwith
        "mk_du_patch_bw: no data dependency is found within ast-function level"
    else
      let func_du_before = map_cf2du_nodes cfg_before du_nodes in
      let func_du_after = map_cf2du_nodes cfg_after du_nodes |> List.rev in
      if List.is_empty func_du_before && List.is_empty func_du_after then
        failwith
          "mk_du_patch_bw: no data dependency is found within ast-function \
           level"
      else if List.is_empty func_du_before then
        let after_patch = List.hd_exn func_du_after in
        let du_before =
          Dug.shortest_path dug src after_patch
          |> Dug.delete_last_edge after_patch
        in
        let du_after = Dug.shortest_path dug after_patch snk in
        (du_before, du_after)
      else if List.is_empty func_du_after then
        let before_patch = List.hd_exn func_du_before in
        let du_before = Dug.shortest_path dug src before_patch in
        let du_after =
          Dug.shortest_path dug before_patch snk
          |> Dug.delete_first_edge before_patch
        in
        (du_before, du_after)
      else
        let before_patch = List.hd_exn func_du_before in
        let after_patch = List.hd_exn func_du_after in
        let du_before = Dug.shortest_path dug src before_patch in
        let du_after = Dug.shortest_path dug after_patch snk in
        (du_before, du_after)
  in
  (Dug.edges2lst before, Dug.edges2lst after)

let mk_patch_comp sdiff =
  (* let du_nodes = extract_ctx_nodes sdiff in *)
  let exps = extract_patch_related_lvals sdiff in
  (* Stdlib.List.append du_nodes exps *)
  exps
  |> Stdlib.List.sort_uniq Stdlib.compare
  |> List.filter ~f:(fun x -> String.equal x "None" |> not)

let rec split_stmt_bw stmt_lst stmt acc =
  match stmt_lst with
  | [] -> ([], [])
  | hd :: tl ->
      if Ast.isom_stmt hd stmt then (acc, tl)
      else split_stmt_bw tl stmt (hd :: acc)

let rec collect_bws rp stmt acc =
  match rp with
  | [] -> acc
  | hd :: tl ->
      if Ast.is_stmt hd then
        let s = Ast.ast2stmt hd in
        match s.Cil.skind with
        | Cil.Block lst | Cil.Loop (lst, _, _, _) ->
            split_stmt_bw lst.Cil.bstmts stmt [] :: acc |> collect_bws tl s
        | Cil.If (_, tb, eb, _) ->
            let tb_b, tb_a = split_stmt_bw tb.Cil.bstmts stmt [] in
            if List.is_empty tb_b && List.is_empty tb_a then
              split_stmt_bw eb.Cil.bstmts stmt [] :: acc |> collect_bws tl s
            else (tb_b, tb_a) :: acc |> collect_bws tl s
        | _ -> failwith "collect_bws: not implemented"
      else if Ast.is_glob hd || Ast.is_fun hd then acc
      else failwith "collect_bws: not implemented"

let mk_ast_patch_bw top_func_name root_path bw =
  let children_of_func =
    Utils.extract_target_func (Ast.get_buggy_ast ()) top_func_name |> fun g ->
    match g with
    | Cil.GFun (f, _) -> f.sbody.bstmts
    | _ -> failwith "mk_ast_patch_bw: not a function"
  in
  let top_stmt =
    List.fold_left
      ~f:(fun acc s -> if Ast.is_stmt s then Ast.ast2stmt s :: acc else acc)
      ~init:[] root_path
    |> List.hd
  in
  let b1, a1 =
    if Option.is_none top_stmt then ([], [])
    else split_stmt_bw children_of_func (Option.value_exn top_stmt) []
  in
  let b2, a2 =
    let bottom_stmt = List.hd_exn root_path in
    if Ast.is_stmt bottom_stmt |> not then ([], [])
    else
      collect_bws (List.tl_exn root_path) (bottom_stmt |> Ast.ast2stmt) []
      |> List.fold_left
           ~f:(fun (acc_b, acc_a) (b, a) -> (b @ acc_b, acc_a @ a))
           ~init:([], [])
  in
  let b3, a3 =
    bw |> fun (b, a) -> (Ast.path2stmts b |> List.rev, Ast.path2stmts a)
  in
  let before = List.rev b1 @ b2 @ b3 |> Ast.stmts2path in
  let after = a3 @ a2 @ a1 |> Ast.stmts2path in
  (before, after)

let define_abs_diff maps buggy diff du_facts _ _ =
  get_gvars buggy;
  List.fold_left
    ~f:(fun acc (action, _) ->
      let ctx = D.get_ctx action in
      (* let ast_patch_bw =
           mk_ast_patch_bw ctx.Diff.top_func_name ctx.root_path ctx.patch_bound
         in *)
      (* let du_patch_bw = mk_du_patch_bw dug src_snk ast_patch_bw maps in *)
      let s_context = mk_abs_ctx ctx maps du_facts in
      mk_sdiff ctx.top_func_name s_context maps action :: acc)
    ~init:[] diff

module DiffJson = struct
  open AbsAst

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
        let tname_json = ("tname", `String t.abs_tname) in
        let typ_json = ("typ", styp_to_sym t.abs_ttype) in
        `Assoc [ ("named", `Assoc [ tname_json; typ_json ]) ]
    | SFun (t, lst, b) ->
        let slist = match lst with Some lst -> lst | None -> [] in
        let typ_json = ("typ", styp_to_sym t) in
        let args_lst =
          List.fold_left
            ~f:(fun acc (s, ty) -> `String s :: styp_to_sym ty :: acc)
            ~init:[] slist
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
    let context_json (context : abs_context) =
      let func_name_json = ("func_name", `String context.func_name) in
      let sid_lst =
        `List
          (List.fold_left
             ~f:(fun acc node -> `String node.id :: acc)
             ~init:[] context.root_path)
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
      (List.fold_left ~f:(fun acc x -> sexp_to_json x :: acc) ~init:[] lst
      |> List.rev)

  and sstmts_to_json lst =
    `List
      (List.fold_left ~f:(fun acc x -> sstmt_to_json x :: acc) ~init:[] lst
      |> List.rev)

  and sstmt_to_json (sstmt : abs_node) =
    let node = sstmt.node in
    let stmt =
      match node with
      | AbsStmt (s, _) -> s
      | _ -> failwith "sstmt_to_json: undefined AbsStmt"
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

  and sexp_to_json (sexp : AbsAst.abs_node) =
    let node = sexp.node in
    let exp =
      match node with
      | AbsExp (e, _) -> e
      | _ -> failwith "sexp_to_json: undefined AbsExp"
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
        AbsAst.pp_absExp Format.std_formatter exp;
        failwith "sexp_to_json: undefined AbsExp"

  and slval_to_json (slval : AbsAst.abs_node) =
    let node = slval.node in
    let lval =
      match node with
      | AbsLval (l, _) -> l
      | _ -> failwith "slval_to_json: undefined AbsLval"
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

  and sconst_to_json (sconst : AbsAst.abs_const) =
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

let extract_parent abs_diff (ast_map : (Ast.t, int) Hashtbl.t) =
  let parent_of_patch =
    List.fold_left ~init:[]
      ~f:(fun acc diff -> extract_context diff :: acc)
      abs_diff
    (* Consider that patch occured in a single location for now *)
    |> List.fold_left ~init:[] ~f:(fun acc c ->
           (c.parent_of_patch.node, c.func_name) :: acc)
  in
  List.fold_left ~init:[]
    ~f:(fun acc (p, f) ->
      match p with
      | AbsAst.AbsGlob (_, g) ->
          (Ast.glob2ast (Some g) |> Hashtbl.find ast_map |> string_of_int, f)
          :: acc
      | AbsStmt (_, s) ->
          (Ast.stmt2ast (Some s) |> Hashtbl.find ast_map |> string_of_int, f)
          :: acc
      | _ -> failwith "parent not found")
    parent_of_patch
  |> List.rev

let to_json abs_list out_dir =
  let oc_diff_json = Stdlib.open_out (out_dir ^ "/diff.json") in
  let rec make_json (id : int) abs_list acc =
    match abs_list with
    | [] -> acc
    | s_action :: s_rest ->
        let json_obj = DiffJson.mk_json_obj s_action in
        if Yojson.equal json_obj `Null then make_json id abs_list acc
        else
          let acc = ("diff-" ^ string_of_int id, json_obj) :: acc in
          make_json (id + 1) s_rest acc
  in
  let actions = `Assoc (List.rev (make_json 0 abs_list [])) in
  let json_obj = `Assoc [ ("diffs", actions) ] in
  Yojson.Safe.pretty_to_channel oc_diff_json json_obj;
  Stdlib.close_out oc_diff_json
