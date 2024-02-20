open Core
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module Set = Stdlib.Set
module L = Logger
module J = Yojson.Basic.Util
module H = Utils
module D = Diff
module PatchComps = Set.Make (String)

type abs_ast =
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
and abs_node = { node : abs_ast; id : string; literal : string }

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
      Format.fprintf fmt "SIf(%a, %a, %a)" pp_node e pp_node_lst s1 pp_node_lst
        s2
  | SSet (l, e) -> Format.fprintf fmt "SSet(%a, %a)" pp_node l pp_node e
  | SCall (l, e, es) ->
      Format.fprintf fmt "SCall(%a, %a, %a)" pp_soptlval l pp_node e pp_node_lst
        es
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

type abs_context = {
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

let rec to_styp t =
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
  | Cil.CInt64 (i, _, _) -> SIntConst (Int64.to_int_exn i)
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

let symbolize_sibs sibs =
  List.fold_left ~f:(fun acc s -> s.id :: acc) ~init:[] sibs |> List.rev

let filter_nodes du_facts nodes =
  List.fold_left
    ~f:(fun acc n -> if Stdlib.List.mem n du_facts then n :: acc else acc)
    ~init:[] nodes
  |> List.rev

let is_lv_or_exp t = Ast.is_exp t || Ast.is_lv t

let get_parent_of_exp_sibs (left_sibs, right_sibs) patch_node =
  let open Option in
  let l = List.hd left_sibs >>| is_lv_or_exp |> exists ~f:Fun.id in
  let r = List.hd right_sibs >>| is_lv_or_exp |> exists ~f:Fun.id in
  if (l || r) && not (String.equal patch_node.id "None") then [ patch_node.id ]
  else []

let match_stmt_id loc_map = function
  | Cil.Instr (Cil.Set (_, _, loc) :: _)
  | Cil.Instr (Cil.Call (_, _, _, loc) :: _)
  | Cil.Return (_, loc)
  | Cil.If (_, _, _, loc)
  | Cil.Loop (_, loc, _, _) ->
      Hashtbl.find_opt loc_map { Maps.file = loc.file; line = loc.line }
      |> Option.value ~default:"None"
  | _ -> "None"

let match_lval_id func dug lv =
  let module LvalMap = Map.Make (String) in
  Hashtbl.find dug.Dug.lvmap_per_func func
  |> LvalMap.find_opt (Ast.s_lv lv)
  (* NOTE: Only function name should be None *)
  |> Option.value ~default:"None"

let extract_fun_name g =
  match g with
  | Cil.GFun (f, _) -> f.Cil.svar.Cil.vname
  | _ -> failwith "extract_fun_name: not a function"

let ast2absnode maps dug func = function
  | Ast.Stmt s ->
      let id = match_stmt_id maps.Maps.loc_map s.Cil.skind in
      let node = AbsStmt (SSNull, s) in
      let literal = Ast.s_stmt s in
      { id; node; literal }
  | Ast.Exp e ->
      let id = "None" in
      let node = AbsExp (SENULL, e) in
      let literal = Ast.s_exp e in
      { id; node; literal }
  | Ast.Lval l ->
      let id = match_lval_id func dug l in
      let node = AbsLval (SLNull, l) in
      let literal = Ast.s_lv l in
      { id; node; literal }
  | Ast.Global g ->
      let id = extract_fun_name g in
      let node = AbsGlob (SGNull, g) in
      let literal = Ast.s_glob g in
      { id; node; literal }
  | _ -> failwith "ast2absnode: context failed to be read"

let mk_s_sibs func dug maps path facts =
  let facts_lst = Chc.to_list facts in
  List.map ~f:(ast2absnode maps dug func) path
  |> symbolize_sibs
  |> filter_nodes (Chc.extract_nodes_in_facts facts_lst maps.Maps.node_map)

let mk_abs_ctx ctx maps dug du_facts =
  let parent_func = ctx.D.top_func_name in
  let prnt_fun = get_parent_fun ctx.D.root_path in
  let patch_node =
    if List.is_empty ctx.D.root_path then
      { node = AbsGlob (SGFun, prnt_fun); id = "None"; literal = "None" }
    else List.hd_exn ctx.D.root_path |> ast2absnode maps dug parent_func
  in
  let left_sibs, right_sibs = ctx.patch_bound in
  (* TODO: get abstract patch between using DUG -> get s_sibs from patch between *)
  let s_left_sibs = mk_s_sibs parent_func dug maps left_sibs du_facts in
  let s_right_sibs = mk_s_sibs parent_func dug maps right_sibs du_facts in
  {
    parent_of_patch = patch_node;
    patch_bound = (s_left_sibs, s_right_sibs);
    func_name = ctx.D.top_func_name;
    sibling_idx = ctx.D.sibling_idx;
  }

let rec mk_abs_offset func dug loc_map = function
  | Cil.NoOffset -> SNoOffset
  | Cil.Field (f, o) ->
      let fcomp = { cname = f.fcomp.cname; cstruct = true } in
      let fname = f.fname in
      let ftype = to_styp f.ftype in
      SField ({ fcomp; fname; ftype }, mk_abs_offset func dug loc_map o)
  | Cil.Index (e, o) ->
      let abs_exp_node, _ = mk_abs_exp func dug loc_map (e, PatchComps.empty) in
      SIndex (abs_exp_node, mk_abs_offset func dug loc_map o)

(* NOTE: patch_comps has only lval that is not sub lval *)
and mk_abs_lv func dug loc_map (lv, pc) =
  let id = match_lval_id func dug lv in
  let lhost, offset = lv in
  let slhost =
    match lhost with
    | Cil.Var v -> SVar { vname = v.vname; vtype = to_styp v.vtype }
    | Cil.Mem e ->
        let abs_exp_node, _ =
          mk_abs_exp func dug loc_map (e, PatchComps.empty)
        in
        SMem abs_exp_node
  in
  let soffset = mk_abs_offset func dug loc_map offset in
  let node = AbsLval (Lval (slhost, soffset), lv) in
  let literal = Ast.s_lv lv in
  ({ node; id; literal }, PatchComps.add id pc)

and mk_abs_exp func dug loc_map (e, pc) =
  let id = "None" in
  let abs_exp, pc' =
    match e with
    | Cil.Const c -> (SConst (to_sconst c), pc)
    | Cil.Lval l ->
        let abs_lv_node, pc1 = mk_abs_lv func dug loc_map (l, pc) in
        (SELval abs_lv_node, pc1)
    | Cil.SizeOf t -> (SSizeOf (to_styp t), pc)
    | Cil.SizeOfE e' ->
        let abs_exp_node, pc1 = mk_abs_exp func dug loc_map (e', pc) in
        (SSizeOfE abs_exp_node, pc1)
    | Cil.SizeOfStr s -> (SSizeOfStr s, pc)
    | Cil.BinOp (op, e1, e2, t) ->
        let abs_exp_node1, pc1 = mk_abs_exp func dug loc_map (e1, pc) in
        let abs_exp_node2, pc2 = mk_abs_exp func dug loc_map (e2, pc1) in
        (SBinOp (to_sbinop op, abs_exp_node1, abs_exp_node2, to_styp t), pc2)
    | Cil.UnOp (op, e', t) ->
        let abs_exp_node, pc1 = mk_abs_exp func dug loc_map (e', pc) in
        (SUnOp (to_sunop op, abs_exp_node, to_styp t), pc1)
    | Cil.CastE (t, e') ->
        let abs_exp_node, pc1 = mk_abs_exp func dug loc_map (e', pc) in
        (SCastE (to_styp t, abs_exp_node), pc1)
    | Cil.Question (e1, e2, e3, t) ->
        let abs_exp_node1, pc1 = mk_abs_exp func dug loc_map (e1, pc) in
        let abs_exp_node2, pc2 = mk_abs_exp func dug loc_map (e2, pc1) in
        let abs_exp_node3, pc3 = mk_abs_exp func dug loc_map (e3, pc2) in
        (SQuestion (abs_exp_node1, abs_exp_node2, abs_exp_node3, to_styp t), pc3)
    | Cil.AddrOf l ->
        let abs_lv_node, pc1 = mk_abs_lv func dug loc_map (l, pc) in
        (SAddrOf abs_lv_node, pc1)
    | Cil.StartOf l ->
        let abs_lv_node, pc1 = mk_abs_lv func dug loc_map (l, pc) in
        (SStartOf abs_lv_node, pc1)
    | _ -> failwith "match_exp: not implemented"
  in
  let node = AbsExp (abs_exp, e) in
  let literal = Ast.s_exp e in
  ({ node; id; literal }, pc')

and mk_abs_exps func dug loc_map (es, pc) =
  List.fold_left
    ~f:(fun (abs_es, pc) e ->
      let abs_e, pc' = mk_abs_exp func dug loc_map (e, pc) in
      (abs_e :: abs_es, pc'))
    ~init:([], pc) es

and mk_abs_instr func dug loc_map (i, pc) =
  match i with
  | Cil.Set (l, e, _) ->
      let abs_lv_node, pc1 = mk_abs_lv func dug loc_map (l, pc) in
      let abs_exp_node, pc2 = mk_abs_exp func dug loc_map (e, pc1) in
      (SSet (abs_lv_node, abs_exp_node), pc2)
  | Cil.Call (Some l, e, es, _) ->
      let abs_lv_node, pc1 = mk_abs_lv func dug loc_map (l, pc) in
      let abs_exp_node, pc2 = mk_abs_exp func dug loc_map (e, pc1) in
      let abs_exp_nodes, pc3 = mk_abs_exps func dug loc_map (es, pc2) in
      (SCall (Some abs_lv_node, abs_exp_node, abs_exp_nodes), pc3)
  | Cil.Call (None, e, es, _) ->
      let abs_exp_node, pc1 = mk_abs_exp func dug loc_map (e, pc) in
      let abs_exp_nodes, pc2 = mk_abs_exps func dug loc_map (es, pc1) in
      (SCall (None, abs_exp_node, abs_exp_nodes), pc2)
  | _ -> failwith "match_stmt: not supported"

and mk_abs_stmt func dug loc_map (s, pc) =
  let id = match_stmt_id loc_map s.Cil.skind in
  let abs_stmt, pc' =
    match s.Cil.skind with
    | Cil.If (e, s1, s2, _) ->
        let abs_exp_node, pc1 = mk_abs_exp func dug loc_map (e, pc) in
        let abs_stmt_node1, pc2 =
          mk_abs_stmts func dug loc_map (s1.Cil.bstmts, pc1)
        in
        let abs_stmt_node2, pc3 =
          mk_abs_stmts func dug loc_map (s2.Cil.bstmts, pc2)
        in
        (SIf (abs_exp_node, abs_stmt_node1, abs_stmt_node2), pc3)
    | Cil.Instr il -> mk_abs_instr func dug loc_map (List.hd_exn il, pc)
    | Cil.Block b ->
        let abs_stmts_node, pc1 =
          mk_abs_stmts func dug loc_map (b.bstmts, pc)
        in
        (SBlock abs_stmts_node, pc1)
    | Cil.Return (Some e, _) ->
        let abs_exp_node, pc1 = mk_abs_exp func dug loc_map (e, pc) in
        (SReturn (Some abs_exp_node), pc1)
    | Cil.Return (None, _) -> (SReturn None, pc)
    | Cil.Goto (s', _) ->
        let node = AbsStmt (SSNull, !s') in
        let id = "GOTO_DST" in
        let literal = Ast.s_stmt !s' in
        (SGoto { node; id; literal }, pc)
    | Cil.Break _ -> (SBreak, pc)
    | Cil.Continue _ -> (SContinue, pc)
    | _ -> failwith "mk_abs_stmt: not implemented"
  in
  let node = AbsStmt (abs_stmt, s) in
  let literal = Ast.s_stmt s in
  ({ node; id; literal }, pc')

and mk_abs_stmts func dug loc_map (ss, patch_comps) =
  List.fold_left
    ~f:(fun (abs_ss, pc) s ->
      let abs_s, pc' = mk_abs_stmt func dug loc_map (s, pc) in
      (abs_s :: abs_ss, pc'))
    ~init:([], patch_comps) ss

let mk_abs_action maps dug du_facts = function
  | D.InsertStmt (ctx, s) ->
      let func = ctx.top_func_name in
      let s_ctx = mk_abs_ctx ctx maps dug du_facts in
      let abs_stmt, patch_comps =
        mk_abs_stmt func dug maps.loc_map (s, PatchComps.empty)
      in
      (SInsertStmt (s_ctx, abs_stmt), patch_comps)
  | D.DeleteStmt (ctx, s) ->
      let func = ctx.top_func_name in
      let s_ctx = mk_abs_ctx ctx maps dug du_facts in
      let abs_stmt, patch_comps =
        mk_abs_stmt func dug maps.loc_map (s, PatchComps.empty)
      in
      (SDeleteStmt (s_ctx, abs_stmt), patch_comps)
  | D.UpdateExp (ctx, e1, e2) ->
      let func = ctx.top_func_name in
      let s_ctx = mk_abs_ctx ctx maps dug du_facts in
      let abs_exp1, patch_comps1 =
        mk_abs_exp func dug maps.loc_map (e1, PatchComps.empty)
      in
      let abs_exp2, patch_comps2 =
        mk_abs_exp func dug maps.loc_map (e2, patch_comps1)
      in
      (SUpdateExp (s_ctx, abs_exp1, abs_exp2), patch_comps2)
  | _ -> failwith "mk_sdiff: not implemented"

let define_abs_diff maps buggy diff dug du_facts _ =
  get_gvars buggy;
  List.fold_left
    ~f:(fun (abs_actions, patch_comps) (action, _) ->
      let abs_action, pc = mk_abs_action maps dug du_facts action in
      (abs_action :: abs_actions, PatchComps.union pc patch_comps))
    ~init:([], PatchComps.empty) diff
  |> fun (actions, patch_comps) ->
  ( List.rev actions,
    let pc = PatchComps.remove "None" patch_comps in
    PatchComps.fold (fun pc l -> pc :: l) pc [] )

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
      | AbsGlob (_, g) ->
          (Ast.glob2ast (Some g) |> Hashtbl.find ast_map |> string_of_int, f)
          :: acc
      | AbsStmt (_, s) ->
          (Ast.stmt2ast (Some s) |> Hashtbl.find ast_map |> string_of_int, f)
          :: acc
      | _ -> failwith "parent not found")
    parent_of_patch
  |> List.rev
