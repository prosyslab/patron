open Core
open ProsysCil.Cil
module Pretty = ProsysCil.Pretty
module Escape = ProsysCil.Escape
module L = Logger
module Hashtbl = Stdlib.Hashtbl

type t =
  | Global of global
  | Fun of string
  | Stmt of stmt
  | Exp of exp
  | Lval of lval
  | NotApplicable

let compare a b =
  match (a, b) with
  | Global g1, Global g2 -> compareLoc (get_globalLoc g1) (get_globalLoc g2)
  | Fun f1, Fun f2 -> String.compare f1 f2
  | Stmt s1, Stmt s2 -> compareLoc (get_stmtLoc s1.skind) (get_stmtLoc s2.skind)
  | _ -> Stdlib.compare a b

let is_glob = function Global _ -> true | _ -> false
let is_fun = function Fun _ -> true | _ -> false
let is_stmt = function Stmt _ -> true | _ -> false
let is_exp = function Exp _ -> true | _ -> false
let is_lv = function Lval _ -> true | _ -> false
let is_blk = function Block _ | Loop _ | If _ -> true | _ -> false
let is_instr = function Instr _ -> true | _ -> false
let get_instrs stmt = match stmt.skind with Instr instrs -> instrs | _ -> []

(* for the reference *)
type edge = t * t
type subtree = edge list
type path = t list

let globs2path globs = List.map ~f:(fun g -> Global g) globs
let stmts2path stmts = List.map ~f:(fun s -> Stmt s) stmts
let exps2path exps = List.map ~f:(fun e -> Exp e) exps

let of_glob element =
  match element with None -> NotApplicable | Some x -> Global x

let of_stmt element =
  match element with None -> NotApplicable | Some x -> Stmt x

let of_exp element =
  match element with None -> NotApplicable | Some x -> Exp x

let of_lval element =
  match element with None -> NotApplicable | Some x -> Lval x

let to_stmt element =
  match element with Stmt x -> x | _ -> L.error "Not a statement"

let to_lval elememt =
  match elememt with Lval l -> l | _ -> L.error "Not a lval"

let path2stmts path = List.map ~f:to_stmt path
let compare = compare
let flip f y x = f x y
let list_fold f list init = List.fold_left ~f:(flip f) ~init list
let link_by_sep sep s acc = if String.is_empty acc then s else acc ^ sep ^ s

let string_of_list ?(first = "[") ?(last = "]") ?(sep = ";") string_of_v list =
  let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
  first ^ list_fold add_string_of_v list "" ^ last

let get_loc_filename (loc : location) =
  String.split ~on:'/' loc.file |> List.last_exn

let get_loc_line (loc : location) = loc.line
let get_stmt_line stmt = get_loc_line (get_stmtLoc stmt.skind)

let get_global_loc glob =
  match glob with
  | GFun (_, loc)
  | GVar (_, _, loc)
  | GType (_, loc)
  | GCompTag (_, loc)
  | GCompTagDecl (_, loc)
  | GEnumTag (_, loc)
  | GEnumTagDecl (_, loc)
  | GVarDecl (_, loc)
  | GAsm (_, loc)
  | GPragma (_, loc) ->
      loc
  | _ -> L.error "get_global_loc error"

let s_location (loc : location) =
  get_loc_filename loc ^ ":" ^ string_of_int loc.line

let tostring s = Escape.escape_string (Pretty.sprint ~width:0 s)
let s_attrs attrs = tostring (d_attrlist () attrs)
let s_attr attr = tostring (d_attr () attr)

let s_glob g =
  match g with
  | GFun (f, _) -> "function:" ^ f.svar.vname
  | _ -> printGlobal !printerForMaincil () g |> Pretty.sprint ~width:80

let rec s_exps es = string_of_list ~first:"(" ~last:")" ~sep:", " s_exp es

and s_exp = function
  | Const c -> s_const c
  | Lval l -> s_lv l
  | SizeOf t -> "SizeOf(" ^ s_type t ^ ")"
  | SizeOfE e -> "SizeOfE(" ^ s_exp e ^ ")"
  | SizeOfStr s -> "SizeOfStr(" ^ s ^ ")"
  | AlignOf t -> "AlignOf(" ^ s_type t ^ ")"
  | AlignOfE e -> "AlignOfE(" ^ s_exp e ^ ")"
  | UnOp (u, e, _) -> s_uop u ^ s_exp_paren e
  | BinOp (b, e1, e2, _) -> s_exp_paren e1 ^ s_bop b ^ s_exp_paren e2
  | Question (c, e1, e2, _) ->
      s_exp_paren c ^ " ? " ^ s_exp_paren e1 ^ " : " ^ s_exp_paren e2
  | CastE (t, e) -> "(" ^ s_type t ^ ")" ^ s_exp_paren e
  | AddrOf l -> "&" ^ s_lv l
  | AddrOfLabel _ -> invalid_arg "AddrOfLabel is not supported."
  | StartOf l -> "StartOf(" ^ s_lv l ^ ")"

and s_exp_paren e =
  match e with
  | UnOp _ | BinOp _ | Question _ | CastE _ -> "(" ^ s_exp e ^ ")"
  | _ -> s_exp e

and s_const c = tostring (d_const () c)
and s_type typ = tostring (d_type () typ)
and s_stmt s = tostring (d_stmt () s)
and s_lv (lh, offset) = s_lhost lh ^ s_offset offset

and s_lhost = function
  | Var vi -> (if vi.vglob then "@" else "") ^ vi.vname
  | Mem e -> "*" ^ s_exp_paren2 e

and s_exp_paren2 e =
  match e with
  | Lval (_, NoOffset) -> s_exp e
  | Lval _ | UnOp _ | BinOp _ | Question _ | CastE _ -> "(" ^ s_exp e ^ ")"
  | _ -> s_exp e

and s_offset = function
  | NoOffset -> ""
  | Field (fi, offset) -> "." ^ fi.fname ^ s_offset offset
  | Index (e, offset) -> "[" ^ s_exp e ^ "]" ^ s_offset offset

and s_uop u = tostring (d_unop () u)
and s_bop b = tostring (d_binop () b)

and s_varinfo vi =
  let name = vi.vname in
  let typ = s_type vi.vtype in
  name ^ ":" ^ typ

and s_instr i =
  match i with
  | Set (lv, exp, _) -> "Set(" ^ s_lv lv ^ "," ^ s_exp exp ^ ")"
  | Call (Some lv, fexp, params, _) ->
      s_lv lv ^ ":= Call(" ^ s_exp fexp ^ s_exps params ^ ")"
  | Call (None, fexp, params, _) -> "Call(" ^ s_exp fexp ^ s_exps params ^ ")"
  | Asm _ -> "Asm"

and s_instrs instrs =
  List.fold_left ~f:(fun s i -> s ^ s_instr i) ~init:"" instrs

let s_node cil =
  match cil with
  | Global g -> s_glob g
  | Stmt s -> s_stmt s
  | Exp e -> s_exp e
  | Lval l -> s_lv l
  | Fun f -> "function:" ^ f
  | NotApplicable -> "NotApplicable"

let repr = function
  | Global g -> "Global (" ^ s_glob g ^ ")"
  | Stmt s -> "Stmt (" ^ s_stmt s ^ ")"
  | Exp e -> "Exp (" ^ s_exp e ^ ")"
  | Lval l -> "Lval (" ^ s_lv l ^ ")"
  | Fun f -> "Function (" ^ f ^ ")"
  | NotApplicable -> "NotApplicable"

let pp_path fmt path =
  List.iter ~f:(fun node -> Format.fprintf fmt "%s\n -->\n" (s_node node)) path

let is_cil_goto = function
  | Goto (s, _) ->
      List.exists
        ~f:(function
          | Label (name, _, _) ->
              String.is_prefix ~prefix:"while_break" name
              || String.is_prefix ~prefix:"while_continue" name
          | _ -> false)
        !s.labels
  | _ -> false

let is_empty_instr stmt = match stmt.skind with Instr [] -> true | _ -> false

let pp_path fmt path =
  List.iter ~f:(fun node -> Format.fprintf fmt "%s\n -->\n" (s_node node)) path

let eq_typ typ_info1 typ_info2 =
  match (typ_info1, typ_info2) with
  | TVoid _, TVoid _
  | TInt _, TInt _
  | TFloat _, TFloat _
  | TPtr _, TPtr _
  | TArray _, TArray _
  | TFun _, TFun _
  | TNamed _, TNamed _
  | TComp _, TComp _
  | TEnum _, TEnum _ ->
      true
  | _ -> String.equal (s_type typ_info1) (s_type typ_info2)

let eq_tmpvar str1 str2 =
  let type1 = Str.regexp "in[0-9]+" in
  let type2 = Str.regexp "tmp___[0-9]+" in
  let type3 = Str.regexp "c[0-9]+" in
  let type4 = Str.regexp "v[0-9]+" in
  let type5 = Str.regexp "ret_.*[0-9]+" in
  let type6 = Str.regexp "val[0-9]+" in
  let type7 = Str.regexp "ptr[0-9]+" in
  let type8 = Str.regexp "__cil_tmp[0-9]+" in
  let type9 = Str.regexp "tmp[0-9]+" in
  let regex_lst =
    [ type1; type2; type3; type4; type5; type6; type7; type8; type9 ]
  in
  let rec aux regex_lst =
    match regex_lst with
    | [] -> false
    | hd :: tl ->
        if Str.string_match hd str1 0 && Str.string_match hd str2 0 then true
        else aux tl
  in
  aux regex_lst

let eq_var s1 s2 = if eq_tmpvar s1 s2 then true else String.equal s1 s2
let isom_exp e1 e2 = String.equal (s_exp e1) (s_exp e2)
let isom_lv l1 l2 = String.equal (s_lv l1) (s_lv l2)
let is_loop = function Loop _ -> true | _ -> false

let eq_bop a b =
  match (a, b) with
  | PlusA, PlusA
  | PlusPI, PlusPI
  | IndexPI, IndexPI
  | MinusA, MinusA
  | MinusPI, MinusPI
  | MinusPP, MinusPP
  | Mod, Mod
  | Shiftlt, Shiftlt
  | Shiftrt, Shiftrt
  | BAnd, BAnd
  | BXor, BXor
  | BOr, BOr
  | Mult, Mult
  | Div, Div
  | Eq, Eq
  | Ne, Ne
  | Lt, Lt
  | Le, Le
  | Gt, Gt
  | Ge, Ge
  | LAnd, LAnd
  | LOr, LOr ->
      true
  | _ -> false

let eq_uop a b =
  match (a, b) with LNot, LNot | BNot, BNot | Neg, Neg -> true | _ -> false

let rec eq_exp (a : exp) (b : exp) =
  match (a, b) with
  | Lval (Var a, NoOffset), Lval (Var b, NoOffset) -> eq_var a.vname b.vname
  | Lval (Mem a, NoOffset), Lval (Mem b, NoOffset) -> eq_exp a b
  | BinOp (a, b, c, _), BinOp (d, e, f, _) ->
      eq_bop a d && eq_exp b e && eq_exp c f
  | UnOp (a, b, _), UnOp (c, d, _) -> eq_uop a c && eq_exp b d
  | CastE (a, b), CastE (c, d) -> eq_typ a c && eq_exp b d
  | AddrOf (Var a, NoOffset), AddrOf (Var b, NoOffset) -> eq_var a.vname b.vname
  | AddrOf (Mem a, NoOffset), AddrOf (Mem b, NoOffset) -> eq_exp a b
  | StartOf (Var a, NoOffset), StartOf (Var b, NoOffset) ->
      eq_var a.vname b.vname
  | StartOf (Mem a, NoOffset), StartOf (Mem b, NoOffset) -> eq_exp a b
  | SizeOfE a, SizeOfE b -> eq_exp a b
  | Const a, Const b -> String.equal (s_const a) (s_const b)
  | Lval (Var a, NoOffset), StartOf (Var b, NoOffset)
  | StartOf (Var a, NoOffset), Lval (Var b, NoOffset) ->
      eq_var a.vname b.vname
  | Question (a, b, c, _), Question (d, e, f, _) ->
      eq_exp a d && eq_exp b e && eq_exp c f
  | _ -> isom_exp a b

let rec diff_exp (a : exp) (b : exp) =
  match (a, b) with
  | Lval (Var a', NoOffset), Lval (Var b', NoOffset) ->
      if eq_var a'.vname b'.vname then [] else [ (a, b) ]
  | Lval (Mem a', NoOffset), Lval (Mem b', NoOffset) -> diff_exp a' b'
  | BinOp (a', b', c', _), BinOp (d', e', f', _) ->
      if eq_bop a' d' then diff_exp b' e' @ diff_exp c' f' else [ (a, b) ]
  | UnOp (a', b', _), UnOp (c', d', _) ->
      if eq_uop a' c' then diff_exp b' d' else [ (a, b) ]
  | CastE (a', b'), CastE (c', d') ->
      if eq_typ a' c' && eq_exp b' d' then [] else [ (a, b) ]
  | AddrOf (Var a', NoOffset), AddrOf (Var b', NoOffset) ->
      if eq_var a'.vname b'.vname then [] else [ (a, b) ]
  | AddrOf (Mem a', NoOffset), AddrOf (Mem b', NoOffset) ->
      if eq_exp a' b' then [] else diff_exp a' b'
  | StartOf (Var a', NoOffset), StartOf (Var b', NoOffset) ->
      if eq_var a'.vname b'.vname then [] else [ (a, b) ]
  | StartOf (Mem a', NoOffset), StartOf (Mem b', NoOffset) -> diff_exp a' b'
  | SizeOfE a', SizeOfE b' -> diff_exp a' b'
  | Const a', Const b' ->
      if String.equal (s_const a') (s_const b') then [] else [ (a, b) ]
  | Lval (Var a', NoOffset), StartOf (Var b', NoOffset)
  | StartOf (Var a', NoOffset), Lval (Var b', NoOffset) ->
      if eq_var a'.vname b'.vname then [] else [ (a, b) ]
  | Question (a', b', c', _), Question (d', e', f', _) ->
      diff_exp a' d' @ diff_exp b' e' @ diff_exp c' f'
  | _ -> if isom_exp a b then [] else [ (a, b) ]

let eq_lval (l1 : lval) (l2 : lval) =
  match (l1, l2) with
  | (host1, _), (host2, _) -> (
      match (host1, host2) with
      | Var vinfo1, Var vinfo2 ->
          eq_var vinfo1.vname vinfo2.vname && eq_typ vinfo1.vtype vinfo2.vtype
      | Mem mem1, Mem mem2 -> eq_exp mem1 mem2
      | _ -> false)

let eq_instr i1 i2 =
  if List.is_empty i1 && List.is_empty i2 then true
  else if List.is_empty i1 || List.is_empty i2 then false
  else
    match (i1, i2) with
    | Set (lv1, _, _) :: _, Set (lv2, _, _) :: _ -> eq_lval lv1 lv2
    | Call (lv1, _, _, _) :: _, Call (lv2, _, _, _) :: _ -> (
        match (lv1, lv2) with
        | None, None -> true
        | Some lv1, Some lv2 -> isom_lv lv1 lv2
        | _ -> false)
    | Asm _ :: _, Asm _ :: _ -> true
    | _ -> false

let rec eq_stmt skind1 skind2 =
  match (skind1, skind2) with
  | Instr i1, Instr i2 -> eq_instr i1 i2
  | Return (Some e1, _), Return (Some e2, _) -> isom_exp e1 e2
  | Return (None, _), Return (None, _) -> true
  | Goto (dest1, _), Goto (dest2, _) ->
      if eq_stmt !dest1.skind !dest2.skind then true else false
  | If (cond1, _, _, _), If (cond2, _, _, _) -> eq_exp cond1 cond2
  | Loop _, Loop _
  | ComputedGoto _, ComputedGoto _
  | Block _, Block _
  | TryExcept _, TryExcept _
  | TryFinally _, TryFinally _
  | Break _, Break _
  | Continue _, Continue _ ->
      true
  | _ -> false

let eq_blk (b1 : block) (b2 : block) =
  let stmts1 = b1.bstmts in
  let stmts2 = b2.bstmts in
  let rec aux stmts1 stmts2 =
    match (stmts1, stmts2) with
    | [], [] -> true
    | [], _ | _, [] -> false
    | hd1 :: tl1, hd2 :: tl2 ->
        if eq_stmt hd1.skind hd2.skind then aux tl1 tl2 else false
  in
  aux stmts1 stmts2

let eq_loc_stmt s1 s2 =
  String.equal
    (get_stmtLoc s1.skind |> s_location)
    (get_stmtLoc s2.skind |> s_location)

let isom_stmt s1 s2 = String.equal (s_stmt s1) (s_stmt s2)
let eq_location l1 l2 = String.equal (s_location l1) (s_location l2)

let eq_global glob1 glob2 =
  match (glob1, glob2) with
  | GFun (func_info1, _), GFun (func_info2, _) ->
      String.equal func_info1.svar.vname func_info2.svar.vname
  | GType (typinfo1, _), GType (typinfo2, _) ->
      String.equal typinfo1.tname typinfo2.tname
      && eq_typ typinfo1.ttype typinfo2.ttype
  | GCompTag _, GCompTag _
  | GCompTagDecl _, GCompTagDecl _
  | GEnumTag _, GEnumTag _
  | GEnumTagDecl _, GEnumTagDecl _ ->
      true
  | GVarDecl (v1, _), GVarDecl (v2, _) -> String.equal v1.vname v2.vname
  | GVar _, GVar _ | GAsm _, GAsm _ | GPragma _, GPragma _ | GText _, GText _ ->
      true
  | _ -> false

let cil_stmts = ref []

class copyStmtVisitor =
  object
    inherit nopCilVisitor

    method! vstmt stmt =
      cil_stmts := stmt :: !cil_stmts;
      DoChildren
  end

let extract_stmts file =
  cil_stmts := [];
  let vis = new copyStmtVisitor in
  visitCilFile vis file;
  !cil_stmts

let extract_globs file = file.globals

let glob2func_name glob =
  match glob with
  | GFun (func_info, _) -> func_info.svar.vname
  | _ -> L.error "Not a function"

let eq_exp_ref e1 e2 = String.equal e1 e2 || String.equal e1 ("&" ^ e2)

let extract_snk_stmt ast_map snk =
  Hashtbl.find_opt ast_map snk |> fun snk ->
  match snk with
  | Some s -> ( match s with Stmt s -> Some s | _ -> None)
  | None -> None

let found_stmt = ref []

class findStmtVisitor stmt =
  object
    inherit nopCilVisitor

    method! vstmt s =
      if isom_stmt s stmt then found_stmt := s :: !found_stmt;
      DoChildren
  end

let get_patent_path stmt ast =
  let rec aux stmt acc =
    found_stmt := [];
    let vis = new findStmtVisitor stmt in
    visitCilFile vis ast;
    if List.length !found_stmt = 1 then
      let stmt = List.hd_exn !found_stmt in
      stmt :: acc |> aux stmt
    else acc
  in
  aux stmt []
