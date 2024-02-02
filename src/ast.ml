open Cil

type t =
  | Global of global
  | Fun of string
  | Stmt of stmt
  | Exp of exp
  | Lval of lval
  | NotApplicable

(* for the reference *)
type edge = t * t
type subtree = edge list
type path = t list

let globs2path globs = List.map (fun g -> Global g) globs
let stmts2path stmts = List.map (fun s -> Stmt s) stmts
let exps2path exps = List.map (fun e -> Exp e) exps

let glob2ast element =
  match element with None -> NotApplicable | Some x -> Global x

let stmt2ast element =
  match element with None -> NotApplicable | Some x -> Stmt x

let exp2ast element =
  match element with None -> NotApplicable | Some x -> Exp x

let lval2ast element =
  match element with None -> NotApplicable | Some x -> Lval x

let ast2stmt element =
  match element with Stmt x -> x | _ -> failwith "Not a statement"

let path2stmts path = List.map ast2stmt path
let compare = compare
let flip f y x = f x y
let list_fold f list init = List.fold_left (flip f) init list
let link_by_sep sep s acc = if acc = "" then s else acc ^ sep ^ s

let string_of_list ?(first = "[") ?(last = "]") ?(sep = ";") string_of_v list =
  let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
  first ^ list_fold add_string_of_v list "" ^ last

let get_loc_filename (loc : Cil.location) =
  try
    let idx = String.rindex loc.file '/' in
    let len = String.length loc.file in
    String.sub loc.file (idx + 1) (len - idx - 1)
  with _ -> loc.file

let get_loc_line (loc : Cil.location) = loc.line

let get_global_loc glob =
  match glob with
  | Cil.GFun (_, loc)
  | Cil.GVar (_, _, loc)
  | Cil.GType (_, loc)
  | Cil.GCompTag (_, loc)
  | Cil.GCompTagDecl (_, loc)
  | Cil.GEnumTag (_, loc)
  | Cil.GEnumTagDecl (_, loc)
  | Cil.GVarDecl (_, loc)
  | Cil.GAsm (_, loc)
  | Cil.GPragma (_, loc) ->
      loc
  | _ -> failwith "get_global_loc error"

let s_location (loc : Cil.location) =
  get_loc_filename loc ^ ":" ^ string_of_int loc.line

let tostring s = Escape.escape_string (Pretty.sprint ~width:0 s)

let s_glob g =
  match g with
  | GFun (f, _) -> "function:" ^ f.svar.vname
  | _ -> Cil.printGlobal !Cil.printerForMaincil () g |> Pretty.sprint ~width:80

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

and s_instr i =
  match i with
  | Set (lv, exp, _) -> "Set(" ^ s_lv lv ^ "," ^ s_exp exp ^ ")"
  | Call (Some lv, fexp, params, _) ->
      s_lv lv ^ ":= Call(" ^ s_exp fexp ^ s_exps params ^ ")"
  | Call (None, fexp, params, _) -> "Call(" ^ s_exp fexp ^ s_exps params ^ ")"
  | Asm _ -> "Asm"

and s_instrs instrs = List.fold_left (fun s i -> s ^ s_instr i) "" instrs

let s_node cil =
  match cil with
  | Global g -> s_glob g
  | Stmt s -> s_stmt s
  | Exp e -> s_exp e
  | Lval l -> s_lv l
  | Fun f -> "function:" ^ f
  | NotApplicable -> "NotApplicable"

let is_empty_instr stmt =
  match stmt.Cil.skind with Cil.Instr [] -> true | _ -> false

let pp_path fmt path =
  List.iter (fun node -> Format.fprintf fmt "%s\n -->\n" (s_node node)) path

let eq_typ typ_info1 typ_info2 =
  match (typ_info1, typ_info2) with
  | Cil.TVoid _, Cil.TVoid _
  | Cil.TInt _, Cil.TInt _
  | Cil.TFloat _, Cil.TFloat _
  | Cil.TPtr _, Cil.TPtr _
  | Cil.TArray _, Cil.TArray _
  | Cil.TFun _, Cil.TFun _
  | Cil.TNamed _, Cil.TNamed _
  | Cil.TComp _, Cil.TComp _
  | Cil.TEnum _, Cil.TEnum _ ->
      true
  | _ -> s_type typ_info1 = s_type typ_info2

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

let eq_var s1 s2 = if eq_tmpvar s1 s2 then true else s1 = s2
let isom_exp e1 e2 = s_exp e1 = s_exp e2
let isom_lv l1 l2 = s_lv l1 = s_lv l2

let isom_stmt s1 s2 =
  let remove_first_line str =
    try
      let idx = String.index str '\n' in
      String.sub str (idx + 1) (String.length str - idx - 1)
    with _ -> str
  in
  let str1 = remove_first_line (s_stmt s1) in
  let str2 = remove_first_line (s_stmt s2) in
  String.equal str1 str2

let rec eq_exp (a : Cil.exp) (b : Cil.exp) =
  match (a, b) with
  | Lval (Var a, NoOffset), Lval (Var b, NoOffset) -> eq_var a.vname b.vname
  | Lval (Mem a, NoOffset), Lval (Mem b, NoOffset) -> eq_exp a b
  | BinOp (a, b, c, _), BinOp (d, e, f, _) -> a = d && eq_exp b e && eq_exp c f
  | UnOp (a, b, _), UnOp (c, d, _) -> a = c && eq_exp b d
  | CastE (a, b), CastE (c, d) -> eq_typ a c && eq_exp b d
  | AddrOf (Var a, NoOffset), AddrOf (Var b, NoOffset) -> eq_var a.vname b.vname
  | AddrOf (Mem a, NoOffset), AddrOf (Mem b, NoOffset) -> eq_exp a b
  | StartOf (Var a, NoOffset), StartOf (Var b, NoOffset) ->
      eq_var a.vname b.vname
  | StartOf (Mem a, NoOffset), StartOf (Mem b, NoOffset) -> eq_exp a b
  | Cil.SizeOfE a, Cil.SizeOfE b -> eq_exp a b
  | Const a, Const b -> a = b
  | Lval (Var a, NoOffset), StartOf (Var b, NoOffset)
  | StartOf (Var a, NoOffset), Lval (Var b, NoOffset) ->
      eq_var a.vname b.vname
  | Question (a, b, c, _), Question (d, e, f, _) ->
      eq_exp a d && eq_exp b e && eq_exp c f
  | _ -> isom_exp a b

let eq_lval (l1 : Cil.lval) (l2 : Cil.lval) =
  match (l1, l2) with
  | (host1, _), (host2, _) -> (
      match (host1, host2) with
      | Var vinfo1, Var vinfo2 ->
          eq_var vinfo1.vname vinfo2.vname && eq_typ vinfo1.vtype vinfo2.vtype
      | Mem mem1, Mem mem2 -> eq_exp mem1 mem2
      | _ -> false)

let eq_instr i1 i2 =
  if i1 = [] && i2 = [] then true
  else if i1 = [] || i2 = [] then false
  else
    let instr1 = List.hd i1 in
    let instr2 = List.hd i2 in
    match (instr1, instr2) with
    | Cil.Set (lv1, _, _), Cil.Set (lv2, _, _) -> eq_lval lv1 lv2
    | Cil.Call (lv1, _, _, _), Cil.Call (lv2, _, _, _) -> (
        match (lv1, lv2) with
        | None, None -> true
        | Some lv1, Some lv2 -> isom_lv lv1 lv2
        | _ -> false)
    | Cil.Asm _, Cil.Asm _ -> true
    | _ -> false

let rec eq_stmt skind1 skind2 =
  match (skind1, skind2) with
  | Cil.Instr i1, Cil.Instr i2 -> eq_instr i1 i2
  | Cil.Return (Some e1, _), Cil.Return (Some e2, _) -> isom_exp e1 e2
  | Cil.Return (None, _), Cil.Return (None, _) -> true
  | Cil.Goto (dest1, _), Cil.Goto (dest2, _) ->
      if eq_stmt !dest1.skind !dest2.skind then true else false
  | Cil.If (cond1, _, _, _), Cil.If (cond2, _, _, _) -> eq_exp cond1 cond2
  | Cil.Loop _, Cil.Loop _
  | Cil.ComputedGoto _, Cil.ComputedGoto _
  | Cil.Block _, Cil.Block _
  | Cil.TryExcept _, Cil.TryExcept _
  | Cil.TryFinally _, Cil.TryFinally _
  | Cil.Break _, Cil.Break _
  | Cil.Continue _, Cil.Continue _ ->
      true
  | _ -> false

let eq_global glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      eq_typ func_info1.svar.vtype func_info2.svar.vtype
      && func_info1.svar.vname = func_info2.svar.vname
  | Cil.GType (typinfo1, _), Cil.GType (typinfo2, _) ->
      typinfo1.tname = typinfo2.tname && eq_typ typinfo1.ttype typinfo2.ttype
  | Cil.GCompTag _, Cil.GCompTag _
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _
  | Cil.GEnumTag _, Cil.GEnumTag _
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _ ->
      true
  | Cil.GVarDecl (v1, _), Cil.GVarDecl (v2, _) -> v1.vname = v2.vname
  | Cil.GVar _, Cil.GVar _
  | Cil.GAsm _, Cil.GAsm _
  | Cil.GPragma _, Cil.GPragma _
  | Cil.GText _, Cil.GText _ ->
      true
  | _ -> false

let cil_stmts = ref []

class copyStmtVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vstmt stmt =
      cil_stmts := stmt :: !cil_stmts;
      DoChildren
  end

let extract_stmts file =
  cil_stmts := [];
  let vis = new copyStmtVisitor in
  ignore (Cil.visitCilFile vis file);
  !cil_stmts

let extract_globs file = file.Cil.globals
