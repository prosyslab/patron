module J = Yojson.Basic.Util
module H = TransformerHelper
module D = Diff

module SElement = struct
  type t =
    | SNull
    | SGlob of sym_global
    | SStmt of sym_stmt
    | SExp of sym_exp
    | SLval of sym_lval

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

  and sym_compinfo = {
    cname : string;
    cfields : sym_fieldinfo list;
    cstruct : bool;
  }

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
  and sym_lval = sym_lhost * sym_offset

  and sym_stmt =
    | SSNull
    | SIf of sym_node * sym_node list * sym_node list
    | SSet of sym_node * sym_node
    | SCall of sym_node option * sym_node * sym_node list
    | SReturn of sym_node option
    | SBlock of sym_node list
    | SGoto of sym_node

  and sym_global =
    | SGNull
    | SGID of string
    | SGFun of string * string
    | GVar of string * string

  and sym_node = {
    node : t;
    id : string;
    literal : string;
    cil : Diff.CilElement.t;
  }

  let rec pp_node fmt e =
    match e.node with
    | SNull -> Format.fprintf fmt "SNull"
    | SStmt s -> Format.fprintf fmt "SStmt(%a)" pp_sstmt s
    | SExp e -> Format.fprintf fmt "SExp(%a)" pp_sexp e
    | SLval l -> Format.fprintf fmt "SLval(%a)" pp_slval l
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

  and pp_soptlval fmt l =
    match l with None -> Format.fprintf fmt "None" | Some l -> pp_node fmt l

  and pp_svarinfo fmt v =
    Format.fprintf fmt "SVarInfo(%s, %a)" v.vname pp_styp v.vtype

  and pp_slval fmt l =
    let lhost, _ = l in
    match lhost with
    | SVar v -> Format.fprintf fmt "LVar(%a)" pp_svarinfo v
    | SMem e -> Format.fprintf fmt "LMem(%a)" pp_node e

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

  and pp_senuminfo fmt e =
    Format.fprintf fmt "SEnumInfo(%s, %a)" e.ename pp_senumitem_lst e.eitems

  and pp_senumitem_lst fmt lst =
    Format.fprintf fmt "[";
    List.iter (fun (s, n) -> Format.fprintf fmt "(%s, %a), " s pp_node n) lst;
    Format.fprintf fmt "]"

  and pp_scompinfo fmt c =
    Format.fprintf fmt "SCompInfo(%s, %a, %b)" c.cname pp_sfieldinfo_lst
      c.cfields c.cstruct

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

module SDiff = struct
  include SElement

  type sym_context = {
    parent : (string * Diff.CilElement.t) list;
    func_name : string;
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

  let rec mk_sdiff ctx cfg exp_map diff =
    match diff with
    | D.Diff.InsertStmt (_, s) ->
        SInsertStmt
          ( ctx,
            {
              node = SStmt (match_stmt cfg exp_map s);
              id = match_stmt_id cfg s.Cil.skind;
              literal = H.string_of_stmt s;
              cil = Diff.CilElement.EStmt s;
            } )
    | D.Diff.DeleteStmt (_, s) ->
        SDeleteStmt
          ( ctx,
            {
              node = SStmt (match_stmt cfg exp_map s);
              id = match_stmt_id cfg s.Cil.skind;
              literal = H.string_of_stmt s;
              cil = Diff.CilElement.EStmt s;
            } )
    | _ -> failwith "mk_sdiff: not implemented"

  and match_stmt cfg exp_map s =
    match s.Cil.skind with
    | Cil.If (e, s1, s2, _) ->
        SElement.SIf
          ( {
              node = SExp (match_exp cfg exp_map e);
              id = match_exp_id exp_map e;
              literal = H.string_of_exp e;
              cil = Diff.CilElement.EExp e;
            },
            List.map
              (fun s ->
                {
                  SElement.node = SStmt (match_stmt cfg exp_map s);
                  id = match_stmt_id cfg s.Cil.skind;
                  literal = H.string_of_stmt s;
                  cil = Diff.CilElement.EStmt s;
                })
              s1.Cil.bstmts,
            List.map
              (fun s ->
                {
                  SElement.node = SStmt (match_stmt cfg exp_map s);
                  id = match_stmt_id cfg s.Cil.skind;
                  literal = H.string_of_stmt s;
                  cil = Diff.CilElement.EStmt s;
                })
              s2.Cil.bstmts )
    | Cil.Instr i -> (
        let i = List.hd i in
        match i with
        | Cil.Set (l, e, _) ->
            SElement.SSet
              ( {
                  node = SLval (match_lval cfg exp_map l);
                  id = match_lval_id exp_map l;
                  literal = H.string_of_lval l;
                  cil = Diff.CilElement.ELval l;
                },
                {
                  node = SExp (match_exp cfg exp_map e);
                  id = match_exp_id exp_map e;
                  literal = H.string_of_exp e;
                  cil = Diff.CilElement.EExp e;
                } )
        | Cil.Call (Some l, e, es, _) ->
            SElement.SCall
              ( Some
                  {
                    node = SLval (match_lval cfg exp_map l);
                    id = match_lval_id exp_map l;
                    literal = H.string_of_lval l;
                    cil = Diff.CilElement.ELval l;
                  },
                {
                  node = SExp (match_exp cfg exp_map e);
                  id = match_exp_id exp_map e;
                  literal = H.string_of_exp e;
                  cil = Diff.CilElement.EExp e;
                },
                List.map
                  (fun e ->
                    {
                      SElement.node = SExp (match_exp cfg exp_map e);
                      id = match_exp_id exp_map e;
                      literal = H.string_of_exp e;
                      cil = Diff.CilElement.EExp e;
                    })
                  es )
        | Cil.Call (None, e, es, _) ->
            SElement.SCall
              ( None,
                {
                  node = SExp (match_exp cfg exp_map e);
                  id = match_exp_id exp_map e;
                  literal = H.string_of_exp e;
                  cil = Diff.CilElement.EExp e;
                },
                List.map
                  (fun e ->
                    {
                      SElement.node = SExp (match_exp cfg exp_map e);
                      id = match_exp_id exp_map e;
                      literal = H.string_of_exp e;
                      cil = Diff.CilElement.EExp e;
                    })
                  es )
        | _ -> failwith "match_stmt: not supported")
    | Cil.Block b ->
        let bl =
          List.fold_left
            (fun (acc : SElement.sym_node list) s ->
              {
                node = SStmt (match_stmt cfg exp_map s);
                id = match_stmt_id cfg s.Cil.skind;
                literal = H.string_of_stmt s;
                cil = Diff.CilElement.EStmt s;
              }
              :: acc)
            [] b.bstmts
          |> List.rev
        in
        SElement.SBlock bl
    | Cil.Return (Some e, _) ->
        SElement.SReturn
          (Some
             {
               node = SExp (match_exp cfg exp_map e);
               id = match_exp_id exp_map e;
               literal = H.string_of_exp e;
               cil = Diff.CilElement.EExp e;
             })
    | Cil.Return (None, _) -> SElement.SReturn None
    | Cil.Goto (s, _) ->
        SElement.SGoto
          {
            node = SStmt (match_stmt cfg exp_map !s);
            id = match_stmt_id cfg !s.Cil.skind;
            literal = H.string_of_stmt !s;
            cil = Diff.CilElement.EStmt !s;
          }
    | _ -> failwith "match_stmt: not implemented"

  and match_exp cfg exp_map e =
    match e with
    | Cil.Const c -> SElement.SConst (to_sconst c)
    | Cil.Lval l ->
        SELval
          {
            node = SLval (match_lval cfg exp_map l);
            id = match_lval_id exp_map l;
            literal = H.string_of_lval l;
            cil = Diff.CilElement.ELval l;
          }
    | Cil.SizeOf t -> SSizeOf (to_styp t)
    | Cil.SizeOfE e' ->
        SSizeOfE
          {
            node = SExp (match_exp cfg exp_map e');
            id = match_exp_id exp_map e';
            literal = H.string_of_exp e';
            cil = Diff.CilElement.EExp e';
          }
    | Cil.SizeOfStr s -> SSizeOfStr s
    | Cil.BinOp (op, e1, e2, t) ->
        SBinOp
          ( to_sbinop op,
            {
              node = SExp (match_exp cfg exp_map e1);
              id = match_exp_id exp_map e1;
              literal = H.string_of_exp e1;
              cil = Diff.CilElement.EExp e1;
            },
            {
              node = SExp (match_exp cfg exp_map e2);
              id = match_exp_id exp_map e2;
              literal = H.string_of_exp e2;
              cil = Diff.CilElement.EExp e2;
            },
            to_styp t )
    | Cil.UnOp (op, e, t) ->
        SUnOp
          ( to_sunop op,
            {
              node = SExp (match_exp cfg exp_map e);
              id = match_exp_id exp_map e;
              literal = H.string_of_exp e;
              cil = Diff.CilElement.EExp e;
            },
            to_styp t )
    | Cil.CastE (t, e) ->
        SCastE
          ( to_styp t,
            {
              node = SExp (match_exp cfg exp_map e);
              id = match_exp_id exp_map e;
              literal = H.string_of_exp e;
              cil = Diff.CilElement.EExp e;
            } )
    | Cil.Question (e1, e2, e3, t) ->
        SQuestion
          ( {
              node = SExp (match_exp cfg exp_map e1);
              id = match_exp_id exp_map e1;
              literal = H.string_of_exp e1;
              cil = Diff.CilElement.EExp e1;
            },
            {
              node = SExp (match_exp cfg exp_map e2);
              id = match_exp_id exp_map e2;
              literal = H.string_of_exp e2;
              cil = Diff.CilElement.EExp e2;
            },
            {
              node = SExp (match_exp cfg exp_map e3);
              id = match_exp_id exp_map e3;
              literal = H.string_of_exp e3;
              cil = Diff.CilElement.EExp e3;
            },
            to_styp t )
    | Cil.AddrOf l ->
        SAddrOf
          {
            node = SLval (match_lval cfg exp_map l);
            id = match_lval_id exp_map l;
            literal = H.string_of_lval l;
            cil = Diff.CilElement.ELval l;
          }
    | Cil.StartOf l ->
        SStartOf
          {
            node = SLval (match_lval cfg exp_map l);
            id = match_lval_id exp_map l;
            literal = H.string_of_lval l;
            cil = Diff.CilElement.ELval l;
          }
    | Cil.AddrOfLabel stmt ->
        SAddrOfLabel
          {
            node = SStmt (match_stmt cfg exp_map !stmt);
            id = match_stmt_id cfg !stmt.Cil.skind;
            literal = H.string_of_stmt !stmt;
            cil = Diff.CilElement.EStmt !stmt;
          }
    | _ -> failwith "match_exp: not implemented"

  and match_lval cfg exp_map l =
    let lhost, offset = l in
    let slhost =
      match lhost with
      | Cil.Var v -> SElement.SVar { vname = v.vname; vtype = to_styp v.vtype }
      | Cil.Mem e ->
          SElement.SMem
            {
              node = SExp (match_exp cfg exp_map e);
              id = match_exp_id exp_map e;
              literal = H.string_of_exp e;
              cil = Diff.CilElement.EExp e;
            }
    in
    let soffset = match_offset cfg exp_map offset in
    (slhost, soffset)

  and match_offset cfg exp_map o =
    match o with
    | Cil.NoOffset -> SElement.SNoOffset
    | Cil.Field (f, o) ->
        SElement.SField
          ( {
              fcomp = { cname = f.fcomp.cname; cfields = []; cstruct = true };
              fname = f.fname;
              ftype = to_styp f.ftype;
            },
            match_offset cfg exp_map o )
    | Cil.Index (e, o) ->
        SElement.SIndex
          ( {
              node = SExp (match_exp cfg exp_map e);
              id = match_exp_id exp_map e;
              literal = H.string_of_exp e;
              cil = Diff.CilElement.EExp e;
            },
            match_offset cfg exp_map o )

  and match_fieldinfo f =
    {
      SElement.fcomp = match_compinfo f.Cil.fcomp;
      SElement.fname = f.Cil.fname;
      SElement.ftype = to_styp f.Cil.ftype;
    }

  and match_compinfo c =
    {
      SElement.cname = c.Cil.cname;
      SElement.cfields = List.map match_fieldinfo c.Cil.cfields;
      SElement.cstruct = c.Cil.cstruct;
    }

  and extract_fun_name g =
    match g with
    | Cil.GFun (f, _) -> f.Cil.svar.Cil.vname
    | _ -> failwith "extract_fun_name: not a function"

  and match_context cfg exp_map lst =
    match lst with
    | [] -> []
    | hd :: tl -> (
        match hd with
        | D.CilElement.EStmt s ->
            (match_stmt_id cfg s.Cil.skind, hd) :: match_context cfg exp_map tl
        | D.CilElement.EExp e ->
            (match_exp_id exp_map e, hd) :: match_context cfg exp_map tl
        | D.CilElement.ELval l ->
            (match_lval_id exp_map l, hd) :: match_context cfg exp_map tl
        | D.CilElement.EGlobal g ->
            (extract_fun_name g, hd) :: match_context cfg exp_map tl
        | _ -> failwith "match_context: not implemented")

  and match_exp_id exp_map e =
    let candidate =
      match e with
      | Cil.Const c -> match_const c exp_map
      | Cil.Lval l ->
          H.StrMap.filter (fun _ v -> H.string_of_lval l |> H.subset v) exp_map
      | Cil.SizeOf t -> match_sizeof t exp_map
      | Cil.BinOp _ ->
          H.StrMap.filter (fun _ v -> H.string_of_exp e |> H.subset v) exp_map
      | Cil.UnOp _ ->
          H.StrMap.filter (fun _ v -> H.string_of_exp e |> H.subset v) exp_map
      | Cil.CastE _ ->
          H.StrMap.filter (fun _ v -> H.string_of_exp e |> H.subset v) exp_map
      | Cil.Question _ ->
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
      if outmap = [] then ("None", "") else List.hd outmap
    in
    id

  and match_sizeof t exp_map =
    H.StrMap.filter (fun _ v -> H.string_of_typ t |> H.subset v) exp_map

  and match_lval_id exp_map l =
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
      if outmap = [] then ("None", "") else List.hd outmap
    in
    id

  and eq_line loc cloc =
    let file_name = loc.Cil.file |> Filename.basename in
    if loc.Cil.line = cloc.H.line && file_name = cloc.H.file then true
    else false

  and match_set_id cfg loc =
    H.CfgMap.fold
      (fun k v acc ->
        match k with
        | H.CSet (_, _, cloc)
        | H.CAlloc (_, _, cloc)
        | H.CFalloc (_, _, cloc)
        | H.CSalloc (_, _, cloc) ->
            if eq_line loc cloc then v :: acc else acc
        | _ -> acc)
      cfg []

  and match_call_id cfg loc =
    H.CfgMap.fold
      (fun k v acc ->
        match k with
        | H.CCall (_, _, cloc) -> if eq_line loc cloc then v :: acc else acc
        | _ -> acc)
      cfg []

  and match_return_id cfg loc =
    H.CfgMap.fold
      (fun k v acc ->
        match k with
        | H.CReturn1 (_, cloc) -> if eq_line loc cloc then v :: acc else acc
        | H.CReturn2 cloc -> if eq_line loc cloc then v :: acc else acc
        | _ -> acc)
      cfg []

  and match_assume_id cfg loc cond =
    H.CfgMap.fold
      (fun k v acc ->
        match k with
        | H.CAssume (ccond, cloc) ->
            if eq_line loc cloc && H.string_of_exp cond |> H.subset ccond then
              v :: acc
            else acc
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
    | Cil.Loop _ -> "None"
    | _ -> "None"

  and match_const c exp_map =
    match c with
    | Cil.CInt64 (i, _, _) ->
        H.StrMap.filter (fun _ v -> Int64.to_string i |> H.subset v) exp_map
    | Cil.CStr s -> H.StrMap.filter (fun _ v -> s |> H.subset v) exp_map
    | Cil.CChr c ->
        H.StrMap.filter (fun _ v -> String.make 1 c |> H.subset v) exp_map
    | Cil.CReal (f, _, _) ->
        H.StrMap.filter (fun _ v -> string_of_float f |> H.subset v) exp_map
    | _ -> failwith "match_const: not implemented"

  and to_styp t =
    match t with
    | Cil.TVoid _ -> SVoid
    | Cil.TInt _ -> SInt
    | Cil.TFloat _ -> SFloat
    | Cil.TPtr (t', _) -> SPtr (to_styp t')
    | Cil.TArray (t', _, _) -> SArray (to_styp t')
    | Cil.TNamed (t', _) ->
        SNamed { sym_tname = t'.Cil.tname; sym_ttype = to_styp t'.ttype }
    | Cil.TFun _ -> failwith "TFun: not implemented"
    | Cil.TComp (c, _) ->
        SComp
          {
            cname = c.Cil.cname;
            cfields = List.map (fun x -> to_sfieldinfo x) c.cfields;
            cstruct = c.cstruct;
          }
    | Cil.TEnum _ -> failwith "TEnum: not implemented"
    | Cil.TBuiltin_va_list _ -> failwith "not supported"

  and to_scompinfo c =
    {
      cname = c.Cil.cname;
      cfields =
        List.fold_left (fun acc f -> to_sfieldinfo f :: acc) [] c.cfields;
      cstruct = c.cstruct;
    }

  and to_sfieldinfo f =
    { fcomp = to_scompinfo f.fcomp; fname = f.fname; ftype = to_styp f.ftype }

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
end

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

let define_sym_diff donor_dir donor diff =
  get_gvars donor;
  let sparrow_dir = Filename.concat donor_dir "sparrow-out" in
  let cfg, exp_map = H.parse_sparrow sparrow_dir in
  List.fold_left
    (fun acc d ->
      let root_path = get_parent_lst d in
      let s_root_path = List.rev root_path |> SDiff.match_context cfg exp_map in
      let root_func, _ = List.hd s_root_path in
      let rest_path = List.tl s_root_path in
      let parent_fun = get_parent_fun root_path in
      let cfg_reduced = reduce_cfg cfg parent_fun.vname in
      let s_context : SDiff.sym_context =
        { parent = rest_path; func_name = root_func }
      in
      SDiff.mk_sdiff s_context cfg_reduced exp_map d :: acc)
    [] diff

(* json area *)
module DiffJson = struct
  open SElement
  open SDiff

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
        `Assoc
          [
            ( "named",
              `Assoc
                [
                  ("tname", `String t.sym_tname);
                  ("typ", styp_to_sym t.sym_ttype);
                ] );
          ]
    | _ -> failwith "not supported"

  let sunop_to_sym op = match op with SNot -> "LNot" | SNeg -> "Neg"

  let rec mk_json_obj (saction : SDiff.t) (caction : D.Diff.t) =
    let context_json (context : SDiff.sym_context) =
      ( "context",
        `Assoc
          [
            ("func_name", `String context.func_name);
            ( "parent",
              `List
                (List.fold_left
                   (fun acc (id, _) -> `String id :: acc)
                   [] context.parent) );
          ] )
    in
    match (saction, caction) with
    | SInsertStmt (context1, snode), InsertStmt _ ->
        `Assoc
          [
            ("action", `String "insert_stmt");
            context_json context1;
            ("change", sstmt_to_json snode);
          ]
    | SDeleteStmt (context1, snode), DeleteStmt _ ->
        `Assoc
          [
            ("action", `String "delete_stmt");
            context_json context1;
            ("change", sstmt_to_json snode);
          ]
    | _ -> failwith "mk_json_obj: not implemented"

  and sstmt_to_json (sstmt : sym_node) =
    let node = sstmt.node in
    let stmt =
      match node with
      | SStmt s -> s
      | _ -> failwith "sstmt_to_json: undefined sstmt"
    in
    match stmt with
    | SIf (exp1, tb1, eb1) ->
        `Assoc
          [
            ( "if",
              `Assoc
                [
                  ( "node",
                    `Assoc
                      [
                        ("cond", sexp_to_json exp1);
                        ( "then",
                          `List
                            (List.rev
                               (List.fold_left
                                  (fun acc x -> sstmt_to_json x :: acc)
                                  [] tb1)) );
                        ( "else",
                          `List
                            (List.rev
                               (List.fold_left
                                  (fun acc x -> sstmt_to_json x :: acc)
                                  [] eb1)) );
                      ] );
                  ("id", `String sstmt.id);
                  ("literal", `String sstmt.literal);
                ] );
          ]
    | SSet (lv1, e1) ->
        `Assoc
          [
            ( "set",
              `Assoc
                [
                  ( "node",
                    `Assoc
                      [ ("lval", slval_to_json lv1); ("exp", sexp_to_json e1) ]
                  );
                  ("id", `String sstmt.id);
                  ("literal", `String sstmt.literal);
                ] );
          ]
    | SCall (Some lv1, e1, es1) ->
        `Assoc
          [
            ( "call",
              `Assoc
                [
                  ( "node",
                    `Assoc
                      [
                        ("lval", slval_to_json lv1);
                        ("exp", sexp_to_json e1);
                        ( "exps",
                          `List
                            (List.rev
                               (List.fold_left
                                  (fun acc x -> sexp_to_json x :: acc)
                                  [] es1)) );
                      ] );
                  ("id", `String sstmt.id);
                  ("literal", `String sstmt.literal);
                ] );
          ]
    | SCall (None, e1, es1) ->
        `Assoc
          [
            ( "call",
              `Assoc
                [
                  ( "node",
                    `Assoc
                      [
                        ("lval", `String "None");
                        ("exp", sexp_to_json e1);
                        ( "exps",
                          `List
                            (List.rev
                               (List.fold_left
                                  (fun acc x -> sexp_to_json x :: acc)
                                  [] es1)) );
                      ] );
                  ("id", `String sstmt.id);
                  ("literal", `String sstmt.literal);
                ] );
          ]
    | SReturn (Some e1) ->
        `Assoc
          [
            ( "return",
              `Assoc
                [
                  ("node", `Assoc [ ("exp", sexp_to_json e1) ]);
                  ("id", `String sstmt.id);
                  ("literal", `String sstmt.literal);
                ] );
          ]
    | SReturn None ->
        `Assoc
          [
            ( "return",
              `Assoc
                [
                  ("node", `Assoc [ ("exp", `String "None") ]);
                  ("id", `String sstmt.id);
                  ("literal", `String sstmt.literal);
                ] );
          ]
    | SGoto s1 ->
        `Assoc
          [
            ( "goto",
              `Assoc
                [
                  ("node", `Assoc [ ("stmt", sstmt_to_json s1) ]);
                  ("id", `String sstmt.id);
                  ("literal", `String sstmt.literal);
                ] );
          ]
    | _ ->
        (* SElement.pp_sstmt Format.std_formatter sstmt; *)
        `Null

  and sexp_to_json (sexp : SElement.sym_node) =
    let node = sexp.node in
    let exp =
      match node with
      | SExp e -> e
      | _ -> failwith "sexp_to_json: undefined sexp"
    in
    match exp with
    | SConst const ->
        `Assoc
          [
            ("node", `Assoc [ ("const", sconst_to_json const) ]);
            ("id", `String sexp.id);
            ("literal", `String sexp.literal);
          ]
    | SELval l -> `Assoc [ ("lval", slval_to_json l) ]
    | SSizeOfE e1 ->
        `Assoc
          [
            ("node", `Assoc [ ("sizeof", `Assoc [ ("e", sexp_to_json e1) ]) ]);
            ("id", `String sexp.id);
            ("literal", `String sexp.literal);
          ]
    | SBinOp (op1, e1_1, e2_1, typ1) ->
        `Assoc
          [
            ( "node",
              `Assoc
                [
                  ( "binop",
                    `Assoc
                      [
                        ("op", `String (sbinop_to_sym op1));
                        ("typ", styp_to_sym typ1);
                        ("e1", sexp_to_json e1_1);
                        ("e2", sexp_to_json e2_1);
                      ] );
                ] );
            ("id", `String sexp.id);
            ("literal", `String sexp.literal);
          ]
    | SCastE (typ, e1) ->
        `Assoc
          [
            ( "node",
              `Assoc
                [
                  ( "cast",
                    `Assoc [ ("typ", styp_to_sym typ); ("e", sexp_to_json e1) ]
                  );
                ] );
            ("id", `String sexp.id);
            ("literal", `String sexp.literal);
          ]
    | SUnOp (op1, e1_1, typ1) ->
        `Assoc
          [
            ( "node",
              `Assoc
                [
                  ( "unop",
                    `Assoc
                      [
                        ("op", `String (sunop_to_sym op1));
                        ("typ", styp_to_sym typ1);
                        ("e", sexp_to_json e1_1);
                      ] );
                ] );
            ("id", `String sexp.id);
            ("literal", `String sexp.literal);
          ]
    | _ ->
        SElement.pp_sexp Format.std_formatter exp;
        failwith "sexp_to_json: undefined sexp"

  and slval_to_json (slval : SElement.sym_node) =
    let node = slval.node in
    let lval =
      match node with
      | SLval l -> l
      | _ -> failwith "slval_to_json: undefined slval"
    in
    let lhost, offset = lval in
    `Assoc
      [
        ( "node",
          `Assoc
            [
              ( "lval",
                `Assoc
                  [
                    ("lhost", slhost_to_json lhost);
                    ("offset", soffset_to_json offset);
                  ] );
            ] );
        ("id", `String slval.id);
        ("literal", `String slval.literal);
      ]

  and slhost_to_json lhost =
    match lhost with
    | SVar v ->
        `Assoc
          [
            ( "var",
              `Assoc [ ("name", `String v.vname); ("typ", styp_to_sym v.vtype) ]
            );
          ]
    | SMem e -> `Assoc [ ("mem", `Assoc [ ("exp", sexp_to_json e) ]) ]

  and soffset_to_json offset =
    match offset with
    | SNoOffset -> `String "nooffset"
    | SField (f, o) ->
        `Assoc
          [
            ( "field",
              `Assoc
                [ ("field", sfield_to_json f); ("offset", soffset_to_json o) ]
            );
          ]
    | SIndex (e, o) ->
        `Assoc
          [
            ( "index",
              `Assoc [ ("exp", sexp_to_json e); ("offset", soffset_to_json o) ]
            );
          ]

  and sfield_to_json f =
    `Assoc
      [
        ( "field",
          `Assoc
            [
              ("comp", scomp_to_json f.fcomp);
              ("name", `String f.fname);
              ("typ", styp_to_sym f.ftype);
            ] );
      ]

  and scomp_to_json c =
    `Assoc
      [
        ( "comp",
          `Assoc
            [
              ("name", `String c.cname);
              ( "fields",
                `List
                  (List.rev
                     (List.fold_left
                        (fun acc x -> sfield_to_json x :: acc)
                        [] c.cfields)) );
              ("struct", `Bool c.cstruct);
            ] );
      ]

  and sconst_to_json (sconst : SElement.sym_const) =
    match sconst with
    | SIntConst i ->
        `Assoc
          [ ("type", `String "int"); ("literal", `String (Int.to_string i)) ]
    | SFloatConst f ->
        `Assoc
          [
            ("type", `String "float"); ("literal", `String (Float.to_string f));
          ]
    | SStringConst s ->
        `Assoc [ ("type", `String "str"); ("literal", `String s) ]
    | SCharConst c ->
        `Assoc
          [ ("type", `String "char"); ("literal", `String (String.make 1 c)) ]
end

let to_json sym_list conc_list out_dir =
  let conc_list = List.rev conc_list in
  let oc_diff_json = open_out (out_dir ^ "/diff.json") in
  let rec make_json (id : int) sym_list conc_list acc =
    match (sym_list, conc_list) with
    | [], [] -> acc
    | s_action :: s_rest, c_action :: c_rest ->
        let json_obj = DiffJson.mk_json_obj s_action c_action in
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
