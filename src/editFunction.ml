module J = Yojson.Basic.Util
module D = Diff
module S = SymDiff
module H = TransformerHelper

let parse_op op =
  match op with
  | "PlusA" -> S.SElement.SPlusA
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
      | "int" -> S.SElement.SInt
      | "float" -> SFloat
      | "void" -> SVoid
      | _ -> failwith "parse_typ: undefined behavior")
  | `Assoc [ ("ptr", `Assoc [ ("typ", t) ]) ] -> SPtr (parse_typ t)
  | _ -> failwith "parse_typ: undefined behavior"

(* let parse_lval_json lval =
   match lval with
   | `Assoc [ ("lval_id", lid); ("exp_id", eid) ] ->
       let lval_id = lid |> J.to_string in
       let exp_id = eid |> J.to_string in
       S.SElement.LID (S.SElement.LvalIDSet (lval_id, exp_id))
   | `Assoc [ ("id", lid) ] ->
       let id = lid |> J.to_string in
       S.SElement.LID (S.SElement.LvalID id)
   | `Assoc [ ("literal", str) ] ->
       let literal = str |> J.to_string in
       S.SElement.LID (S.SElement.IDNotAvailable literal)
   | _ -> failwith "parse_lval_json: undefined behavior" *)

let parse_const_json const id =
  match const with
  | `Assoc [ ("type", typ); ("literal", lit) ] -> (
      let t = J.to_string typ in
      let l = J.to_string lit in
      match t with
      | "int" -> S.SElement.SConst (SIntConst (int_of_string l), id)
      | "float" -> SConst (SFloatConst (float_of_string l), id)
      | "char" -> SConst (SCharConst (List.hd (H.explode l)), id)
      | "string" -> SConst (SStringConst l, id)
      | _ -> failwith "parse_const_json: undefined behavior")
  | _ -> failwith "parse_const_json: undefined behavior"

let rec parse_exp_json contents =
  let sub = J.member "sub" contents in
  let id = J.member "id" contents |> J.to_string in
  match sub with
  | `Assoc [ ("const", contents) ] -> parse_const_json contents id
  | `Assoc [ ("binop", contents) ] ->
      let op = parse_op (contents |> J.member "op" |> J.to_string) in
      let typ = parse_typ (contents |> J.member "typ") in
      let e1 = parse_exp_json (contents |> J.member "e1") in
      let e2 = parse_exp_json (contents |> J.member "e2") in
      S.SElement.SBinOp (op, e1, e2, typ, id)
  | `Assoc [ ("cast", contents) ] ->
      let typ = parse_typ (contents |> J.member "typ") in
      let e = parse_exp_json (contents |> J.member "e") in
      S.SElement.SCastE (typ, e, id)
  | `Assoc [ ("sizeof", contents) ] ->
      let e = parse_exp_json contents in
      S.SElement.SSizeOfE (e, id)
  | `Assoc [ ("lval", contents) ] ->
      let lv = contents |> J.to_string in
      S.SElement.SELval lv
  | _ -> failwith "parse_exp_json: undefined behavior"

let parse_return_json contents =
  let sub = J.member "sub" contents in
  let id = J.member "id" contents |> J.to_string in
  match sub with
  | `Assoc [ ("exp", exp) ] -> (
      match exp with
      | `String s ->
          if s = "None" then S.SElement.SReturn (None, id)
          else SReturn (Some (parse_exp_json exp), id)
      | `Assoc _ -> SReturn (Some (parse_exp_json exp), id)
      | _ -> failwith "parse_return_json: undefined behavior")
  | _ -> failwith "parse_return_json: undefined behavior"

let rec parse_if_json contents =
  let sub = J.member "sub" contents in
  let id = J.member "id" contents |> J.to_string in
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

      S.SElement.SIf (cond, then_block, else_block, id)
  | _ -> failwith "parse_if_json: undefined behavior"

and parse_stmt_json sym =
  match sym with
  | `Assoc [ (stmt_name, contents) ] -> (
      match stmt_name with
      | "if" -> parse_if_json contents
      | "return" -> parse_return_json contents
      | _ -> failwith "parse_stmt_json: not implemented")
  | _ -> failwith "parse_stmt_json: undefined behavior"

let parse_sym_json action context sym =
  let context =
    {
      S.SDiff.parent =
        context |> J.to_list |> List.map (fun x -> x |> J.to_string);
    }
  in
  match action with
  | "insert_stmt" -> SymDiff.SDiff.SInsertStmt (context, parse_stmt_json sym)
  | _ -> failwith "undefined action"

let parse_edit_function oc_diff =
  let diffs = oc_diff |> J.member "diffs" in
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

let rec translate_node node stmts =
  match stmts with
  | [] -> failwith "translate_node: unable to locate the translated node"
  | h :: t -> (
      match (node, h.Cil.skind) with
      | H.CNone, _ ->
          failwith "translate_node: unable to locate the translated node"
      | H.CSet (_, _, loc), Cil.Instr i | H.CCall (_, _, loc), Cil.Instr i -> (
          match List.hd i with
          | Cil.Call (_, _, _, cloc) ->
              let fn = Filename.basename cloc.Cil.file in
              if cloc.Cil.line = loc.line && fn = loc.file then h
              else translate_node node t
          | Cil.Set (_, _, cloc) ->
              let fn = Filename.basename cloc.Cil.file in
              if loc.line = loc.line && fn = loc.file then h
              else translate_node node t
          | _ -> translate_node node t)
      | H.CIf loc, Cil.If (_, _, _, cloc) ->
          let fn = Filename.basename cloc.Cil.file in
          if loc.line = loc.line && fn = loc.file then h
          else translate_node node t
      | H.CAssume (_, loc), Cil.If (_, _, _, cloc) ->
          let fn = Filename.basename cloc.Cil.file in
          if loc.line = loc.line && fn = loc.file then h
          else translate_node node t
      | H.CReturn1 (_, loc), Cil.Return (_, cloc)
      | H.CReturn2 loc, Cil.Return (_, cloc) ->
          let fn = Filename.basename cloc.Cil.file in
          if loc.line = loc.line && fn = loc.file then h
          else translate_node node t
      | _ -> translate_node node t)

(* Todo: exp ctx *)
let translate_context comp_map cfg stmts context =
  let rec convert_node ctx acc =
    match ctx with
    | [] -> acc
    | hd :: tl ->
        let c = H.StrMap.find hd comp_map in
        let found =
          H.CfgMap.fold (fun k v acc -> if v = c then k :: acc else acc) cfg []
          |> List.hd
        in
        convert_node tl (found :: acc)
  in
  let ctx = convert_node context [] |> List.rev in
  {
    D.Diff.parent =
      List.map (fun x -> D.CilElement.EStmt (translate_node x stmts)) ctx;
    depth = 0;
  }

let translate_const const =
  match const with
  | S.SElement.SIntConst i -> Cil.CInt64 (Int64.of_int i, Cil.IInt, None)
  | S.SElement.SFloatConst f -> Cil.CReal (f, Cil.FDouble, None)
  | S.SElement.SCharConst c -> Cil.CChr c
  | S.SElement.SStringConst s -> Cil.CStr s

let rec translate_exp comp_map exp_map exp =
  match exp with
  | S.SElement.SConst (i, id) ->
      if H.StrMap.exists (fun k _ -> k = id) comp_map then
        let conv_id = H.StrMap.find id comp_map in
        failwith "translate_exp: not implemented"
        (* S.SElement.SConst (H.StrMap.find conv_id exp_map, conv_id) |> translate_const *)
      else translate_const i
  | _ -> failwith "translate_exp: not implemented"

let rec translate_stmt comp_map cfg exp_map stmt =
  match stmt with
  | S.SElement.SIf (cond, then_block, else_block, id) ->
      let cond = translate_exp comp_map exp_map cond in
      let then_block =
        List.map (fun x -> translate_stmt comp_map cfg exp_map x) then_block
      in
      let else_block =
        List.map (fun x -> translate_stmt comp_map cfg exp_map x) else_block
      in
      S.SElement.SIf (cond, then_block, else_block, id)
  | _ -> failwith "translate_stmt: not implemented"

let translate sparrow_path donee edit_function oc_model =
  let sparrow_dir = Filename.concat sparrow_path "sparrow-out" in
  let cfg, exp_map = H.parse_sparrow sparrow_dir in
  let patch_between = oc_model |> J.member "patch_between" in
  let start_str =
    patch_between |> J.member "start" |> J.member "after" |> J.to_string
  in
  let start =
    H.CfgMap.fold
      (fun k v acc -> if v = start_str then k :: acc else acc)
      cfg []
    |> List.hd
  in
  let end_str =
    patch_between |> J.member "end" |> J.member "after" |> J.to_string
  in
  let end_ =
    H.CfgMap.fold (fun k v acc -> if v = end_str then k :: acc else acc) cfg []
    |> List.hd
  in
  let comp_map =
    oc_model |> J.member "comp" |> J.to_list
    |> List.fold_left
         (fun acc x ->
           let b = x |> J.member "before" |> J.to_string in
           let a = x |> J.member "after" |> J.to_string in
           H.StrMap.add b a acc)
         H.StrMap.empty
  in
  let donee_stmts = H.extract_stmts donee in
  let patch_between =
    (translate_node start donee_stmts, translate_node end_ donee_stmts)
  in
  let translated_ef =
    List.fold_left
      (fun acc d ->
        match d with
        | S.SDiff.SInsertStmt (context, stmt) ->
            let context =
              translate_context comp_map cfg donee_stmts context.parent
            in
            let stmt = translate_stmt comp_map cfg exp_map stmt in
            D.Diff.InsertStmt (context, stmt) :: acc
        | _ -> failwith "translate: not implemented")
      [] edit_function
  in
  (patch_between, translated_ef)
