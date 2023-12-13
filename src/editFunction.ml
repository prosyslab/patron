module J = Yojson.Basic.Util
module D = Diff
module S = SymDiff
module H = Utils

type ast_node = Fun of Cil.global | Stmt of Cil.stmt | Exp of Cil.exp

type t =
  | InsertStmt of ast_node * Cil.stmt
  | DeleteStmt of Cil.stmt
  | InsertExp of ast_node * Cil.exp
  | DeleteExp of Cil.exp
  (* TODO *)
  | UpdateExp of D.CilElement.t * D.CilElement.t * D.CilElement.t
  | InsertLval of D.CilElement.t * D.CilElement.t
  | DeleteLval of D.CilElement.t

let of_exp node =
  match node with Exp e -> e | _ -> failwith "extract_cil: not exp"

let swap_exp = ref []

class expVisitor target =
  object
    inherit Cil.nopCilVisitor

    method! vstmt (s : Cil.stmt) =
      let is_found =
        match s.Cil.skind with
        | Cil.Instr i -> (
            if List.length i = 0 then false
            else
              let i = List.hd i in
              match i with
              | Cil.Call (Some lval, f, args, _) ->
                  let l_str = Utils.SparrowParser.s_lv lval in
                  if String.equal l_str target then (
                    swap_exp := Cil.Lval lval :: !swap_exp;
                    true)
                  else
                    let f_str = Utils.SparrowParser.s_exp f in
                    if String.equal f_str target then (
                      swap_exp := f :: !swap_exp;
                      true)
                    else
                      let args_str = List.map Utils.SparrowParser.s_exp args in
                      if
                        List.exists
                          (fun arg -> String.equal arg target)
                          args_str
                      then (
                        ( List.find (fun arg -> String.equal arg target) args_str
                        |> fun x ->
                          List.find
                            (fun arg ->
                              Utils.SparrowParser.s_exp arg |> String.equal x)
                            args )
                        |> fun x ->
                        swap_exp := x :: !swap_exp;
                        true)
                      else false
              | Cil.Call (None, f, args, _) ->
                  let f_str = Utils.SparrowParser.s_exp f in
                  if String.equal f_str target then (
                    swap_exp := f :: !swap_exp;
                    true)
                  else
                    let args_str = List.map Utils.SparrowParser.s_exp args in
                    if List.exists (fun arg -> String.equal arg target) args_str
                    then (
                      ( List.find (fun arg -> String.equal arg target) args_str
                      |> fun x ->
                        List.find
                          (fun arg ->
                            Utils.SparrowParser.s_exp arg |> String.equal x)
                          args )
                      |> fun x ->
                      swap_exp := x :: !swap_exp;
                      true)
                    else false
              | Cil.Set (lval, exp, _) -> (
                  let l_str = Utils.SparrowParser.s_lv lval in
                  if String.equal l_str target then (
                    swap_exp := Cil.Lval lval :: !swap_exp;
                    true)
                  else
                    let exp_str = Utils.SparrowParser.s_exp exp in
                    if String.equal exp_str target then true
                    else
                      match exp with
                      | Cil.CastE (_, e) ->
                          let e_str = Utils.SparrowParser.s_exp e in
                          if String.equal e_str target then (
                            swap_exp := e :: !swap_exp;
                            true)
                          else false
                      | _ -> false)
              | _ -> false)
        | Cil.Return (Some exp, _) ->
            let exp_str = Utils.SparrowParser.s_exp exp in
            String.equal exp_str target
        | _ -> false
      in
      if is_found then SkipChildren else DoChildren
  end

let rec translate_lval ast model_map exp_map slval =
  let id = slval.S.SElement.id in
  let lval = slval.S.SElement.node in
  match lval with
  | S.SElement.SLval (sym, cil) ->
      if List.exists (fun (k, _) -> String.equal id k) model_map then
        let new_id =
          List.find (fun (k, _) -> String.equal id k) model_map |> snd
        in
        let new_exp_str = Hashtbl.find exp_map new_id in
        match (sym, cil) with
        | S.SElement.SLNull, _ -> failwith "translate_lval:Lval is null"
        | S.SElement.Lval (S.SElement.SVar _, _), (Cil.Var _, _) -> (
            let vis = new expVisitor new_exp_str in
            ignore (Cil.visitCilFile vis ast);
            match List.hd !swap_exp with Cil.Lval lval -> lval | _ -> cil)
        | S.SElement.Lval (S.SElement.SMem _, _), (Cil.Mem _, _) -> (
            let vis = new expVisitor new_exp_str in
            ignore (Cil.visitCilFile vis ast);
            match List.hd !swap_exp with Cil.Lval lval -> lval | _ -> cil)
        | _ -> failwith "translate_lval: not implemented"
      else cil
  | _ -> failwith "translate_lval: translation target is not an lvalue"

and translate_exp ast (model_map : (string * string) list) exp_map sexp =
  let id = sexp.S.SElement.id in
  let exp = sexp.S.SElement.node in
  match exp with
  | S.SElement.SExp (sym, cil) -> (
      match (sym, cil) with
      | S.SElement.SConst c, Cil.Const _ ->
          if List.exists (fun (k, _) -> String.equal id k) model_map then
            let new_id =
              List.find (fun (k, _) -> String.equal id k) model_map |> snd
            in
            let new_exp_str = Hashtbl.find exp_map new_id in
            match c with
            | S.SElement.SIntConst i ->
                Cil.Const
                  (Cil.CInt64 (Int64.of_string new_exp_str, Cil.IInt, None))
            | S.SElement.SFloatConst f ->
                Cil.Const
                  (Cil.CReal (float_of_string new_exp_str, Cil.FDouble, None))
            | S.SElement.SCharConst c ->
                Cil.Const (Cil.CChr (String.get new_exp_str 0))
            | S.SElement.SStringConst s -> Cil.Const (Cil.CStr new_exp_str)
          else (* TODO: casting within constant*)
            cil
      | S.SElement.SELval l, Cil.Lval _ ->
          let lval = translate_lval ast model_map exp_map l in
          Cil.Lval lval
      | S.SElement.SBinOp (_, l, r, _), Cil.BinOp (op', _, _, t') ->
          let lval = translate_exp ast model_map exp_map l in
          let rval = translate_exp ast model_map exp_map r in
          Cil.BinOp (op', lval, rval, t')
      | S.SElement.SCastE (_, e), Cil.CastE (t, _) ->
          let exp = translate_exp ast model_map exp_map e in
          Cil.CastE (t, exp)
      | S.SElement.SUnOp _, Cil.UnOp _
      | S.SElement.SSizeOf _, Cil.SizeOf _
      | S.SElement.SSizeOfE _, Cil.SizeOfE _
      | S.SElement.SSizeOfStr _, Cil.SizeOfStr _
      | _ ->
          Utils.print_ekind cil;
          failwith "translate_exp: not implemented")
  | _ -> failwith "translate_exp: ranslation target is not an expression"

let rec translate_stmt ast model_map cfg exp_map stmt =
  let id = stmt.S.SElement.id in
  let node = stmt.S.SElement.node in
  match node with
  | S.SElement.SStmt (sym, cil) -> (
      match (sym, cil.Cil.skind) with
      | S.SElement.SIf (scond, sthen_block, selse_block), Cil.If _ ->
          let cond = translate_exp ast model_map exp_map scond in
          let then_block =
            List.fold_left
              (fun acc ss -> translate_stmt ast model_map cfg exp_map ss :: acc)
              [] sthen_block
            |> List.rev
          in
          let else_block =
            List.fold_left
              (fun acc ss -> translate_stmt ast model_map cfg exp_map ss :: acc)
              [] selse_block
            |> List.rev
          in
          Cil.mkStmt
            (Cil.If
               ( cond,
                 Cil.mkBlock then_block,
                 Cil.mkBlock else_block,
                 Cil.locUnknown ))
      | S.SElement.SReturn (Some sym), Cil.Return _ ->
          let exp = translate_exp ast model_map exp_map sym in
          Cil.mkStmt (Cil.Return (Some exp, Cil.locUnknown))
      | S.SElement.SReturn None, Cil.Return _ ->
          Cil.mkStmt (Cil.Return (None, Cil.locUnknown))
      | S.SElement.SGoto _, Cil.Goto _ -> cil
      | a, Cil.Instr i -> (
          match (a, List.hd i) with
          | S.SElement.SSet (l, r), Cil.Set _ ->
              let lval = translate_lval ast model_map exp_map l in
              let rval = translate_exp ast model_map exp_map r in
              Cil.mkStmt (Cil.Instr [ Cil.Set (lval, rval, Cil.locUnknown) ])
          | S.SElement.SCall (Some l, f, args), Cil.Call _ ->
              let lval = translate_lval ast model_map exp_map l in
              let fun_exp = translate_exp ast model_map exp_map f in
              let args =
                List.fold_left
                  (fun acc arg ->
                    translate_exp ast model_map exp_map arg :: acc)
                  [] args
                |> List.rev
              in
              Cil.mkStmt
                (Cil.Instr
                   [ Cil.Call (Some lval, fun_exp, args, Cil.locUnknown) ])
          | S.SElement.SCall (None, f, args), Cil.Call _ ->
              let fun_exp = translate_exp ast model_map exp_map f in
              let args =
                List.fold_left
                  (fun acc arg ->
                    translate_exp ast model_map exp_map arg :: acc)
                  [] args
                |> List.rev
              in
              Cil.mkStmt
                (Cil.Instr [ Cil.Call (None, fun_exp, args, Cil.locUnknown) ])
          | _ ->
              failwith
                "translate_stmt: translation target is not an instruction type")
      | _ -> failwith "translate_stmt: not implemented")
  | _ -> failwith "translate_stmt: translation target is not a statement type"

let translate ast sym_diff model_path maps patch_node_id =
  Logger.info "Translating patch...";
  let cfg = maps.Maps.cfg_map in
  let exp_map = maps.Maps.exp_map in
  let model_map = H.parse_model model_path in
  let ast_map = maps.Maps.ast_map in
  let translated =
    List.fold_left
      (fun acc diff ->
        match diff with
        | S.SDiff.SInsertStmt (context, stmt) ->
            (* let patch_node = context.S.SDiff.patch_node in *)
            let new_patch_id =
              List.find
                (fun (k, _) ->
                  String.equal k
                    (String.concat "-" [ "AstNode"; patch_node_id ]))
                model_map
              |> snd
            in
            let new_parent_node =
              (* match new_patch_id with
                 | None -> (
                     match patch_node.node with
                     | S.SElement.SStmt (_, s) -> Stmt s
                     | S.SElement.SGlob (_, g) -> Fun g
                     | _ -> failwith "translate: not implemented")
                 | Some id -> *)
              (* TODO: case where parent is global *)
              let translated_stmt =
                (* Parser.ASTMap.M.fold
                     (fun k v acc -> if v = id then k :: acc else acc)
                     ast_map []
                   |> List.hd *)
                Hashtbl.fold
                  (fun k v acc ->
                    if "AstNode-" ^ string_of_int v |> String.equal new_patch_id
                    then k :: acc
                    else acc)
                  ast_map []
                |> List.hd
              in
              Stmt translated_stmt
            in
            InsertStmt
              (new_parent_node, translate_stmt ast model_map cfg exp_map stmt)
            :: acc
        | S.SDiff.SDeleteStmt (_, stmt) ->
            let stmt = translate_stmt ast model_map cfg exp_map stmt in
            DeleteStmt stmt :: acc
        | _ -> failwith "translate: not implemented")
      [] sym_diff
  in
  translated
