module J = Yojson.Basic.Util
module D = Diff
module S = SymDiff
module H = Utils

let translate_by_model id model =
  List.find_opt (fun (k, _) -> String.equal k id) model |> function
  | x -> ( match x with Some (_, v) -> Some v | None -> None)

let translate_node_lst lst model =
  List.fold_left
    (fun acc x ->
      match translate_by_model x model with Some x -> x :: acc | None -> acc)
    [] lst

let of_exp node =
  match node with Ast.Exp e -> e | _ -> failwith "extract_cil: not exp"

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
                  let l_str = Ast.s_lv lval in
                  if String.equal l_str target then (
                    swap_exp := Cil.Lval lval :: !swap_exp;
                    true)
                  else
                    let f_str = Ast.s_exp f in
                    if String.equal f_str target then (
                      swap_exp := f :: !swap_exp;
                      true)
                    else
                      let args_str = List.map Ast.s_exp args in
                      if
                        List.exists
                          (fun arg -> String.equal arg target)
                          args_str
                      then (
                        ( List.find (fun arg -> String.equal arg target) args_str
                        |> fun x ->
                          List.find
                            (fun arg -> Ast.s_exp arg |> String.equal x)
                            args )
                        |> fun x ->
                        swap_exp := x :: !swap_exp;
                        true)
                      else false
              | Cil.Call (None, f, args, _) ->
                  let f_str = Ast.s_exp f in
                  if String.equal f_str target then (
                    swap_exp := f :: !swap_exp;
                    true)
                  else
                    let args_str = List.map Ast.s_exp args in
                    if List.exists (fun arg -> String.equal arg target) args_str
                    then (
                      ( List.find (fun arg -> String.equal arg target) args_str
                      |> fun x ->
                        List.find
                          (fun arg -> Ast.s_exp arg |> String.equal x)
                          args )
                      |> fun x ->
                      swap_exp := x :: !swap_exp;
                      true)
                    else false
              | Cil.Set (lval, exp, _) -> (
                  let l_str = Ast.s_lv lval in
                  if String.equal l_str target then (
                    swap_exp := Cil.Lval lval :: !swap_exp;
                    true)
                  else
                    let exp_str = Ast.s_exp exp in
                    if String.equal exp_str target then true
                    else
                      match exp with
                      | Cil.CastE (_, e) ->
                          let e_str = Ast.s_exp e in
                          if String.equal e_str target then (
                            swap_exp := e :: !swap_exp;
                            true)
                          else false
                      | _ -> false)
              | _ -> false)
        | Cil.Return (Some exp, _) ->
            let exp_str = Ast.s_exp exp in
            String.equal exp_str target
        | _ -> false
      in
      if is_found then SkipChildren else DoChildren
  end

let rec translate_lval ast model_map exp_map slval =
  let id = slval.S.SymAst.id in
  let lval = slval.S.SymAst.node in
  match lval with
  | S.SymAst.SLval (sym, cil) ->
      if List.exists (fun (k, _) -> String.equal id k) model_map then
        let new_id =
          List.find (fun (k, _) -> String.equal id k) model_map |> snd
        in
        let new_exp_str = Hashtbl.find exp_map new_id in
        match (sym, cil) with
        | S.SymAst.SLNull, _ -> failwith "translate_lval:Lval is null"
        | S.SymAst.Lval (S.SymAst.SVar _, _), (Cil.Var _, _) -> (
            let vis = new expVisitor new_exp_str in
            ignore (Cil.visitCilFile vis ast);
            match List.hd !swap_exp with Cil.Lval lval -> lval | _ -> cil)
        | S.SymAst.Lval (S.SymAst.SMem _, _), (Cil.Mem _, _) -> (
            let vis = new expVisitor new_exp_str in
            ignore (Cil.visitCilFile vis ast);
            match List.hd !swap_exp with Cil.Lval lval -> lval | _ -> cil)
        | _ -> failwith "translate_lval: not implemented"
      else cil
  | _ -> failwith "translate_lval: translation target is not an lvalue"

and translate_exp ast (model_map : (string * string) list) exp_map sexp =
  let id = sexp.S.SymAst.id in
  let exp = sexp.S.SymAst.node in
  match exp with
  | S.SymAst.SExp (sym, cil) -> (
      match (sym, cil) with
      | S.SymAst.SConst c, Cil.Const _ ->
          if List.exists (fun (k, _) -> String.equal id k) model_map then
            let new_id =
              List.find (fun (k, _) -> String.equal id k) model_map |> snd
            in
            let new_exp_str = Hashtbl.find exp_map new_id in
            match c with
            | S.SymAst.SIntConst _ ->
                Cil.Const
                  (Cil.CInt64 (Int64.of_string new_exp_str, Cil.IInt, None))
            | S.SymAst.SFloatConst _ ->
                Cil.Const
                  (Cil.CReal (float_of_string new_exp_str, Cil.FDouble, None))
            | S.SymAst.SCharConst _ ->
                Cil.Const (Cil.CChr (String.get new_exp_str 0))
            | S.SymAst.SStringConst _ -> Cil.Const (Cil.CStr new_exp_str)
          else (* TODO: casting within constant*)
            cil
      | S.SymAst.SELval l, Cil.Lval _ ->
          let lval = translate_lval ast model_map exp_map l in
          Cil.Lval lval
      | S.SymAst.SBinOp (_, l, r, _), Cil.BinOp (op', _, _, t') ->
          let lval = translate_exp ast model_map exp_map l in
          let rval = translate_exp ast model_map exp_map r in
          Cil.BinOp (op', lval, rval, t')
      | S.SymAst.SCastE (_, e), Cil.CastE (t, _) ->
          let exp = translate_exp ast model_map exp_map e in
          Cil.CastE (t, exp)
      | S.SymAst.SUnOp (_, t, _), Cil.UnOp (op', _, t') ->
          let exp = translate_exp ast model_map exp_map t in
          Cil.UnOp (op', exp, t')
      | S.SymAst.SSizeOf _, Cil.SizeOf _
      | S.SymAst.SSizeOfE _, Cil.SizeOfE _
      | S.SymAst.SSizeOfStr _, Cil.SizeOfStr _
      | _ ->
          Utils.print_ekind cil;
          failwith "translate_exp: not implemented")
  | _ -> failwith "translate_exp: ranslation target is not an expression"

let rec translate_stmt ast model_map cfg exp_map stmt =
  let node = stmt.S.SymAst.node in
  match node with
  | S.SymAst.SStmt (sym, cil) -> (
      match (sym, cil.Cil.skind) with
      | S.SymAst.SIf (scond, sthen_block, selse_block), Cil.If _ ->
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
      | S.SymAst.SReturn (Some sym), Cil.Return _ ->
          let exp = translate_exp ast model_map exp_map sym in
          Cil.mkStmt (Cil.Return (Some exp, Cil.locUnknown))
      | S.SymAst.SReturn None, Cil.Return _ ->
          Cil.mkStmt (Cil.Return (None, Cil.locUnknown))
      | S.SymAst.SGoto _, Cil.Goto _ -> cil
      | a, Cil.Instr i -> (
          match (a, List.hd i) with
          | S.SymAst.SSet (l, r), Cil.Set _ ->
              let lval = translate_lval ast model_map exp_map l in
              let rval = translate_exp ast model_map exp_map r in
              Cil.mkStmt (Cil.Instr [ Cil.Set (lval, rval, Cil.locUnknown) ])
          | S.SymAst.SCall (Some l, f, args), Cil.Call _ ->
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
          | S.SymAst.SCall (None, f, args), Cil.Call _ ->
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

let get_new_patch_id id model =
  (* print_endline id;
     if List.exists (fun (k, _) -> String.equal k id) model then *)
  List.find
    (fun (k, _) -> String.equal k (String.concat "-" [ "AstNode"; id ]))
    model
  |> snd
  |> Str.global_replace (Str.regexp "AstNode-") ""
  |> int_of_string
(* else
   failwith "get_new_patch_id: patch location is not included in the pattern" *)

let compute_patch_loc (before, after) patch_ingredients node_map ast_map_rev =
  let cfg2ast_stmt node_lst =
    if node_lst = [] then []
    else
      List.fold_left
        (fun acc s ->
          try List.find (fun x -> String.equal s x) patch_ingredients :: acc
          with _ -> acc)
        [] node_lst
      |> fun x ->
      if x = [] then []
      else
        List.fold_left
          (fun acc x ->
            Hashtbl.find node_map x |> fun x ->
            let x_int = int_of_string x in
            (Hashtbl.find ast_map_rev x_int |> Ast.ast2stmt) :: acc)
          [] x
        |> Ast.stmts2path
  in
  (cfg2ast_stmt before, cfg2ast_stmt after)

let find_patch_fun diff model =
  let get_func str = String.split_on_char '-' str |> List.hd in
  let untranslated_func_name =
    match diff with
    | S.SInsertStmt (ctx, _)
    | S.SDeleteStmt (ctx, _)
    | S.SUpdateExp (ctx, _, _)
    | S.SInsertExp (ctx, _)
    | S.SDeleteExp (ctx, _)
    | S.SInsertLval (ctx, _)
    | S.SDeleteLval (ctx, _)
    | S.SUpdateLval (ctx, _, _) ->
        ctx.func_name
  in
  List.find
    (fun (k, _) -> get_func k |> String.equal untranslated_func_name)
    model
  |> snd |> get_func

let translate ast sym_diff model_path maps patch_node_ids patch_ingredients =
  Logger.info "Translating patch...";
  let cfg = maps.Maps.cfg_map in
  let exp_map = maps.Maps.exp_map in
  let model_map = H.parse_model model_path in
  let ast_map = maps.Maps.ast_map in
  let ast_map_rev = Utils.reverse_hashtbl ast_map in
  let node_map = maps.Maps.node_map in
  (* ToDO: make the order of hashtbl proper so that it will optimize *)
  let translated_ingredients = translate_node_lst patch_ingredients model_map in
  List.fold_left2
    (fun acc diff parent_id ->
      match diff with
      | S.SInsertStmt (ctx, stmt) ->
          let new_patch_id =
            if String.equal parent_id "" then -1
            else get_new_patch_id parent_id model_map
          in
          let new_parent_node =
            if new_patch_id = -1 then
              let translated_func_name = find_patch_fun diff model_map in
              Ast.Fun translated_func_name
            else
              let translated_stmt = Hashtbl.find ast_map_rev new_patch_id in
              translated_stmt
          in
          let before, after =
            compute_patch_loc ctx.S.patch_between translated_ingredients
              node_map ast_map_rev
          in
          let ctx =
            D.mk_context [ new_parent_node ] before after ctx.S.sibling_idx
          in
          D.InsertStmt (ctx, translate_stmt ast model_map cfg exp_map stmt)
          :: acc
      | S.SDeleteStmt (ctx, stmt) ->
          let ctx =
            D.mk_context [ Ast.NotApplicable ] [] [] ctx.S.sibling_idx
          in
          let translated_stmt = translate_stmt ast model_map cfg exp_map stmt in
          D.DeleteStmt (ctx, translated_stmt) :: acc
      | S.SUpdateExp (ctx, e1, e2) ->
          let new_patch_id = get_new_patch_id parent_id model_map in
          let new_parent_node =
            let translated_stmt = Hashtbl.find ast_map_rev new_patch_id in
            translated_stmt
          in
          let ctx = D.mk_context [ new_parent_node ] [] [] ctx.S.sibling_idx in
          let translated_e1 = translate_exp ast model_map exp_map e1 in
          let translated_e2 = translate_exp ast model_map exp_map e2 in
          D.UpdateExp (ctx, translated_e1, translated_e2) :: acc
      | _ -> failwith "translate: not implemented")
    [] sym_diff patch_node_ids
