module J = Yojson.Basic.Util
module D = Diff
module A = AbsDiff
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

let swap_lval = ref []
let swap_exp = ref []
let swap_stmt = ref []

class lvTranslationVisitor target =
  object (lvalVisitor)
    inherit Cil.nopCilVisitor

    method search_offset target offset =
      match offset with
      | Cil.Field (_, o) -> lvalVisitor#search_offset target o
      | Cil.Index (e, o) ->
          lvalVisitor#search_exp target e || lvalVisitor#search_offset target o
      | Cil.NoOffset -> false

    method search_lval target lval =
      let lv_str = Ast.s_lv lval in
      if String.equal lv_str target then (
        swap_lval := lval :: !swap_lval;
        true)
      else
        let lhost, offset = lval in
        let is_matched =
          match lhost with
          | Cil.Mem e -> lvalVisitor#search_exp target e
          | Cil.Var _ -> false
        in
        if is_matched |> not then lvalVisitor#search_offset target offset
        else is_matched

    method search_exp target exp =
      match exp with
      | Cil.CastE (_, e) -> lvalVisitor#search_exp target e
      | Cil.BinOp (_, e1, e2, _) ->
          lvalVisitor#search_exp target e1 || lvalVisitor#search_exp target e2
      | Cil.UnOp (_, e, _) -> lvalVisitor#search_exp target e
      | Cil.AddrOf l | Cil.StartOf l -> lvalVisitor#search_lval target l
      | Cil.Lval l -> lvalVisitor#search_lval target l
      | Cil.SizeOfE e -> lvalVisitor#search_exp target e
      | _ -> false

    method search_call target lv_opt args =
      match lv_opt with
      | Some lval ->
          lvalVisitor#search_lval target lval
          || List.map (lvalVisitor#search_exp target) args
             |> List.exists (fun x -> x)
      | None ->
          List.map (lvalVisitor#search_exp target) args
          |> List.exists (fun x -> x)

    method search_set target lval exp =
      lvalVisitor#search_lval target lval || lvalVisitor#search_exp target exp

    method search_instr target instrs =
      if List.length instrs = 0 then false
      else
        let i = List.hd instrs in
        match i with
        | Cil.Call (lv_opt, _, args, _) ->
            lvalVisitor#search_call target lv_opt args
        | Cil.Set (lval, exp, _) -> lvalVisitor#search_set target lval exp
        | _ -> false

    method! vstmt (s : Cil.stmt) =
      let is_found =
        match s.Cil.skind with
        | Cil.Instr i -> lvalVisitor#search_instr target i
        | Cil.Return (Some exp, _) -> lvalVisitor#search_exp target exp
        | Cil.If (exp, _, _, _) -> lvalVisitor#search_exp target exp
        | _ -> false
      in
      if is_found then SkipChildren else DoChildren
  end

class expTranslationVisitor target =
  object (expVisitor)
    inherit Cil.nopCilVisitor

    method search_offset target offset =
      match offset with
      | Cil.Field (_, o) -> expVisitor#search_offset target o
      | Cil.Index (e, o) ->
          expVisitor#search_exp target e || expVisitor#search_offset target o
      | Cil.NoOffset -> false

    method search_lval target lval =
      let lhost, offset = lval in
      let is_matched =
        match lhost with
        | Cil.Mem e -> expVisitor#search_exp target e
        | Cil.Var _ -> false
      in
      if is_matched |> not then expVisitor#search_offset target offset
      else is_matched

    method search_exp target exp =
      let exp_str = Ast.s_exp exp in
      if String.equal exp_str target then (
        swap_exp := exp :: !swap_exp;
        true)
      else
        match exp with
        | Cil.CastE (_, e) -> expVisitor#search_exp target e
        | Cil.BinOp (_, e1, e2, _) ->
            expVisitor#search_exp target e1 || expVisitor#search_exp target e2
        | Cil.UnOp (_, e, _) -> expVisitor#search_exp target e
        | Cil.AddrOf l | Cil.StartOf l -> expVisitor#search_lval target l
        | Cil.Lval l -> expVisitor#search_lval target l
        | Cil.SizeOfE e -> expVisitor#search_exp target e
        | _ -> false

    method search_call target lv_opt args =
      match lv_opt with
      | Some lval ->
          expVisitor#search_lval target lval
          || List.map (expVisitor#search_exp target) args
             |> List.exists (fun x -> x)
      | None ->
          List.map (expVisitor#search_exp target) args
          |> List.exists (fun x -> x)

    method search_set target lval exp =
      expVisitor#search_lval target lval || expVisitor#search_exp target exp

    method search_instr target instrs =
      if List.length instrs = 0 then false
      else
        let i = List.hd instrs in
        match i with
        | Cil.Call (lv_opt, _, args, _) ->
            expVisitor#search_call target lv_opt args
        | Cil.Set (lval, exp, _) -> expVisitor#search_set target lval exp
        | _ -> false

    method! vstmt (s : Cil.stmt) =
      let is_found =
        match s.Cil.skind with
        | Cil.Instr i -> expVisitor#search_instr target i
        | Cil.Return (Some exp, _) -> expVisitor#search_exp target exp
        | Cil.If (exp, _, _, _) -> expVisitor#search_exp target exp
        | _ -> false
      in
      if is_found then SkipChildren else DoChildren
  end

let rec translate_exp ast model_map (lookup_maps : Maps.translation_lookup_maps)
    sexp =
  let id = sexp.A.AbsAst.id in
  if List.exists (fun (k, _) -> String.equal id k) model_map then (
    let new_id = List.find (fun (k, _) -> String.equal id k) model_map |> snd in
    let new_exp_str = Hashtbl.find lookup_maps.Maps.lval_map new_id in
    swap_exp := [];
    let vis = new expTranslationVisitor new_exp_str in
    ignore (Cil.visitCilFile (vis :> Cil.cilVisitor) ast);
    List.hd !swap_exp)
  else break_down_translate_exp ast model_map lookup_maps sexp.A.AbsAst.node

and translate_offset ast model_map lookup_maps abs_offset offset =
  match (abs_offset, offset) with
  | A.AbsAst.SNoOffset, Cil.NoOffset -> offset
  | A.AbsAst.SField (_, o), Cil.Field (f, o') ->
      Cil.Field (f, translate_offset ast model_map lookup_maps o o')
  | A.AbsAst.SIndex (e, o), Cil.Index (_, o') ->
      let new_e = translate_exp ast model_map lookup_maps e in
      let new_o = translate_offset ast model_map lookup_maps o o' in
      Cil.Index (new_e, new_o)
  | _ -> failwith "translate_offset: concrete and abstract offset not matched"

and translate_lhost ast model_map lookup_maps abs_lhost lhost =
  match (abs_lhost, lhost) with
  | A.AbsAst.SMem e, Cil.Mem _ ->
      Cil.Mem (translate_exp ast model_map lookup_maps e)
  | A.AbsAst.SVar _, Cil.Var _ -> lhost
  | _ -> failwith "translate_lhost: concrete and abstract lhost not matched"

and break_down_translate_lval ast model_map lookup_maps lval =
  match lval with
  | A.AbsAst.AbsLval (sym, cil) -> (
      match (sym, cil) with
      | A.AbsAst.SLNull, _ -> failwith "translate_lval:Lval is null"
      | A.AbsAst.Lval (abs_lhost, abs_offset), (lhost, offset) ->
          ( translate_lhost ast model_map lookup_maps abs_lhost lhost,
            translate_offset ast model_map lookup_maps abs_offset offset ))
  | _ -> failwith "translate_lval: translation target is not an lvalue"

and translate_lval ast model_map (lookup_maps : Maps.translation_lookup_maps)
    slval =
  let id = slval.A.AbsAst.id in
  if List.exists (fun (k, _) -> String.equal id k) model_map then (
    let new_id = List.find (fun (k, _) -> String.equal id k) model_map |> snd in
    let new_lv_str = Hashtbl.find lookup_maps.lval_map new_id in
    swap_lval := [];
    let vis = new lvTranslationVisitor new_lv_str in
    ignore (Cil.visitCilFile (vis :> Cil.cilVisitor) ast);
    List.hd !swap_lval)
  else break_down_translate_lval ast model_map lookup_maps slval.A.AbsAst.node

and break_down_translate_exp ast model_map
    (lookup_maps : Maps.translation_lookup_maps) exp =
  match exp with
  | A.AbsAst.AbsExp (sym, cil) -> (
      match (sym, cil) with
      | A.AbsAst.SConst _, Cil.Const _ -> cil
      | A.AbsAst.SELval l, Cil.Lval _ ->
          let lval = translate_lval ast model_map lookup_maps l in
          Cil.Lval lval
      | A.AbsAst.SBinOp (_, l, r, _), Cil.BinOp (op', _, _, t') ->
          let lval = translate_exp ast model_map lookup_maps l in
          let rval = translate_exp ast model_map lookup_maps r in
          Cil.BinOp (op', lval, rval, t')
      | A.AbsAst.SCastE (_, e), Cil.CastE (t, _) ->
          let exp = translate_exp ast model_map lookup_maps e in
          Cil.CastE (t, exp)
      | A.AbsAst.SUnOp (_, t, _), Cil.UnOp (op', _, t') ->
          let exp = translate_exp ast model_map lookup_maps t in
          Cil.UnOp (op', exp, t')
      | A.AbsAst.SSizeOfE e, Cil.SizeOfE _ ->
          let exp = translate_exp ast model_map lookup_maps e in
          Cil.SizeOfE exp
      | A.AbsAst.SAddrOf l, Cil.AddrOf _ ->
          let lval = translate_lval ast model_map lookup_maps l in
          Cil.AddrOf lval
      | A.AbsAst.SStartOf l, Cil.StartOf _ ->
          let lval = translate_lval ast model_map lookup_maps l in
          Cil.StartOf lval
      | A.AbsAst.SQuestion (a, b, c, _), Cil.Question (_, _, _, t) ->
          let cond = translate_exp ast model_map lookup_maps a in
          let b_exp = translate_exp ast model_map lookup_maps b in
          let c_exp = translate_exp ast model_map lookup_maps c in
          Cil.Question (cond, b_exp, c_exp, t)
      | A.AbsAst.SSizeOf _, Cil.SizeOf _
      | A.AbsAst.SSizeOfStr _, Cil.SizeOfStr _
      | _ ->
          Utils.print_ekind cil;
          failwith "translate_exp: not implemented")
  | _ -> failwith "translate_exp: translation target is not an expression"

class stmtVisitor (target : Cil.stmt) =
  object
    inherit Cil.nopCilVisitor

    method! vstmt (s : Cil.stmt) =
      let is_found = String.equal (Ast.s_stmt s) (Ast.s_stmt target) in
      if is_found then (
        swap_stmt := s :: !swap_stmt;
        SkipChildren)
      else DoChildren
  end

let rec translate_stmt ast model_map node_map ast_map lookup_maps stmt =
  let id = stmt.A.AbsAst.id in
  if List.exists (fun (k, _) -> String.equal id k) model_map then (
    let new_id = List.find (fun (k, _) -> String.equal id k) model_map |> snd in
    let new_ast_node =
      Hashtbl.find node_map new_id
      |> int_of_string |> Hashtbl.find ast_map |> Ast.ast2stmt
    in
    swap_stmt := [];
    let vis = new stmtVisitor new_ast_node in
    ignore (Cil.visitCilFile vis ast);
    List.hd !swap_stmt)
  else
    break_down_translate_stmt stmt.A.AbsAst.node ast model_map node_map ast_map
      lookup_maps

and break_down_translate_stmt node ast model_map node_map ast_map lookup_maps =
  match node with
  | A.AbsAst.AbsStmt (sym, cil) -> (
      match (sym, cil.Cil.skind) with
      | A.AbsAst.SIf (scond, sthen_block, selse_block), Cil.If _ ->
          translate_if_stmt ast model_map node_map ast_map lookup_maps scond
            sthen_block selse_block
      | A.AbsAst.SReturn (Some sym), Cil.Return _ ->
          let exp = translate_exp ast model_map lookup_maps sym in
          Cil.mkStmt (Cil.Return (Some exp, Cil.locUnknown))
      | A.AbsAst.SReturn None, Cil.Return _ ->
          Cil.mkStmt (Cil.Return (None, Cil.locUnknown))
      | A.AbsAst.SGoto _, Cil.Goto _ -> cil
      | abs_instr, Cil.Instr i ->
          translate_instr ast model_map lookup_maps abs_instr i
      | _ -> failwith "translate_stmt: not implemented")
  | _ -> failwith "translate_stmt: translation target is not a statement type"

and translate_if_stmt ast model_map node_map ast_map lookup_maps scond
    sthen_block selse_block =
  let cond = translate_exp ast model_map lookup_maps scond in
  let then_block =
    List.fold_left
      (fun acc ss ->
        translate_stmt ast model_map node_map ast_map lookup_maps ss :: acc)
      [] sthen_block
    |> List.rev
  in
  let else_block =
    List.fold_left
      (fun acc ss ->
        translate_stmt ast model_map node_map ast_map lookup_maps ss :: acc)
      [] selse_block
    |> List.rev
  in
  Cil.mkStmt
    (Cil.If
       (cond, Cil.mkBlock then_block, Cil.mkBlock else_block, Cil.locUnknown))

and translate_instr ast model_map (lookup_maps : Maps.translation_lookup_maps)
    abs_instr i =
  match (abs_instr, List.hd i) with
  | A.AbsAst.SSet (l, r), Cil.Set _ ->
      let lval = translate_lval ast model_map lookup_maps l in
      let rval = translate_exp ast model_map lookup_maps r in
      Cil.mkStmt (Cil.Instr [ Cil.Set (lval, rval, Cil.locUnknown) ])
  | A.AbsAst.SCall (Some l, f, args), Cil.Call _ ->
      let lval = translate_lval ast model_map lookup_maps l in
      let fun_exp = translate_exp ast model_map lookup_maps f in
      let args =
        List.fold_left
          (fun acc arg -> translate_exp ast model_map lookup_maps arg :: acc)
          [] args
        |> List.rev
      in
      Cil.mkStmt
        (Cil.Instr [ Cil.Call (Some lval, fun_exp, args, Cil.locUnknown) ])
  | A.AbsAst.SCall (None, f, args), Cil.Call _ ->
      let fun_exp = AbsDiff.get_original_exp f in
      let args =
        List.fold_left
          (fun acc arg -> translate_exp ast model_map lookup_maps arg :: acc)
          [] args
        |> List.rev
      in
      Cil.mkStmt (Cil.Instr [ Cil.Call (None, fun_exp, args, Cil.locUnknown) ])
  | _ ->
      failwith "translate_stmt: translation target is not an instruction type"

let get_new_patch_id id model =
  List.find (fun (k, _) -> String.equal k (Utils.mk_ast_node_str id)) model
  |> snd
  |> Str.global_replace (Str.regexp "AstNode-") ""
  |> int_of_string

let compute_patch_loc (before, after) model_map node_map ast_map_rev =
  let cfg2ast_stmt node_lst =
    if node_lst = [] then []
    else
      translate_node_lst node_lst model_map |> fun x ->
      List.fold_left
        (fun acc x ->
          try
            Hashtbl.find node_map x |> fun x ->
            (int_of_string x |> Hashtbl.find ast_map_rev |> Ast.ast2stmt) :: acc
          with Not_found -> acc)
        [] x
      |> Ast.stmts2path
  in
  (cfg2ast_stmt before, cfg2ast_stmt after)

let find_patch_fun diff model =
  let get_func str = String.split_on_char '-' str |> List.hd in
  let untranslated_func_name =
    match diff with
    | A.SInsertStmt (ctx, _)
    | SDeleteStmt (ctx, _)
    | SUpdateExp (ctx, _, _)
    | SInsertExp (ctx, _)
    | SDeleteExp (ctx, _)
    | SInsertLval (ctx, _)
    | SDeleteLval (ctx, _)
    | SUpdateLval (ctx, _, _) ->
        ctx.func_name
  in
  List.find
    (fun (k, _) -> get_func k |> String.equal untranslated_func_name)
    model
  |> snd |> get_func

let extract_id_from_term term =
  match term with
  | Chc.Elt.FDNumeral id ->
      Str.global_replace (Str.regexp "AstNode-") "" id |> int_of_string
  | _ -> failwith "extract_id_from_term: unexpected type"

let find_func_name_of_stmt stmt_id parent_facts ast_map =
  let facts = Chc.to_list parent_facts in
  let rec aux id =
    List.fold_left
      (fun acc fact ->
        match fact with
        | Chc.Elt.FuncApply ("AstParent", [ parent_term; child_term ]) ->
            if extract_id_from_term child_term = id then
              let parent_id = extract_id_from_term parent_term in
              let parent_node = Hashtbl.find ast_map parent_id in
              if Ast.is_glob parent_node || Ast.is_fun parent_node then
                parent_node :: acc
              else aux parent_id @ acc
            else acc
        | _ -> acc)
      [] facts
  in
  aux stmt_id |> List.hd |> fun g ->
  match g with
  | Ast.Global g -> Ast.glob2func_name g
  | Ast.Fun f -> f
  | _ -> failwith "find_func_name_of_stmt: unexpected type"

let get_parent_of_stmt parent_id model_map ast_map parent_facts =
  let new_patch_id = get_new_patch_id parent_id model_map in
  let translated_stmt = Hashtbl.find ast_map new_patch_id in
  let func_name =
    match translated_stmt with
    | Ast.Global g -> Ast.glob2func_name g
    | Ast.Fun f -> f
    | Ast.Stmt _ -> find_func_name_of_stmt new_patch_id parent_facts ast_map
    | _ -> failwith "get_parent_of_stmt: unexpected type"
  in
  (translated_stmt, func_name)

let translate_insert_stmt ast parent_id ctx stmt model maps ast_map_rev
    parent_facts =
  let lookup_maps =
    { Maps.exp_map = maps.Maps.exp_map; lval_map = maps.Maps.lval_map }
  in
  let new_parent_node, new_func_name =
    get_parent_of_stmt parent_id model ast_map_rev parent_facts
  in
  let before, after =
    compute_patch_loc ctx.A.patch_bound model maps.Maps.node_map ast_map_rev
  in
  let ctx =
    D.mk_context [ new_parent_node ] before after ctx.A.sibling_idx
      new_func_name
  in
  D.InsertStmt
    ( ctx,
      translate_stmt ast model maps.Maps.node_map ast_map_rev lookup_maps stmt
    )

let translate_delete_stmt ast parent_id ctx stmt model_map maps ast_map_rev
    parent_facts =
  let loopup_maps =
    { Maps.exp_map = maps.Maps.exp_map; lval_map = maps.Maps.lval_map }
  in
  let new_parent_node, new_func_name =
    get_parent_of_stmt parent_id model_map ast_map_rev parent_facts
  in
  let ctx =
    D.mk_context [ new_parent_node ] [] [] ctx.A.sibling_idx new_func_name
  in
  let translated_stmt =
    translate_stmt ast model_map maps.Maps.node_map ast_map_rev loopup_maps stmt
  in
  D.DeleteStmt (ctx, translated_stmt)

let translate_update_exp ast parent_id ctx e1 e2 model_map maps ast_map_rev
    parent_facts =
  let loopup_maps =
    { Maps.exp_map = maps.Maps.exp_map; lval_map = maps.Maps.lval_map }
  in
  let new_parent_node, new_func_name =
    get_parent_of_stmt parent_id model_map ast_map_rev parent_facts
  in
  let ctx =
    D.mk_context [ new_parent_node ] [] [] ctx.A.sibling_idx new_func_name
  in
  let translated_e1 = translate_exp ast model_map loopup_maps e1 in
  let translated_e2 = translate_exp ast model_map loopup_maps e2 in
  D.UpdateExp (ctx, translated_e1, translated_e2)

let translate ast abs_diff model_path maps patch_node_ids parent_facts =
  Logger.info "Translating patch...";
  let model_map = H.parse_model model_path in
  let ast_map_rev = Utils.reverse_hashtbl maps.Maps.ast_map in
  List.fold_left2
    (fun acc diff parent_id ->
      match diff with
      | A.SInsertStmt (ctx, stmt) ->
          translate_insert_stmt ast parent_id ctx stmt model_map maps
            ast_map_rev parent_facts
          :: acc
      | SDeleteStmt (ctx, stmt) ->
          translate_delete_stmt ast parent_id ctx stmt model_map maps
            ast_map_rev parent_facts
          :: acc
      | SUpdateExp (ctx, e1, e2) ->
          translate_update_exp ast parent_id ctx e1 e2 model_map maps
            ast_map_rev parent_facts
          :: acc
      | _ -> failwith "translate: not implemented")
    [] abs_diff patch_node_ids
