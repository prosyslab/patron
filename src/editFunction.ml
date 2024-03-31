open Core
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module J = Yojson.Basic.Util
module D = Diff
module A = AbsDiff
module H = Utils
module L = Logger
module AstSet = Set.Make (Ast)
module StrSet = Set.Make (String)

let translate_id sol_map id = Hashtbl.find_opt sol_map id

let translate_ids sol_map ids =
  StrSet.fold
    (fun id new_ids ->
      translate_id sol_map id
      |> Option.fold ~f:(fun ids new_id -> StrSet.add new_id ids) ~init:new_ids)
    ids StrSet.empty

let fst_of_branch b s =
  match s.Cil.skind with
  | Cil.If (_, tb, fb, _) ->
      if b then List.hd tb.bstmts |> Option.value ~default:s
      else List.hd fb.bstmts |> Option.value ~default:s
  | _ -> L.error "fst_of_branch - wrong stmt"

let ids2asts maps ids =
  StrSet.fold
    (fun id asts ->
      let ast_opt = Hashtbl.find_opt maps.Maps.ast_map id in
      if Option.is_some ast_opt then
        let ast = Option.value_exn ast_opt in
        if Ast.is_stmt ast then
          let ast =
            match Hashtbl.find maps.Maps.cmd_map id with
            | Maps.Assume b ->
                Ast.to_stmt ast |> fst_of_branch b |> Option.some |> Ast.of_stmt
            | _ -> ast
          in
          AstSet.add ast asts
        else AstSet.add ast asts
      else asts)
    ids AstSet.empty

let rec translate_offset maps sol_map abs_offset offset =
  match (abs_offset, offset) with
  | A.SNoOffset, Cil.NoOffset -> offset
  | A.SField (_, o), Cil.Field (f, o') ->
      Cil.Field (f, translate_offset maps sol_map o o')
  | A.SIndex (e, o), Cil.Index (_, o') ->
      let new_e = translate_exp maps sol_map e.ast in
      let new_o = translate_offset maps sol_map o o' in
      Cil.Index (new_e, new_o)
  | _ -> L.error "translate_offset - concrete and abstract offset not matched"

and translate_lhost maps sol_map abs_lhost lhost =
  match (abs_lhost, lhost) with
  | A.SMem e, Cil.Mem _ -> Cil.Mem (translate_exp maps sol_map e.ast)
  | A.SVar _, Cil.Var _ -> lhost
  | _ -> L.error "translate_lhost - concrete and abstract lhost not matched"

and break_down_translate_lval maps sol_map lval =
  match lval with
  | A.AbsLval (sym, cil) -> (
      match (sym, cil) with
      | A.SLNull, _ -> L.error "translate_lval - Lval is null"
      | A.Lval (abs_lhost, abs_offset), (lhost, offset) ->
          ( translate_lhost maps sol_map abs_lhost lhost,
            translate_offset maps sol_map abs_offset offset ))
  | _ -> L.error "translate_lval - translation target is not an lvalue"

and translate_lval maps sol_map slval =
  let new_lvs = translate_ids sol_map slval.A.ids |> ids2asts maps in
  if AstSet.is_empty new_lvs then
    break_down_translate_lval maps sol_map slval.A.ast
  else AstSet.choose new_lvs |> Ast.to_lval

and translate_exp maps sol_map = function
  | A.AbsExp (sym, cil) -> (
      match (sym, cil) with
      | A.SConst _, Cil.Const _ -> cil
      | A.SELval l, Cil.Lval _ ->
          let lval = translate_lval maps sol_map l in
          Cil.Lval lval
      | A.SBinOp (_, l, r, _), Cil.BinOp (op', _, _, t') ->
          let lval = translate_exp maps sol_map l.A.ast in
          let rval = translate_exp maps sol_map r.A.ast in
          Cil.BinOp (op', lval, rval, t')
      | A.SCastE (_, e), Cil.CastE (t, _) ->
          let exp = translate_exp maps sol_map e.A.ast in
          Cil.CastE (t, exp)
      | A.SUnOp (_, t, _), Cil.UnOp (op', _, t') ->
          let exp = translate_exp maps sol_map t.A.ast in
          Cil.UnOp (op', exp, t')
      | A.SSizeOfE e, Cil.SizeOfE _ ->
          let exp = translate_exp maps sol_map e.A.ast in
          Cil.SizeOfE exp
      | A.SAddrOf l, Cil.AddrOf _ ->
          let lval = translate_lval maps sol_map l in
          Cil.AddrOf lval
      | A.SStartOf l, Cil.StartOf _ ->
          let lval = translate_lval maps sol_map l in
          Cil.StartOf lval
      | A.SQuestion (a, b, c, _), Cil.Question (_, _, _, t) ->
          let cond = translate_exp maps sol_map a.A.ast in
          let b_exp = translate_exp maps sol_map b.A.ast in
          let c_exp = translate_exp maps sol_map c.A.ast in
          Cil.Question (cond, b_exp, c_exp, t)
      | A.SSizeOf _, e -> e
      | A.SSizeOfStr _, Cil.SizeOfStr _ | _ ->
          Utils.print_ekind cil;
          L.error "translate_exp - not implemented")
  | _ -> L.error "translate_exp - translation target is not an expression"

let rec translate_if_stmt maps sol_map scond sthen_block selse_block =
  let cond = translate_exp maps sol_map scond.A.ast in
  let then_block =
    List.fold_left
      ~f:(fun acc ss -> translate_new_stmt maps sol_map ss.A.ast :: acc)
      ~init:[] sthen_block
    |> List.rev
  in
  let else_block =
    List.fold_left
      ~f:(fun acc ss -> translate_new_stmt maps sol_map ss.A.ast :: acc)
      ~init:[] selse_block
    |> List.rev
  in
  Cil.mkStmt
    (Cil.If
       (cond, Cil.mkBlock then_block, Cil.mkBlock else_block, Cil.locUnknown))

and translate_instr maps sol_map abs_instr i =
  match (abs_instr, List.hd_exn i) with
  | A.SSet (l, r), Cil.Set _ ->
      let lval = translate_lval maps sol_map l in
      let rval = translate_exp maps sol_map r.A.ast in
      Cil.mkStmt (Cil.Instr [ Cil.Set (lval, rval, Cil.locUnknown) ])
  | A.SCall (Some l, f, args), Cil.Call _ ->
      let lval = translate_lval maps sol_map l in
      let fun_exp = translate_exp maps sol_map f.A.ast in
      let args =
        List.fold_left
          ~f:(fun acc arg -> translate_exp maps sol_map arg.A.ast :: acc)
          ~init:[] args
        |> List.rev
      in
      Cil.mkStmt
        (Cil.Instr [ Cil.Call (Some lval, fun_exp, args, Cil.locUnknown) ])
  | A.SCall (None, f, args), Cil.Call _ ->
      let fun_exp = A.get_original_exp f in
      let args =
        List.fold_left
          ~f:(fun acc arg -> translate_exp maps sol_map arg.A.ast :: acc)
          ~init:[] args
        |> List.rev
      in
      Cil.mkStmt (Cil.Instr [ Cil.Call (None, fun_exp, args, Cil.locUnknown) ])
  | a, i ->
      L.error
        "translate_stmt - translation target is not an instruction type:\n\
         %a\n\
         %s"
        AbsDiff.pp_absstmt a (Ast.s_instr i)

and translate_new_stmt maps sol_map = function
  | A.AbsStmt (sym, cil) -> (
      match (sym, cil.Cil.skind) with
      | A.SIf (scond, sthen_block, selse_block), Cil.If _ ->
          translate_if_stmt maps sol_map scond sthen_block selse_block
      | A.SReturn (Some sym), Cil.Return _ ->
          let exp = translate_exp maps sol_map sym.A.ast in
          Cil.mkStmt (Cil.Return (Some exp, Cil.locUnknown))
      | A.SReturn None, Cil.Return _ ->
          Cil.mkStmt (Cil.Return (None, Cil.locUnknown))
      | A.SGoto _, Cil.Goto _ -> cil
      | abs_instr, Cil.Instr i -> translate_instr maps sol_map abs_instr i
      | _ -> L.error "translate_stmt - not implemented")
  | _ -> L.error "translate_stmt - translation target is not a statement type"

let translate_new_stmts maps sol_map =
  List.map ~f:(fun abs_node -> translate_new_stmt maps sol_map abs_node.A.ast)

let translate_func_name sol_map abs_node_lst =
  abs_node_lst |> translate_ids sol_map |> StrSet.choose
  |> Utils.get_func_name_from_node

let translate_orig_stmts maps sol_map abs_nodes =
  let new_asts = abs_nodes |> translate_ids sol_map |> ids2asts maps in
  AstSet.fold
    (fun ast stmts ->
      (* NOTE: function entry is not used for now *)
      if Ast.is_stmt ast then Ast.to_stmt ast :: stmts else stmts)
    new_asts []
  |> List.rev

let translate_insert_stmt maps sol_map before after ss =
  let target_before = translate_orig_stmts maps sol_map before in
  let target_after = translate_orig_stmts maps sol_map after in
  let target_func_name =
    translate_func_name sol_map
      (if List.is_empty target_before then after else before)
  in
  let new_ss = translate_new_stmts maps sol_map ss in
  D.InsertStmt (target_func_name, target_before, new_ss, target_after)

let translate_delete_stmt maps sol_map s =
  let target_func_name = translate_func_name sol_map (StrSet.singleton s) in
  let new_s =
    translate_orig_stmts maps sol_map (StrSet.singleton s) |> List.hd_exn
  in
  D.DeleteStmt (target_func_name, new_s)

let translate_update_stmt maps sol_map before after ss =
  let target_before = translate_orig_stmts maps sol_map before in
  let target_after = translate_orig_stmts maps sol_map after in
  let target_func_name =
    translate_func_name sol_map
      (if List.is_empty target_before then after else before)
  in
  let new_ss = translate_new_stmts maps sol_map ss in
  D.UpdateStmt (target_func_name, target_before, new_ss, target_after)

let translate_update_exp maps sol_map s e1 e2 =
  let target_func_name = translate_func_name sol_map (StrSet.singleton s) in
  (* NOTE: abs_stmt is exactly that one *)
  let new_s =
    translate_orig_stmts maps sol_map (StrSet.singleton s) |> List.hd_exn
  in
  let new_e1 = translate_exp maps sol_map e1.A.ast in
  let new_e2 = translate_exp maps sol_map e2.A.ast in
  D.UpdateExp (target_func_name, new_s, new_e1, new_e2)

let translate_update_callexp maps sol_map s s2 =
  let target_func_name = translate_func_name sol_map (StrSet.singleton s) in
  let new_s =
    translate_orig_stmts maps sol_map (StrSet.singleton s) |> List.hd_exn
  in
  let new_s2 = translate_new_stmt maps sol_map s2.A.ast in
  D.UpdateCallExp (target_func_name, new_s, new_s2)

let translate maps out_dir target_alarm abs_diff =
  Logger.info "Translating patch...";
  let sol_map = Hashtbl.create 1000 in
  Hashtbl.reset sol_map;
  H.parse_map out_dir (target_alarm ^ "_sol.map") sol_map;
  List.map
    ~f:(fun diff ->
      match diff with
      | A.SInsertStmt (before, ss, after) ->
          translate_insert_stmt maps sol_map before after ss
      | A.SDeleteStmt s -> translate_delete_stmt maps sol_map s
      | A.SUpdateStmt (before, ss, after) ->
          translate_update_stmt maps sol_map before after ss
      | A.SUpdateExp (s, e1, e2) -> translate_update_exp maps sol_map s e1 e2
      | A.SUpdateCallExp (s, s2) -> translate_update_callexp maps sol_map s s2
      | _ -> L.error "translate - not implemented")
    abs_diff
