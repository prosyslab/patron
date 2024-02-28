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

let translate_node_lst sol_map lst =
  List.fold_left
    ~f:(fun acc x ->
      match Hashtbl.find_opt sol_map x with Some x -> x :: acc | None -> acc)
    ~init:[] lst

let of_exp node =
  match node with Ast.Exp e -> e | _ -> failwith "extract_cil: not exp"

let swap_lval = ref []
let swap_exp = ref []

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
          || List.exists ~f:(lvalVisitor#search_exp target) args
      | None -> List.exists ~f:(lvalVisitor#search_exp target) args

    method search_set target lval exp =
      lvalVisitor#search_lval target lval || lvalVisitor#search_exp target exp

    method search_instr target instrs =
      if List.length instrs = 0 then false
      else
        let i = List.hd_exn instrs in
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
          || List.exists ~f:(expVisitor#search_exp target) args
      | None -> List.exists ~f:(expVisitor#search_exp target) args

    method search_set target lval exp =
      expVisitor#search_lval target lval || expVisitor#search_exp target exp

    method search_instr target instrs =
      if List.length instrs = 0 then false
      else
        let i = List.hd_exn instrs in
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

let rec translate_offset ast sol_map lookup_maps abs_offset offset =
  match (abs_offset, offset) with
  | A.SNoOffset, Cil.NoOffset -> offset
  | A.SField (_, o), Cil.Field (f, o') ->
      Cil.Field (f, translate_offset ast sol_map lookup_maps o o')
  | A.SIndex (e, o), Cil.Index (_, o') ->
      let new_e = translate_exp ast sol_map lookup_maps e.ast in
      let new_o = translate_offset ast sol_map lookup_maps o o' in
      Cil.Index (new_e, new_o)
  | _ -> failwith "translate_offset: concrete and abstract offset not matched"

and translate_lhost ast sol_map lookup_maps abs_lhost lhost =
  match (abs_lhost, lhost) with
  | A.SMem e, Cil.Mem _ -> Cil.Mem (translate_exp ast sol_map lookup_maps e.ast)
  | A.SVar _, Cil.Var _ -> lhost
  | _ -> failwith "translate_lhost: concrete and abstract lhost not matched"

and break_down_translate_lval ast sol_map lookup_maps lval =
  match lval with
  | A.AbsLval (sym, cil) -> (
      match (sym, cil) with
      | A.SLNull, _ -> failwith "translate_lval:Lval is null"
      | A.Lval (abs_lhost, abs_offset), (lhost, offset) ->
          ( translate_lhost ast sol_map lookup_maps abs_lhost lhost,
            translate_offset ast sol_map lookup_maps abs_offset offset ))
  | _ -> failwith "translate_lval: translation target is not an lvalue"

and translate_lval ast sol_map (lookup_maps : Maps.translation_lookup_maps)
    slval =
  let donor_id =
    if StrSet.is_empty slval.A.ids then "None" else StrSet.choose slval.A.ids
  in
  if Hashtbl.mem sol_map donor_id then (
    let new_lv_str =
      Hashtbl.find sol_map donor_id |> Hashtbl.find lookup_maps.lval_map
    in
    swap_lval := [];
    let vis :> Cil.cilVisitor = new lvTranslationVisitor new_lv_str in
    ignore (Cil.visitCilFile vis ast);
    List.hd_exn !swap_lval)
  else break_down_translate_lval ast sol_map lookup_maps slval.A.ast

and translate_exp ast sol_map (lookup_maps : Maps.translation_lookup_maps) =
  function
  | A.AbsExp (sym, cil) -> (
      match (sym, cil) with
      | A.SConst _, Cil.Const _ -> cil
      | A.SELval l, Cil.Lval _ ->
          let lval = translate_lval ast sol_map lookup_maps l in
          Cil.Lval lval
      | A.SBinOp (_, l, r, _), Cil.BinOp (op', _, _, t') ->
          let lval = translate_exp ast sol_map lookup_maps l.A.ast in
          let rval = translate_exp ast sol_map lookup_maps r.A.ast in
          Cil.BinOp (op', lval, rval, t')
      | A.SCastE (_, e), Cil.CastE (t, _) ->
          let exp = translate_exp ast sol_map lookup_maps e.A.ast in
          Cil.CastE (t, exp)
      | A.SUnOp (_, t, _), Cil.UnOp (op', _, t') ->
          let exp = translate_exp ast sol_map lookup_maps t.A.ast in
          Cil.UnOp (op', exp, t')
      | A.SSizeOfE e, Cil.SizeOfE _ ->
          let exp = translate_exp ast sol_map lookup_maps e.A.ast in
          Cil.SizeOfE exp
      | A.SAddrOf l, Cil.AddrOf _ ->
          let lval = translate_lval ast sol_map lookup_maps l in
          Cil.AddrOf lval
      | A.SStartOf l, Cil.StartOf _ ->
          let lval = translate_lval ast sol_map lookup_maps l in
          Cil.StartOf lval
      | A.SQuestion (a, b, c, _), Cil.Question (_, _, _, t) ->
          let cond = translate_exp ast sol_map lookup_maps a.A.ast in
          let b_exp = translate_exp ast sol_map lookup_maps b.A.ast in
          let c_exp = translate_exp ast sol_map lookup_maps c.A.ast in
          Cil.Question (cond, b_exp, c_exp, t)
      | A.SSizeOf _, Cil.SizeOf _ | A.SSizeOfStr _, Cil.SizeOfStr _ | _ ->
          Utils.print_ekind cil;
          failwith "translate_exp: not implemented")
  | _ -> failwith "translate_exp: translation target is not an expression"

let rec translate_if_stmt ast sol_map lookup_maps scond sthen_block selse_block
    =
  let cond = translate_exp ast sol_map lookup_maps scond.A.ast in
  let then_block =
    List.fold_left
      ~f:(fun acc ss ->
        translate_new_stmt ast sol_map lookup_maps ss.A.ast :: acc)
      ~init:[] sthen_block
    |> List.rev
  in
  let else_block =
    List.fold_left
      ~f:(fun acc ss ->
        translate_new_stmt ast sol_map lookup_maps ss.A.ast :: acc)
      ~init:[] selse_block
    |> List.rev
  in
  Cil.mkStmt
    (Cil.If
       (cond, Cil.mkBlock then_block, Cil.mkBlock else_block, Cil.locUnknown))

and translate_instr ast sol_map (lookup_maps : Maps.translation_lookup_maps)
    abs_instr i =
  match (abs_instr, List.hd_exn i) with
  | A.SSet (l, r), Cil.Set _ ->
      let lval = translate_lval ast sol_map lookup_maps l in
      let rval = translate_exp ast sol_map lookup_maps r.A.ast in
      Cil.mkStmt (Cil.Instr [ Cil.Set (lval, rval, Cil.locUnknown) ])
  | A.SCall (Some l, f, args), Cil.Call _ ->
      let lval = translate_lval ast sol_map lookup_maps l in
      let fun_exp = translate_exp ast sol_map lookup_maps f.A.ast in
      let args =
        List.fold_left
          ~f:(fun acc arg ->
            translate_exp ast sol_map lookup_maps arg.A.ast :: acc)
          ~init:[] args
        |> List.rev
      in
      Cil.mkStmt
        (Cil.Instr [ Cil.Call (Some lval, fun_exp, args, Cil.locUnknown) ])
  | A.SCall (None, f, args), Cil.Call _ ->
      let fun_exp = A.get_original_exp f in
      let args =
        List.fold_left
          ~f:(fun acc arg ->
            translate_exp ast sol_map lookup_maps arg.A.ast :: acc)
          ~init:[] args
        |> List.rev
      in
      Cil.mkStmt (Cil.Instr [ Cil.Call (None, fun_exp, args, Cil.locUnknown) ])
  | _ ->
      failwith "translate_stmt: translation target is not an instruction type"

and translate_new_stmt ast sol_map lookup_maps = function
  | A.AbsStmt (sym, cil) -> (
      match (sym, cil.Cil.skind) with
      | A.SIf (scond, sthen_block, selse_block), Cil.If _ ->
          translate_if_stmt ast sol_map lookup_maps scond sthen_block
            selse_block
      | A.SReturn (Some sym), Cil.Return _ ->
          let exp = translate_exp ast sol_map lookup_maps sym.A.ast in
          Cil.mkStmt (Cil.Return (Some exp, Cil.locUnknown))
      | A.SReturn None, Cil.Return _ ->
          Cil.mkStmt (Cil.Return (None, Cil.locUnknown))
      | A.SGoto _, Cil.Goto _ -> cil
      | abs_instr, Cil.Instr i ->
          translate_instr ast sol_map lookup_maps abs_instr i
      | _ -> failwith "translate_stmt: not implemented")
  | _ -> failwith "translate_stmt: translation target is not a statement type"

let translate_new_stmts ast sol_map lookup_maps =
  List.map ~f:(fun abs_node ->
      translate_new_stmt ast sol_map lookup_maps abs_node.A.ast)

let translate_id sol_map id = Hashtbl.find_opt sol_map id

let translate_ids sol_map ids =
  StrSet.fold
    (fun id new_ids ->
      translate_id sol_map id
      |> Option.fold ~f:(fun ids fn -> StrSet.add fn ids) ~init:new_ids)
    ids StrSet.empty

let extract_func_name node_id = String.split ~on:'-' node_id |> List.hd_exn

let translate_func_name sol_map abs_node_lst =
  A.collect_node_id abs_node_lst
  |> translate_ids sol_map |> StrSet.choose |> extract_func_name

let ids2asts ast_map ids =
  StrSet.fold
    (fun id asts ->
      let ast_opt = Hashtbl.find_opt ast_map id in
      if Option.is_some ast_opt then
        let ast = Option.value_exn ast_opt in
        AstSet.add ast asts
      else asts)
    ids AstSet.empty

let translate_orig_stmts sol_map ast_map abs_node_lst =
  let new_ids = A.collect_node_id abs_node_lst |> translate_ids sol_map in
  let new_asts = ids2asts ast_map new_ids in
  AstSet.fold (fun ast stmts -> Ast.to_stmt ast :: stmts) new_asts []
  |> List.rev

let translate_insert_stmt ast sol_map maps ast_map before after ss =
  let lookup_maps =
    { Maps.exp_map = maps.Maps.exp_map; lval_map = maps.Maps.lval_map }
  in
  let target_func_name = translate_func_name sol_map before in
  let target_before = translate_orig_stmts sol_map ast_map before in
  L.info "num of before: %i" (List.length target_before);
  let new_ss = translate_new_stmts ast sol_map lookup_maps ss in
  let target_after = translate_orig_stmts sol_map ast_map after in
  D.InsertStmt (target_func_name, target_before, new_ss, target_after)

let translate ast abs_diff out_dir target_alarm maps =
  Logger.info "Translating patch...";
  let sol_map = Hashtbl.create 1000 in
  Hashtbl.reset sol_map;
  H.parse_map out_dir (target_alarm ^ "_sol.map") sol_map;
  List.map
    ~f:(fun diff ->
      match diff with
      | A.SInsertStmt (before, ss, after) ->
          translate_insert_stmt ast sol_map maps maps.Maps.ast_map before after
            ss
      | _ -> failwith "translate: not implemented")
    abs_diff
