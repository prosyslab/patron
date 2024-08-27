open Core
module D = Diff
module EF = EditFunction
module H = Utils
module L = Logger

let target_func = ref []

(* close to the before *)
let first_patch_strat = ref None

(* close to the snk *)
let second_patch_strat = ref None
let first_strat_parent = ref None
let second_strat_parent = ref None
let first_strat = 0
let second_strat = 1
let patch_strat_priority = ref first_strat
let patron_tmp_var_cnt = ref 0
let vdec_map = Hashtbl.create (module String)

class funcFinder func =
  object
    inherit Cil.nopCilVisitor

    method! vglob glob =
      match glob with
      | Cil.GFun (fd, _) ->
          if String.equal fd.svar.vname func then (
            target_func := fd :: !target_func;
            SkipChildren)
          else Cil.SkipChildren
      | _ -> Cil.SkipChildren
  end

let extract_fundec func_name ast =
  target_func := [];
  let vis = new funcFinder func_name in
  Cil.visitCilFile vis ast;
  List.hd_exn !target_func

let is_in_stmt s_opt b =
  let s = Option.value_exn s_opt in
  List.exists ~f:(fun stmt -> phys_equal s stmt) b

let is_func_var v = match v.Cil.vtype with Cil.TFun _ -> true | _ -> false

let insert_var_dec v =
  let func_dec = List.hd_exn !target_func in
  Cil.makeLocalVar func_dec v.Cil.vname v.Cil.vtype |> ignore

let mk_patron_tmp_var v =
  if Hashtbl.mem vdec_map v.Cil.vname then
    let new_vname = Hashtbl.find_exn vdec_map v.Cil.vname in
    Cil.makeVarinfo false new_vname v.Cil.vtype
  else
    let new_vname = "__patron_tmp" ^ string_of_int !patron_tmp_var_cnt in
    patron_tmp_var_cnt := !patron_tmp_var_cnt + 1;
    Hashtbl.add_exn vdec_map ~key:v.Cil.vname ~data:new_vname;
    Cil.makeLocalVar (List.hd_exn !target_func) new_vname v.Cil.vtype

let transform_lval lv fundec =
  match lv with
  | Cil.Var v, off when not (is_func_var v) -> (
      let v' =
        if Str.string_match (Str.regexp ".*__cil_tmp.*") v.Cil.vname 0 then (
          insert_var_dec v;
          Some (mk_patron_tmp_var v))
        else
          List.find
            ~f:(fun v' -> String.equal v.vname v'.Cil.vname)
            fundec.Cil.slocals
      in
      match v' with
      | Some v' -> (Cil.Var v', off)
      | None ->
          if not (Hashtbl.mem vdec_map v.Cil.vname) then (
            insert_var_dec v;
            Hashtbl.add_exn vdec_map ~key:v.Cil.vname ~data:v.Cil.vname);
          lv)
  | _ -> lv

let rec transform_exp e fundec =
  match e with
  | Cil.Lval lv -> Cil.Lval (transform_lval lv fundec)
  | Cil.CastE (t, e) -> Cil.CastE (t, transform_exp e fundec)
  | Cil.BinOp (b, e1, e2, t) ->
      Cil.BinOp (b, transform_exp e1 fundec, transform_exp e2 fundec, t)
  | Cil.UnOp (u, e, t) -> Cil.UnOp (u, transform_exp e fundec, t)
  | _ -> e

let transform_instr i fundec =
  match i with
  | Cil.Set (lv, e, loc) ->
      let lv' = transform_lval lv fundec in
      let e' = transform_exp e fundec in
      Cil.Set (lv', e', loc)
  | Cil.Call (lv, e, el, loc) ->
      let lv' = Option.map ~f:(fun lv -> transform_lval lv fundec) lv in
      let el' = List.map ~f:(fun e -> transform_exp e fundec) el in
      Cil.Call (lv', e, el', loc)
  | _ -> i

let transform_return e loc fundec =
  match fundec.Cil.svar.vtype with
  | Cil.TVoid _ -> Cil.Return (None, loc)
  | Cil.TInt _ ->
      if Option.is_none e then
        Cil.Return
          ( Some (Cil.Const (Cil.CInt64 (Int64.of_int (-1), Cil.IInt, None))),
            loc )
      else Cil.Return (e, loc)
  | _ -> Cil.Return (e, loc)

let rec transform_stmt s fundec =
  match s.Cil.skind with
  | Cil.Instr instrs ->
      let instrs' = List.map ~f:(fun i -> transform_instr i fundec) instrs in
      { s with skind = Cil.Instr instrs' }
  | Cil.Return (e, loc) -> { s with skind = transform_return e loc fundec }
  | Cil.If (e, tb, fb, loc) ->
      let e' = transform_exp e fundec in
      let tb'_stmts =
        List.fold_left
          ~f:(fun acc s -> transform_stmt s fundec :: acc)
          ~init:[] tb.bstmts
      in
      let tb' = { tb with bstmts = List.rev tb'_stmts } in
      let fb'_stmts =
        List.fold_left
          ~f:(fun acc s -> transform_stmt s fundec :: acc)
          ~init:[] fb.bstmts
      in
      let fb' = { fb with bstmts = List.rev fb'_stmts } in
      { s with skind = Cil.If (e', tb', fb', loc) }
  | _ -> s

let fit_stmt_to_donee s func_name donee =
  let fun_dec = extract_fundec func_name donee in
  transform_stmt s fun_dec

let is_patched = ref false

let partition mid stmts =
  let blst, _, alst =
    List.fold_left
      ~f:(fun (blst, found, alst) stmt ->
        if not found then
          if phys_equal stmt mid then (blst, true, alst)
          else (stmt :: blst, found, alst)
        else (blst, found, stmt :: alst))
      ~init:([], false, []) stmts
  in
  (List.rev blst, List.rev alst)

type insert_mode = Before | After

let line_partition stmts =
  let get_last_loc stmt =
    match stmt.Cil.skind with
    | Cil.Instr instrs ->
        if List.is_empty instrs then None
        else Some (Cil.get_instrLoc (List.last_exn instrs))
    | _ -> Some (Cil.get_stmtLoc stmt.Cil.skind)
  in
  let partition stmt tmp_stack full_stack =
    let target_loc = Cil.get_stmtLoc stmt.Cil.skind in
    if List.is_empty tmp_stack then ([ stmt ], full_stack)
    else
      let last_stmt = List.last_exn tmp_stack in
      let last_loc_opt = get_last_loc last_stmt in
      if Option.is_none last_loc_opt then (tmp_stack, full_stack)
      else
        let last_loc = Option.value_exn last_loc_opt in
        if Int.equal last_loc.line target_loc.Cil.line then
          (stmt :: tmp_stack, full_stack)
        else (stmt :: [], List.rev tmp_stack :: full_stack)
  in
  let last_stmt, blk =
    List.fold_left
      ~f:(fun (tmp_stack, full_stack) stmt ->
        partition stmt tmp_stack full_stack)
      ~init:([], []) stmts
  in
  last_stmt :: blk |> List.rev

let insert_patch_before_snk snk patch blk =
  let partitioned_blk = line_partition blk in
  List.fold_right
    ~f:(fun stmts acc ->
      let first_stmt = List.hd stmts in
      if Option.is_none first_stmt then stmts @ acc
      else
        let snk_loc = Cil.get_stmtLoc snk.Cil.skind in
        match (Option.value_exn first_stmt).skind with
        | Cil.Instr instrs ->
            if
              List.exists
                ~f:(fun i -> Cil.get_instrLoc i |> Ast.eq_location snk_loc)
                instrs
            then patch @ stmts @ acc
            else stmts @ acc
        | _ ->
            if
              Cil.get_stmtLoc (Option.value_exn first_stmt).skind
              |> Ast.eq_location snk_loc
            then patch @ stmts @ acc
            else stmts @ acc)
    ~init:[] partitioned_blk

class insertStmtsecondVisitor snk patch =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      if is_in_stmt (Some snk) b.bstmts then (
        let new_bstmts = insert_patch_before_snk snk patch b.bstmts in
        second_strat_parent := Some b;
        second_patch_strat := Some { b with bstmts = new_bstmts };
        DoChildren)
      else DoChildren
  end

let choose_patch_strat using assist_opt =
  match using with
  | Before when Option.is_some assist_opt -> patch_strat_priority := first_strat
  | After -> patch_strat_priority := first_strat
  | _ -> patch_strat_priority := second_strat

let insert_internal ?(using = Before) ?(update = false) assist_opt snk_opt patch
    stmts =
  choose_patch_strat using assist_opt;
  if Option.is_none assist_opt then
    let stmts = List.rev stmts in
    match using with Before -> patch @ stmts | After -> stmts @ patch
  else
    let assist = Option.value_exn assist_opt in
    let rev_or_not = match using with Before -> Fun.id | After -> List.rev in
    let new_stmts, patched =
      List.fold_left
        ~f:(fun (new_stmts, patched) stmt ->
          if phys_equal stmt assist || (update && Ast.is_cil_goto stmt.Cil.skind)
          then (rev_or_not patch @ (assist :: new_stmts), true)
          else (stmt :: new_stmts, patched))
        ~init:([], false) (rev_or_not stmts)
    in
    let new_stmts = rev_or_not new_stmts in
    if patched then new_stmts
    else
      match using with
      | Before -> patch @ new_stmts
      | After when Option.is_some snk_opt ->
          if not (is_in_stmt snk_opt new_stmts) then
            patch_strat_priority := second_strat;
          new_stmts @ patch
      | _ -> new_stmts @ patch

let insert_ss ?(using = After) ?(update = false) snk_opt before_opt after_opt
    patch stmts =
  let mid, assist_opt =
    match using with
    | Before -> (Option.value_exn before_opt, after_opt)
    | After -> (Option.value_exn after_opt, before_opt)
  in
  let blst, alst = partition mid stmts in
  match mid.Cil.skind with
  (* | Cil.Loop (block, loc, t1, t2) ->
      let new_b_stmts =
        insert_internal ~using ~update snk_opt assist_opt patch
          (List.rev block.bstmts)
      in
      let new_stmt =
        Cil.Loop ({ block with bstmts = new_b_stmts }, loc, t1, t2)
      in
      blst @ [ { mid with skind = new_stmt } ] @ alst *)
  | Cil.If (e, tb, fb, loc) ->
      (* TODO: check true branch false branch *)
      if List.is_empty tb.bstmts then
        let new_b_stmts =
          insert_internal ~using ~update snk_opt assist_opt patch
            (List.rev tb.bstmts)
        in
        let new_stmt = Cil.If (e, { tb with bstmts = new_b_stmts }, fb, loc) in
        blst @ [ { mid with skind = new_stmt } ] @ alst
      else
        let new_b_stmts =
          insert_internal ~using ~update snk_opt assist_opt patch
            (List.rev fb.bstmts)
        in
        let new_stmt = Cil.If (e, tb, { fb with bstmts = new_b_stmts }, loc) in
        blst @ [ { mid with skind = new_stmt } ] @ alst
  | _ -> (
      match using with
      | Before ->
          let new_alst =
            insert_internal ~using ~update snk_opt assist_opt patch
              (List.rev alst)
          in
          blst @ [ mid ] @ new_alst
      | After ->
          let new_blst =
            insert_internal ~using ~update snk_opt assist_opt patch
              (List.rev blst)
          in
          new_blst @ [ mid ] @ alst)

class insertStmtfirstVisitor ?(update = false) snk before after ss =
  object
    inherit Cil.nopCilVisitor

    method! vblock b =
      if Option.is_some after then
        if is_in_stmt after b.bstmts then (
          Option.value_exn after |> Ast.s_stmt |> print_endline;
          let new_stmts =
            insert_ss ~using:After ~update snk before after ss b.bstmts
          in
          first_strat_parent := Some b;
          first_patch_strat := Some { b with bstmts = new_stmts };
          SkipChildren)
        else if Option.is_some before && is_in_stmt before b.bstmts then (
          let new_stmts =
            insert_ss ~using:Before ~update snk before after ss b.bstmts
          in
          first_strat_parent := Some b;
          first_patch_strat := Some { b with bstmts = new_stmts };
          SkipChildren)
        else DoChildren
      else DoChildren
  end

class insertStmtApplyVisitor before after =
  object
    inherit Cil.nopCilVisitor

    method! vblock b =
      if Ast.eq_blk b before then ChangeTo after else DoChildren
  end

let mk_patched_func f new_b old_b_opt =
  let old_b = Option.value_exn old_b_opt in
  Cil.visitCilFunction (new insertStmtApplyVisitor old_b new_b) f |> ignore;
  f

class insertStmtVisitor ?(update = false) target_func snk_opt before after ss =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then (
        Cil.visitCilFunction
          (new insertStmtfirstVisitor ~update snk_opt before after ss)
          f
        |> ignore;
        if Option.is_some snk_opt then
          Cil.visitCilFunction
            (new insertStmtsecondVisitor (Option.value_exn snk_opt) ss)
            f
          |> ignore;
        if
          Option.is_some !first_patch_strat
          || Option.is_some !second_patch_strat
        then is_patched := true;
        match (!first_patch_strat, !second_patch_strat) with
        | Some first_opt, Some second_opt ->
            string_of_int !patch_strat_priority |> print_endline;
            if Int.equal !patch_strat_priority first_strat then
              let _ = print_endline "first" in
              ChangeTo (mk_patched_func f first_opt !first_strat_parent)
            else ChangeTo (mk_patched_func f second_opt !second_strat_parent)
        | _, Some second_opt ->
            ChangeTo (mk_patched_func f second_opt !second_strat_parent)
        | Some first_opt, _ ->
            ChangeTo (mk_patched_func f first_opt !first_strat_parent)
        | _ -> DoChildren)
      else DoChildren
  end

let delete_elt_stmt s stmts =
  let new_stmts, patched =
    List.fold_left
      ~f:(fun (new_stmts, patched) stmt ->
        if (not patched) && phys_equal stmt s then (new_stmts, true)
        else (stmt :: new_stmts, patched))
      ~init:([], false) stmts
  in
  (List.rev new_stmts, patched)

let update_elt_stmt s ss stmts =
  let new_stmts, patched =
    List.fold_left
      ~f:(fun (new_stmts, patched) stmt ->
        if (not patched) && phys_equal stmt s then (ss @ new_stmts, true)
        else (stmt :: new_stmts, patched))
      ~init:([], false) stmts
  in
  (List.rev new_stmts, patched)

class deleteStmtfromBlockVisitor s =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      let new_bstmts, patched = delete_elt_stmt s b.bstmts in
      if patched then (
        is_patched := true;
        ChangeTo { b with bstmts = new_bstmts })
      else DoChildren
  end

class deleteStmtfromFuncVisitor target_func ss =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then
        let vis = new deleteStmtfromBlockVisitor ss in
        ChangeTo (Cil.visitCilFunction vis f)
      else SkipChildren
  end

class updateStmtfromBlockVisitor s ss =
  object
    inherit Cil.nopCilVisitor

    method! vblock (b : Cil.block) =
      let new_bstmts, patched = update_elt_stmt s ss b.bstmts in
      if patched then (
        is_patched := true;
        ChangeTo { b with bstmts = new_bstmts })
      else DoChildren
  end

class updateStmtfromFuncVisitor target_func s ss =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then
        let vis = new updateStmtfromBlockVisitor s ss in
        ChangeTo (Cil.visitCilFunction vis f)
      else SkipChildren
  end

class replaceExpVisitor from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vexpr e =
      if Ast.isom_exp from_exp e then (
        is_patched := true;
        ChangeTo to_exp)
      else DoChildren
  end

class replaceExpinStmt parent from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vstmt s =
      if phys_equal parent s then
        let vis = new replaceExpVisitor from_exp to_exp in
        let new_stmt = Cil.visitCilStmt vis s in
        if !is_patched then ChangeTo new_stmt
        else
          let from_exp =
            match from_exp with Cil.CastE (_, e) -> e | _ -> from_exp
          in
          let vis = new replaceExpVisitor from_exp to_exp in
          ChangeTo (Cil.visitCilStmt vis s)
      else DoChildren
  end

class updateExpVisitor target_func parent from_exp to_exp =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then
        let vis = new replaceExpinStmt parent from_exp to_exp in
        ChangeTo (Cil.visitCilFunction vis f)
      else SkipChildren
  end

class replaceStmt from_stmt to_stmt =
  object
    inherit Cil.nopCilVisitor

    method! vstmt s =
      if phys_equal s from_stmt then ChangeTo to_stmt else DoChildren
  end

class updateCallExpVisitor target_func from_stmt to_stmt =
  object
    inherit Cil.nopCilVisitor

    method! vfunc (f : Cil.fundec) =
      if String.equal f.svar.vname target_func then
        let vis = new replaceStmt from_stmt to_stmt in
        ChangeTo (Cil.visitCilFunction vis f)
      else SkipChildren
  end

let apply_insert_stmt ?(update = false) func_name snk_opt before after ss donee
    =
  if update then L.info "Applying UpdateGoToStmt..."
  else L.info "Applying InsertStmt...";
  is_patched := false;
  List.iter ~f:(fun s -> L.info "before:\n%s" (Ast.s_stmt s)) before;
  let very_before = List.last before in
  let very_after = List.hd after in
  if Option.is_none very_before && Option.is_none very_after then
    L.warn "apply_insert_stmt - cannot be patched";
  let ss' =
    List.fold_left
      ~f:(fun acc s -> fit_stmt_to_donee s func_name donee :: acc)
      ~init:[] ss
    |> List.rev
  in
  let vis =
    new insertStmtVisitor ~update func_name snk_opt very_before very_after ss'
  in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply InsertStmt"
  else L.info "Successfully applied InsertStmt at %s" func_name

let apply_update_stmt func_name s ss donee =
  L.info "Applying UpdateStmt...";
  is_patched := false;
  let ss' =
    List.fold_left
      ~f:(fun acc s -> fit_stmt_to_donee s func_name donee :: acc)
      ~init:[] ss
    |> List.rev
  in
  let vis = new updateStmtfromFuncVisitor func_name s ss' in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply UpdateStmt"
  else L.info "Successfully applied UpdateStmt at %s" func_name

let apply_delete_stmt func_name s donee =
  L.info "Applying DeleteStmt...";
  is_patched := false;
  let vis = new deleteStmtfromFuncVisitor func_name s in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply DeleteStmt"
  else L.info "Successfully applied DeleteStmt at %s" func_name

let apply_update_exp func_name s e1 e2 donee =
  L.info "Applying UpdateExp...";
  is_patched := false;
  let vis = new updateExpVisitor func_name s e1 e2 in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply UpdateExp"
  else L.info "Successfully applied UpdateExp at %s" func_name

let apply_update_callexp func_name s s2 donee =
  L.info "Applying UpdateCallExp...";
  is_patched := false;
  let vis = new updateCallExpVisitor func_name s s2 in
  Cil.visitCilFile vis donee;
  if not !is_patched then Logger.warn "failed to apply UpdateCallExp"
  else L.info "Successfully applied UpdateCalExp at %s" func_name

let apply_action donee snk_opt = function
  | D.InsertStmt (func_name, before, ss, after) ->
      apply_insert_stmt func_name snk_opt before after ss donee
  | D.DeleteStmt (func_name, s) -> apply_delete_stmt func_name s donee
  | D.UpdateStmt (func_name, _, s, ss, _) ->
      apply_update_stmt func_name s ss donee
  | D.UpdateGoToStmt (func_name, before, ss, after) ->
      apply_insert_stmt ~update:true func_name snk_opt before after ss donee
  | D.UpdateExp (func_name, s, e1, e2) ->
      apply_update_exp func_name s e1 e2 donee
  | D.UpdateCallExp (func_name, s, s2) ->
      apply_update_callexp func_name s s2 donee
  | _ -> failwith "apply_action - Not implemented"

let write_out path ast =
  let out_chan_orig = Core.Out_channel.create path in
  Cil.dumpFile Cil.defaultCilPrinter out_chan_orig path ast

let run donee diff snk_opt =
  Logger.info "%d actions to apply" (List.length diff);
  List.iter
    ~f:
      (is_patched := false;
       apply_action donee snk_opt)
    diff;
  donee
