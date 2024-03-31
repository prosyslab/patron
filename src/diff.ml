open Core
module H = Utils
module F = Format
module L = Logger

type action_type = Insertion | Deletion | Update
type parent_branch = NoBranch | TrueBranch | FalseBranch

type diff_env = {
  patch_depth : int;
  parent_branch : parent_branch list;
  prev_sibling : Ast.t;
}

let mk_diff_env patch_depth parent_branch prev_sibling =
  { patch_depth; parent_branch; prev_sibling }

let extract_func_name root_path =
  List.fold_left
    ~f:(fun acc n ->
      match n with
      | Ast.Fun f -> f :: acc
      | Ast.Global g -> (
          match g with Cil.GFun (f, _) -> f.svar.vname :: acc | _ -> acc)
      | _ -> acc)
    ~init:[] root_path
  |> fun out -> try List.hd_exn out with _ -> "None"

let get_env = snd
let get_diff = fst

type t =
  (* orig before globals * new globals * orig after globals *)
  | InsertGlobal of Cil.global list * Cil.global list * Cil.global list
  (* deleted globals *)
  | DeleteGlobal of Cil.global
  (* func name * orig before stmts * new stmts * orig after stmts *)
  | InsertStmt of string * Cil.stmt list * Cil.stmt list * Cil.stmt list
  (* func name * deleted stmts *)
  | DeleteStmt of string * Cil.stmt
  (* Only use update stmt when goto is deleted and new stmt is inserted *)
  (* func name * orig before stmts (until goto) * new stmts * orig after stmts *)
  | UpdateStmt of string * Cil.stmt list * Cil.stmt list * Cil.stmt list
  (* func name * target stmt (may be call exp) * orig before exps * new exps * orig after exps *)
  | InsertExp of string * Cil.stmt * Cil.exp list * Cil.exp list * Cil.exp list
  (* func name * target stmt * deleted exps *)
  | DeleteExp of string * Cil.stmt * Cil.exp
  (* func name * target stmt * orig exp * new exp *)
  | UpdateExp of string * Cil.stmt * Cil.exp * Cil.exp
  (* func name * target(orig) stmt * new stmt, but lval must be same *)
  | UpdateCallExp of string * Cil.stmt * Cil.stmt
  (* func name * target stmt (may be call instr) * new lval *)
  | InsertLval of string * Cil.stmt * Cil.lval
  (* func name * target stmt (may be call instr) * deleted lval *)
  | DeleteLval of string * Cil.stmt * Cil.lval
  (* func name * target stmt * orig lval * new lval *)
  | UpdateLval of string * Cil.stmt * Cil.lval * Cil.lval

let pp_env fmt env =
  F.fprintf fmt "Depth: %d\n" env.patch_depth;
  F.fprintf fmt "Previous Sibling Node: \n%s\n" (Ast.s_node env.prev_sibling)

let lst2strlines to_string =
  List.fold_left ~f:(fun s a -> s ^ "\n" ^ to_string a) ~init:""

let pp_diff ~simple fmt action =
  match action with
  | InsertGlobal (before, gs, after) ->
      F.fprintf fmt "\tInsertGlobal: \n";
      if simple then F.fprintf fmt "# of Before:%i\n" (List.length before)
      else F.fprintf fmt "Before:%s\n" (lst2strlines Ast.s_glob before);
      if simple then F.fprintf fmt "# of After:%i\n" (List.length after)
      else F.fprintf fmt "After:%s\n" (lst2strlines Ast.s_glob after);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Inserted:%s\n" (lst2strlines Ast.s_glob gs)
  | DeleteGlobal g ->
      F.fprintf fmt "\tDeletGlobal: \n";
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Deleted:%s\n" (Ast.s_glob g)
  | InsertStmt (func, before, ss, after) ->
      F.fprintf fmt "\tInsertStmt: \n";
      F.fprintf fmt "Function: %s\n" func;
      if simple then F.fprintf fmt "# of Before:%i\n" (List.length before)
      else F.fprintf fmt "Before:%s\n" (lst2strlines Ast.s_stmt before);
      if simple then F.fprintf fmt "# of After:%i\n" (List.length after)
      else F.fprintf fmt "After:%s\n" (lst2strlines Ast.s_stmt after);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Inserted:%s\n" (lst2strlines Ast.s_stmt ss)
  | DeleteStmt (func, s) ->
      F.fprintf fmt "\tDeleteStmt: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Deleted:%s\n" (Ast.s_stmt s)
  | UpdateStmt (func, before, ss, after) ->
      F.fprintf fmt "\tUpdateStmt: \n";
      F.fprintf fmt "Function: %s\n" func;
      if simple then F.fprintf fmt "# of Before:%i\n" (List.length before)
      else F.fprintf fmt "Before:%s\n" (lst2strlines Ast.s_stmt before);
      if simple then F.fprintf fmt "# of After:%i\n" (List.length after)
      else F.fprintf fmt "After:%s\n" (lst2strlines Ast.s_stmt after);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Inserted:%s\n" (lst2strlines Ast.s_stmt ss)
  | InsertExp (func, s, before, es, after) ->
      F.fprintf fmt "\tInsertExp: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Stmt:%s\n" (Ast.s_stmt s);
      if simple then F.fprintf fmt "# of Before:%i\n" (List.length before)
      else F.fprintf fmt "Before:%s\n" (lst2strlines Ast.s_exp before);
      if simple then F.fprintf fmt "# of After:%i\n" (List.length after)
      else F.fprintf fmt "After:%s\n" (lst2strlines Ast.s_exp after);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Inserted:%s\n" (lst2strlines Ast.s_exp es)
  | DeleteExp (func, s, e) ->
      F.fprintf fmt "\tDeleteExp: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Stmt:%s\n" (Ast.s_stmt s);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Deleted:%s\n" (Ast.s_exp e)
  | UpdateExp (func, s, e1, e2) ->
      F.fprintf fmt "\tUpdateExp: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Stmt:%s\n" (Ast.s_stmt s);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "From:\t%s\n" (Ast.s_exp e1);
      F.fprintf fmt "To:\t%s\n" (Ast.s_exp e2)
  | UpdateCallExp (func, s1, s2) ->
      F.fprintf fmt "\tUpdateCallExp: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "From:%s\n" (Ast.s_stmt s1);
      F.fprintf fmt "To:\t%s\n" (Ast.s_stmt s2)
  | InsertLval (func, s, lv) ->
      F.fprintf fmt "\tInsertLval: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Stmt:%s\n" (Ast.s_stmt s);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Inserted: \n%s" (Ast.s_lv lv)
  | DeleteLval (func, s, lv) ->
      F.fprintf fmt "\tDeletLval: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Stmt:%s\n" (Ast.s_stmt s);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "Inserted: \n%s" (Ast.s_lv lv)
  | UpdateLval (func, s, l1, l2) ->
      F.fprintf fmt "\tUpdateLval: \n";
      F.fprintf fmt "Function: %s\n" func;
      F.fprintf fmt "Stmt:%s\n" (Ast.s_stmt s);
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "From:\t%s\n" (Ast.s_lv l1);
      F.fprintf fmt "To:\t%s\n" (Ast.s_lv l2)

let pp_edit_script fmt es =
  F.fprintf fmt "Edit Script Summary:\n";
  F.fprintf fmt "Size: %d\n" (List.length es);
  List.iteri
    ~f:(fun i x ->
      let diff, env = x in
      F.fprintf fmt "============diff-%d============\n" i;
      F.fprintf fmt "Meta Data:\n%a\n\n" pp_env env;
      F.fprintf fmt "\n%a\n" (pp_diff ~simple:true) diff;
      F.fprintf fmt "================================\n")
    es

let mk_diff_exp code func_name parent depth left_sibs right_sibs exp_lst =
  let prev_node = List.last left_sibs |> Ast.of_exp in
  let env = mk_diff_env depth [] prev_node in
  match code with
  | Insertion ->
      [ (InsertExp (func_name, parent, left_sibs, exp_lst, right_sibs), env) ]
  | Deletion ->
      List.map ~f:(fun e -> (DeleteExp (func_name, parent, e), env)) exp_lst
  | _ -> L.error "mk_diff_exp - unexpected code"

let is_update_stmt diffs =
  if List.length diffs < 2 then false
  else
    match diffs with
    | [ (DeleteStmt _, _); (InsertStmt _, _) ] -> true
    | _ -> false

let is_update_glob diffs =
  if List.length diffs < 2 then false
  else
    match diffs with
    | [ (DeleteGlobal _, _); (InsertGlobal _, _) ] -> true
    | _ -> false

let rec find_continue_point_exp exp1 param =
  match param with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_exp hd exp1 then tl else find_continue_point_exp exp1 tl

let rec find_eq_exp_in_tl depth exp1 expl acc =
  match expl with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_exp hd exp1 then hd :: acc
      else
        let result = find_eq_exp_in_tl depth exp1 tl [ hd ] in
        if List.is_empty result then [] else result @ acc

let compute_right_siblings_exp diffs rest =
  match List.hd diffs with
  | Some next -> next :: find_continue_point_exp next rest
  | None -> []

let get_followup_diff_exp code func_name parent depth exp1 exp2 expl1 expl2
    left_sibs =
  let prev_node = List.last left_sibs |> Ast.of_exp in
  match code with
  | Update ->
      let env = mk_diff_env depth [] prev_node in
      [ (UpdateExp (func_name, parent, exp1, exp2), env) ]
  | _ ->
      let inserted_exps = find_eq_exp_in_tl depth exp1 expl2 [] in
      if List.is_empty inserted_exps then
        let deleted_exps = find_eq_exp_in_tl depth exp2 expl1 [] in
        if List.is_empty deleted_exps then
          let env = mk_diff_env depth [] prev_node in
          [ (UpdateExp (func_name, parent, exp1, exp2), env) ]
        else
          let deleted_exps = exp1 :: List.tl_exn deleted_exps in
          let right_sibs = compute_right_siblings_exp deleted_exps expl1 in
          mk_diff_exp Deletion func_name parent depth left_sibs right_sibs
            deleted_exps
      else
        let inserted_exps = exp2 :: List.tl_exn inserted_exps in
        let right_siblings = compute_right_siblings_exp expl1 inserted_exps in
        mk_diff_exp Insertion func_name parent depth left_sibs right_siblings
          inserted_exps

let rec fold_continue_point_param func_name parent depth h1 h2 tl1 tl2 es acc =
  match es with
  | [] -> L.error "fold_continue_point_param - unexpected empty list"
  | (hd, env) :: _ -> (
      match hd with
      | InsertExp _ ->
          if env.patch_depth = depth then
            let continue_point = find_continue_point_exp h1 tl2 in
            fold_param2 func_name parent depth tl1 continue_point acc
          else []
      | DeleteExp _ ->
          if env.patch_depth = depth then
            let continue_point = find_continue_point_exp h2 tl1 in
            fold_param2 func_name parent depth continue_point tl2 acc
          else []
      | _ -> fold_param2 func_name parent depth tl1 tl2 acc)

and get_diff_param func_name parent depth exp1 exp2 expl1 expl2 left_siblings =
  if Ast.eq_exp exp1 exp2 then []
  else
    get_followup_diff_exp Insertion func_name parent depth exp1 exp2 expl1 expl2
      left_siblings

and fold_param2 func_name parent depth el1 el2 left_sibs =
  let prev_node = List.last left_sibs |> Ast.of_exp in
  match (el1, el2) with
  | [], [] -> []
  | hd1 :: tl1, hd2 :: tl2 ->
      let es =
        get_diff_param func_name parent depth hd1 hd2 tl1 tl2 left_sibs
      in
      let updated_left_sibs = List.rev left_sibs |> List.cons hd1 |> List.rev in
      if List.is_empty es then
        fold_param2 func_name parent depth tl1 tl2 updated_left_sibs
      else
        es
        @ fold_continue_point_param func_name parent depth hd1 hd2 tl1 tl2 es
            left_sibs
  | [], lst ->
      let env = mk_diff_env depth [] prev_node in
      [ (InsertExp (func_name, parent, left_sibs, lst, []), env) ]
  | lst, [] ->
      let env = mk_diff_env depth [] prev_node in
      List.map ~f:(fun e -> (DeleteExp (func_name, parent, e), env)) lst

let extract_call func_name parent depth s1 lv1 f1 el1 s2 lv2 f2 el2 =
  let env = mk_diff_env depth [] Ast.NotApplicable in
  let lval_diff =
    match (lv1, lv2) with
    | None, Some lv -> [ (InsertLval (func_name, parent, lv), env) ]
    | Some lv, None -> [ (DeleteLval (func_name, parent, lv), env) ]
    | Some l1, Some l2 ->
        if Ast.eq_lval l1 l2 then []
        else [ (UpdateLval (func_name, parent, l1, l2), env) ]
    | _ -> []
  in
  if Ast.isom_exp f1 f2 then
    let param_diff = fold_param2 func_name parent 0 el1 el2 [] in
    lval_diff @ param_diff
  else if List.is_empty lval_diff then
    [ (UpdateCallExp (func_name, s1, s2), env) ]
  else [ (* NOTE: may be handled as DeleteStmt; InsertStmt *) ]

let extract_exp func_name parent env e1 e2 =
  let diffs = Ast.diff_exp e1 e2 in
  List.map ~f:(fun (a, b) -> (UpdateExp (func_name, parent, a, b), env)) diffs

let extract_set func_name parent depth lv1 e1 lv2 e2 =
  let env = mk_diff_env depth [] Ast.NotApplicable in
  let lval_diff =
    if Ast.eq_lval lv1 lv2 then []
    else [ (UpdateLval (func_name, parent, lv1, lv2), env) ]
  in
  let exp_diff = extract_exp func_name parent env e1 e2 in
  lval_diff @ exp_diff

(* This is where stmt/instr ends *)

let extract_instr func_name parent depth stmt1 instr1 stmt2 instr2 =
  match (instr1, instr2) with
  | Cil.Set (lv1, e1, _), Cil.Set (lv2, e2, _) ->
      extract_set func_name parent depth lv1 e1 lv2 e2
  | Cil.Call (lv1, f1, el1, _), Cil.Call (lv2, f2, el2, _) ->
      extract_call func_name parent depth stmt1 lv1 f1 el1 stmt2 lv2 f2 el2
  | _ -> []

let rec find_continue_point_stmt stmt1 stmts =
  match stmts with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_stmt stmt1.Cil.skind hd.Cil.skind then stmts
      else find_continue_point_stmt stmt1 tl

let rec find_eq_stmt_in_tl depth stmt1 stmts acc =
  match stmts with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_stmt stmt1.Cil.skind hd.Cil.skind then hd :: acc |> List.rev
      else find_eq_stmt_in_tl depth stmt1 tl (hd :: acc)

let rec mk_diff_stmt code func_name prnt_brnch depth before after stmt_lst =
  let prev_node = List.last before |> Ast.of_stmt in
  let env = mk_diff_env depth prnt_brnch prev_node in
  match code with
  | Insertion -> [ (InsertStmt (func_name, before, stmt_lst, after), env) ]
  | Deletion ->
      List.map ~f:(fun stmt -> (DeleteStmt (func_name, stmt), env)) stmt_lst
  | _ -> L.error "mk_diff_stmt - unexpected code"

and fold_continue_point_stmt func_name prnt_brnch depth h1 h2 tl1 tl2 before =
  function
  | InsertStmt _, env ->
      if env.patch_depth = depth then
        let continue_point = find_continue_point_stmt h1 tl2 in
        fold_stmts2 func_name prnt_brnch depth (h1 :: tl1) continue_point before
      else []
  | DeleteStmt _, env ->
      if env.patch_depth = depth then
        let continue_point = find_continue_point_stmt h2 tl1 in
        fold_stmts2 func_name prnt_brnch depth continue_point (h2 :: tl2) before
      else []
  | _ -> fold_stmts2 func_name prnt_brnch depth tl1 tl2 before

and compute_right_siblings_stmt diffs rest =
  List.slice rest (List.length diffs - 1) (List.length rest)

and get_followup_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before =
  let prev_node = List.last before |> Ast.of_stmt in
  let inserted_stmts = find_eq_stmt_in_tl depth hd1 tl2 [] in
  if List.is_empty inserted_stmts then
    let deleted_stmts = find_eq_stmt_in_tl depth hd2 tl1 [] in
    if List.is_empty deleted_stmts then
      let env = mk_diff_env depth prnt_brnch prev_node in
      if Ast.is_cil_goto hd1.skind then
        [ (UpdateStmt (func_name, before, [ hd2 ], tl1), env) ]
      else
        [
          (DeleteStmt (func_name, hd1), env);
          (InsertStmt (func_name, before, [ hd2 ], tl1), env);
        ]
    else
      let deleted_stmts = hd1 :: List.drop_last_exn deleted_stmts in
      let right_siblings = compute_right_siblings_stmt deleted_stmts tl1 in
      mk_diff_stmt Deletion func_name prnt_brnch depth before right_siblings
        deleted_stmts
  else
    let inserted_stmts = hd2 :: List.drop_last_exn inserted_stmts in
    let after = hd1 :: tl1 in
    mk_diff_stmt Insertion func_name prnt_brnch depth before after
      inserted_stmts

and compute_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before =
  match (hd1.Cil.skind, hd2.Cil.skind) with
  | Cil.Instr i1, Cil.Instr i2 ->
      if Ast.eq_instr i1 i2 then
        let instr1, instr2 = (List.hd_exn i1, List.hd_exn i2) in
        extract_instr func_name hd1 depth hd1 instr1 hd2 instr2
      else
        get_followup_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before
  | Cil.If (c1, t_blck1, eblck1, _), Cil.If (c2, t_blck2, eblck2, _) ->
      let exp_diff =
        if Ast.eq_exp c1 c2 then []
        else get_followup_diff_exp Update func_name hd1 0 c1 c2 [] [] []
      in
      if Ast.eq_stmt hd1.Cil.skind hd2.Cil.skind then
        exp_diff
        @ extract_block func_name (TrueBranch :: prnt_brnch) (depth + 1) t_blck1
            t_blck2 before
        @ extract_block func_name
            (FalseBranch :: prnt_brnch)
            (depth + 1) eblck1 eblck2 before
      else
        get_followup_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before
  | Cil.Loop (blk1, _, _, _), Cil.Loop (blk2, _, _, _) ->
      if Ast.eq_stmt hd1.Cil.skind hd2.Cil.skind then
        extract_block func_name prnt_brnch (depth + 1) blk1 blk2 before
      else
        get_followup_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before
  | Cil.Return (Some e1, _), Cil.Return (Some e2, _) ->
      if Ast.eq_stmt hd1.skind hd2.skind then []
      else get_followup_diff_exp Update func_name hd1 0 e1 e2 [] [] []
  | Cil.Return (None, _), Cil.Return (None, _) -> []
  | Cil.Block b1, Cil.Block b2 ->
      if Ast.eq_stmt hd1.Cil.skind hd2.Cil.skind then
        extract_block func_name prnt_brnch (depth + 1) b1 b2 before
      else
        get_followup_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before
  | Cil.Goto (dest1, _), Cil.Goto (dest2, _) ->
      if Ast.eq_stmt !dest1.Cil.skind !dest2.Cil.skind then []
      else
        get_followup_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before
  | Cil.TryExcept _, Cil.TryExcept _ | Cil.TryFinally _, Cil.TryFinally _ -> []
  | _ ->
      get_followup_diff_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2 before

and decide_next_step_stmt func_name prnt_brnch depth diff hd1 hd2 tl1 tl2
    new_before before =
  match diff with
  | [] -> fold_stmts2 func_name prnt_brnch depth tl1 tl2 new_before
  | (InsertStmt _, _) :: (DeleteStmt _, _) :: _ ->
      diff @ fold_stmts2 func_name prnt_brnch depth tl1 tl2 before
  | _ ->
      let continue_diff =
        List.last_exn diff
        |> fold_continue_point_stmt func_name prnt_brnch depth hd1 hd2 tl1 tl2
             before
      in
      diff @ continue_diff

and fold_stmts2 func_name prnt_brnch depth stmts1 stmts2 before =
  let prev_node = List.last before |> Ast.of_stmt in
  match (stmts1, stmts2) with
  | [], [] -> []
  | s1 :: ss1, s2 :: ss2 ->
      let updated_before = List.rev before |> List.cons s1 |> List.rev in
      let es =
        compute_diff_stmt func_name prnt_brnch depth s1 s2 ss1 ss2 before
      in
      if is_update_stmt es then
        es @ fold_stmts2 func_name prnt_brnch depth ss1 ss2 updated_before
      else
        decide_next_step_stmt func_name prnt_brnch depth es s1 s2 ss1 ss2
          updated_before before
  | [], lst ->
      let env = mk_diff_env depth prnt_brnch prev_node in
      [ (InsertStmt (func_name, before, lst, []), env) ]
  | lst, [] ->
      let env = mk_diff_env depth prnt_brnch prev_node in
      List.map ~f:(fun stmt -> (DeleteStmt (func_name, stmt), env)) lst

and extract_block func_name prnt_brnch depth block1 block2 before =
  let remove_empty_instrs stmts =
    List.fold_left
      ~f:(fun acc x -> if Ast.is_empty_instr x then acc else x :: acc)
      ~init:[] stmts
    |> List.rev
  in
  let stmts1 = remove_empty_instrs block1.Cil.bstmts in
  let stmts2 = remove_empty_instrs block2.Cil.bstmts in
  fold_stmts2 func_name prnt_brnch depth stmts1 stmts2 before

let process_cil_glob_list lst =
  List.fold_left ~f:(fun acc glob -> Ast.Global glob :: acc) ~init:[] lst
  |> List.rev

let rec find_eq_glob_in_tl glob1 globals acc =
  match globals with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_global glob1 hd then hd :: acc |> List.rev
      else find_eq_glob_in_tl glob1 tl (hd :: acc)

let rec find_continue_point_glob glob1 globals =
  match globals with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_global glob1 hd then globals
      else find_continue_point_glob glob1 tl

let rec mk_diff_glob code depth acc_left acc_right glob_lst =
  let prev_node = List.last acc_left |> Ast.of_glob in
  let env = mk_diff_env depth [] prev_node in
  match code with
  | Insertion -> [ (InsertGlobal (acc_left, glob_lst, acc_right), env) ]
  | Deletion -> List.map ~f:(fun glob -> (DeleteGlobal glob, env)) glob_lst
  | _ -> L.error "mk_diff_glob - unexpected code"

and fold_continue_point_glob depth glob1 glob2 es tl1 tl2 =
  match es with
  | [] -> L.error "fold_continue_point_glob - unexpected empty list"
  | (hd, _) :: _ -> (
      match hd with
      | InsertGlobal _ ->
          let continue_point = find_continue_point_glob glob1 tl2 in
          fold_globals2 depth (glob1 :: tl1) continue_point
      | DeleteGlobal _ ->
          let continue_point = find_continue_point_glob glob2 tl1 in
          fold_globals2 depth continue_point (glob2 :: tl2)
      | _ -> fold_globals2 depth tl1 tl2)

and compute_right_siblings_glob diffs rest =
  List.slice rest (List.length diffs - 1) (List.length rest)

and get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sibs =
  let prev_node = List.last left_sibs |> Ast.of_glob in
  let inserted_globs = find_eq_glob_in_tl glob1 tl2 [] in
  if List.is_empty inserted_globs then
    let deleted_globs = find_eq_glob_in_tl glob2 tl1 [] in
    if List.is_empty deleted_globs then
      let env = mk_diff_env depth [] prev_node in
      [
        (DeleteGlobal glob1, env);
        (InsertGlobal (left_sibs, [ glob2 ], tl1), env);
      ]
    else
      let deleted_globs = glob1 :: List.drop_last_exn deleted_globs in
      let right_siblings = compute_right_siblings_glob deleted_globs tl1 in
      mk_diff_glob Deletion depth left_sibs right_siblings deleted_globs
  else
    let inserted_globs = glob2 :: List.drop_last_exn inserted_globs in
    let right_siblings = compute_right_siblings_glob inserted_globs tl2 in
    mk_diff_glob Insertion depth left_sibs right_siblings inserted_globs

and compute_diff_glob depth glob1 glob2 tl1 tl2 left_sbis =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      if Ast.eq_global glob1 glob2 then
        let depth = depth + 1 in
        extract_block func_info1.svar.vname [] depth func_info1.sbody
          func_info2.sbody []
      else get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sbis
  | Cil.GVarDecl _, Cil.GVarDecl _ ->
      if Ast.eq_global glob1 glob2 then []
      else get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sbis
  | Cil.GType _, Cil.GType _ ->
      if Ast.eq_global glob1 glob2 then []
      else get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sbis
  | Cil.GCompTag _, Cil.GCompTag _
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _
  | Cil.GEnumTag _, Cil.GEnumTag _
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _
  | Cil.GVar _, Cil.GVar _
  | Cil.GAsm _, Cil.GAsm _
  | Cil.GPragma _, Cil.GPragma _
  | Cil.GText _, Cil.GText _ ->
      []
  | _ -> get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sbis

and decide_next_step_glob depth diff hd1 hd2 tl1 tl2 new_l_sibs l_sibs =
  match diff with
  | [] -> fold_globals2 depth tl1 tl2 new_l_sibs
  | (h, _) :: t ->
      if List.length t <> 0 then
        match (h, List.hd_exn t |> get_diff) with
        | InsertGlobal _, DeleteGlobal _ ->
            diff @ fold_globals2 depth tl1 tl2 l_sibs
        | _ -> diff @ fold_continue_point_glob depth hd1 hd2 diff tl1 tl2 l_sibs
      else diff @ fold_continue_point_glob depth hd1 hd2 diff tl1 tl2 l_sibs

and fold_globals2 depth donor_gobals patch_globals left_sibs =
  let prev_node = List.last left_sibs |> Ast.of_glob in
  match (donor_gobals, patch_globals) with
  | [], [] -> []
  | hd1 :: tl1, hd2 :: tl2 ->
      let updated_left_sibs = List.rev left_sibs |> List.cons hd1 |> List.rev in
      let diff = compute_diff_glob depth hd1 hd2 tl1 tl2 left_sibs in
      if is_update_glob diff then
        diff @ fold_globals2 depth tl1 tl2 updated_left_sibs
      else
        decide_next_step_glob depth diff hd1 hd2 tl1 tl2 updated_left_sibs
          left_sibs
  | [], lst ->
      let env = mk_diff_env depth [] prev_node in
      [ (InsertGlobal (left_sibs, lst, []), env) ]
  | lst, [] ->
      let env = mk_diff_env depth [] prev_node in
      List.map ~f:(fun glob -> (DeleteGlobal glob, env)) lst

let compare = compare

let define_diff out_dir buggy_file patch_file =
  let globs1, globs2 =
    ( H.remove_comments buggy_file.Cil.globals,
      H.remove_comments patch_file.Cil.globals )
  in
  let diff = fold_globals2 0 globs1 globs2 [] in
  let oc = Out_channel.create (Filename.concat out_dir "diff.txt") in
  let fmt = F.formatter_of_out_channel oc in
  pp_edit_script fmt diff;
  F.pp_print_flush fmt ();
  Out_channel.close oc;
  diff
