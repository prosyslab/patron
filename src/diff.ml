open Core
module H = Utils
module F = Format

(* for the readability reference *)
let beginning_idx = 0

type action_type = Insertion | Deletion | Update
type parent_branch = NoBranch | TrueBranch | FalseBranch

type diff_env = {
  patch_depth : int;
  parent_branch : parent_branch list;
  prev_sibling : Ast.t;
}

type context = {
  root_path : Ast.path;
  patch_bound : Ast.path * Ast.path;
  sibling_idx : int;
  top_func_name : string;
}

let mk_context root_path before after sibling_idx top_func_name =
  { root_path; patch_bound = (before, after); sibling_idx; top_func_name }

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
  | InsertGlobal of context * Cil.global
  | DeleteGlobal of context * Cil.global
  | InsertStmt of context * Cil.stmt
  | DeleteStmt of context * Cil.stmt
  | InsertExp of context * Cil.exp
  | DeleteExp of context * Cil.exp
  | UpdateExp of context * Cil.exp * Cil.exp
  | InsertLval of context * Cil.lval
  | DeleteLval of context * Cil.lval
  | UpdateLval of context * Cil.lval * Cil.lval

let get_ctx diff =
  match diff with
  | InsertGlobal (ctx, _)
  | DeleteGlobal (ctx, _)
  | InsertStmt (ctx, _)
  | DeleteStmt (ctx, _)
  | InsertExp (ctx, _)
  | DeleteExp (ctx, _)
  | UpdateExp (ctx, _, _)
  | InsertLval (ctx, _)
  | DeleteLval (ctx, _)
  | UpdateLval (ctx, _, _) ->
      ctx

let pp_env fmt env =
  F.fprintf fmt "Depth: %d\n" env.patch_depth;
  F.fprintf fmt "Previous Sibling Node: \n%s\n" (Ast.s_node env.prev_sibling)

let pp_ctx fmt ctx =
  F.fprintf fmt "Context Summary:\n";
  F.fprintf fmt "Parent Function: %s\n" ctx.top_func_name;
  F.fprintf fmt "parents(bottom_up) -> \n";
  F.fprintf fmt "%a\n" Ast.pp_path ctx.root_path;
  F.fprintf fmt "-----------------------------------------\n";
  let before, after = ctx.patch_bound in
  F.fprintf fmt "Before: %a\n" Ast.pp_path before;
  F.fprintf fmt "-----------------------------------------\n";
  F.fprintf fmt "After: %a\n" Ast.pp_path after;
  F.fprintf fmt "-----------------------------------------\n"

let pp_diff fmt action =
  match action with
  | InsertGlobal (ctx, g2) ->
      F.fprintf fmt "\tInsertGlobal: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "%s\n" (Ast.s_glob g2)
  | DeleteGlobal (ctx, g2) ->
      F.fprintf fmt "\tDeletGlobal: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "%s\n" (Ast.s_glob g2)
  | InsertStmt (ctx, s1) ->
      F.fprintf fmt "\tInsertStmt: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "%s\n" (Ast.s_stmt s1)
  | DeleteStmt (ctx, s1) ->
      F.fprintf fmt "\tDeletStmt: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "%s\n" (Ast.s_stmt s1)
  | InsertExp (ctx, e1) ->
      F.fprintf fmt "\tInsertExp: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "%s\n" (Ast.s_exp e1)
  | DeleteExp (ctx, e1) ->
      F.fprintf fmt "\tDeleteExp: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "%s\n" (Ast.s_exp e1)
  | UpdateExp (ctx, e1, e2) ->
      F.fprintf fmt "\tUpdateExp: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "From:\t%s\n" (Ast.s_exp e1);
      F.fprintf fmt "To:\t%s\n" (Ast.s_exp e2)
  | InsertLval (ctx, l1) ->
      F.fprintf fmt "\t%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "InsertLval: %s" (Ast.s_lv l1)
  | DeleteLval (ctx, l1) ->
      F.fprintf fmt "\t%a\n" pp_ctx ctx;
      F.fprintf fmt "Diff Summary:\n";
      F.fprintf fmt "DeleteLval: \n%s" (Ast.s_lv l1)
  | UpdateLval (ctx, l1, l2) ->
      F.fprintf fmt "\tUpdateLval: \n";
      F.fprintf fmt "%a\n" pp_ctx ctx;
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
      F.fprintf fmt "\n%a\n" pp_diff diff;
      F.fprintf fmt "================================\n")
    es

let process_cil_exp_list lst =
  List.fold_left ~f:(fun acc exp -> Ast.Exp exp :: acc) ~init:[] lst |> List.rev

let rec find_direct_parent root_path =
  match root_path with
  | [] -> failwith "search_parent_sibs_of_exp: failed to find exp's parent"
  | hd :: tl -> (
      match hd with
      | Ast.Stmt _ | Ast.Global _ | Ast.Fun _ -> hd
      | _ -> find_direct_parent tl)

let find_first_block_parent root_path =
  let rec aux = function
    | Ast.Stmt s -> (
        match s.Cil.skind with
        | Block _ | Loop _ | If _ -> s
        | _ ->
            (try List.tl_exn root_path
             with _ ->
               failwith "find_first_block_parent: block parent does not exist")
            |> find_direct_parent |> aux)
    | _ -> failwith "find_first_block_parent: block parent does not exist"
  in
  find_direct_parent root_path |> aux

let search_parent_sibs_fun parent_stmt func =
  let rec aux parent_stmt stmt_lst acc =
    match stmt_lst with
    | [] -> ([], [])
    | hd :: tl ->
        if Ast.eq_stmt parent_stmt.Cil.skind hd.Cil.skind then (List.rev acc, tl)
        else aux parent_stmt tl (hd :: acc)
  in
  let ast = Ast.get_buggy_ast () in
  Utils.extract_target_func_stmt_lst ast func |> fun stmt_lst ->
  aux parent_stmt stmt_lst []

let search_parent_sibs_glob parent_stmt glob =
  let rec aux parent_stmt stmt_lst acc =
    match stmt_lst with
    | [] -> ([], [])
    | hd :: tl ->
        if Ast.eq_stmt parent_stmt.Cil.skind hd.Cil.skind then (List.rev acc, tl)
        else aux parent_stmt tl (hd :: acc)
  in
  match glob with
  | Cil.GFun (f, _) -> aux parent_stmt f.Cil.sbody.Cil.bstmts []
  | _ -> failwith "search_parent_sibs_glob: unexpected global type"

let search_parent_sibs_stmt parent_stmt stmt =
  let rec aux parent_stmt stmt_lst acc =
    match stmt_lst with
    | [] -> ([], [])
    | hd :: tl ->
        if Ast.eq_stmt parent_stmt.Cil.skind hd.Cil.skind then (List.rev acc, tl)
        else aux parent_stmt tl (hd :: acc)
  in
  match stmt.Cil.skind with
  | Loop (blk, _, _, _) | Block blk -> aux parent_stmt blk.Cil.bstmts []
  | If (_, t_blk, e_blk, _) ->
      let tb_out = aux parent_stmt t_blk.Cil.bstmts [] in
      if fst tb_out |> List.is_empty && snd tb_out |> List.is_empty then
        aux parent_stmt e_blk.Cil.bstmts []
      else tb_out
  | _ -> failwith "search_parent_sibs_stmt: unexpected stmt type"

let search_parent_sibs_of_exp root_path =
  let parent = find_direct_parent root_path in
  if Ast.is_glob parent || Ast.is_fun parent then
    failwith "search_parent_sibs_of_exp: unexpected parent type"
  else
    let parent_stmt = Ast.ast2stmt parent in
    let grand_parent = find_direct_parent (List.tl_exn root_path) in
    match grand_parent with
    | Ast.Stmt s -> search_parent_sibs_stmt parent_stmt s
    | Ast.Global g -> search_parent_sibs_glob parent_stmt g
    | Ast.Fun f -> search_parent_sibs_fun parent_stmt f
    | _ -> failwith "search_parent_sibs_of_exp: unexpected grand parent type"

let rec mk_diff_exp code parent depth exp_lst left_sibs right_sibs =
  match exp_lst with
  | [] -> []
  | hd :: tl -> (
      let prev_node = List.hd left_sibs |> Ast.exp2ast in
      let func = extract_func_name parent in
      let env = mk_diff_env depth [] prev_node in
      let l_sibs, r_sibs = search_parent_sibs_of_exp parent in
      let context =
        mk_context parent (Ast.stmts2path l_sibs) (Ast.stmts2path r_sibs)
          (List.length l_sibs) func
      in
      match code with
      | Insertion ->
          (InsertExp (context, hd), env)
          :: mk_diff_exp code parent depth tl left_sibs right_sibs
      | Deletion ->
          (DeleteExp (context, hd), env)
          :: mk_diff_exp code parent depth tl left_sibs right_sibs
      | _ -> failwith "mk_diff_exp: unexpected code")

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

let get_followup_diff_exp code parent depth exp1 exp2 expl1 expl2 left_sibs =
  let prev_node = List.hd left_sibs |> Ast.exp2ast in
  (* let right_sibs = compute_right_siblings_exp expl1 expl2 in *)
  match code with
  | Update ->
      let func = extract_func_name parent in
      let env = mk_diff_env depth [] prev_node in
      let l_sibs, r_sibs = search_parent_sibs_of_exp parent in
      let ctx =
        mk_context parent (Ast.stmts2path l_sibs) (Ast.stmts2path r_sibs)
          (List.length l_sibs) func
      in
      [ (UpdateExp (ctx, exp1, exp2), env) ]
  | _ ->
      let inserted_exps = find_eq_exp_in_tl depth exp1 expl2 [] in
      if List.is_empty inserted_exps then
        let deleted_exps = find_eq_exp_in_tl depth exp2 expl1 [] in
        if List.is_empty deleted_exps then
          let func = extract_func_name parent in
          let env = mk_diff_env depth [] prev_node in
          let l_sibs, r_sibs = search_parent_sibs_of_exp parent in
          let ctx =
            mk_context parent (Ast.stmts2path l_sibs) (Ast.stmts2path r_sibs)
              (List.length l_sibs) func
          in
          [ (UpdateExp (ctx, exp1, exp2), env) ]
        else
          let deletion = exp1 :: List.tl_exn deleted_exps in
          let right_sibs = compute_right_siblings_exp deleted_exps expl1 in
          mk_diff_exp Deletion parent depth deletion left_sibs right_sibs
      else
        let insertion = exp2 :: List.tl_exn inserted_exps in
        let right_siblings = compute_right_siblings_exp expl1 inserted_exps in
        mk_diff_exp Insertion parent depth insertion left_sibs right_siblings

let rec fold_continue_point_param parent depth h1 h2 tl1 tl2 es acc =
  match es with
  | [] -> failwith "fold_continue_point_stmt: unexpected empty list"
  | (hd, env) :: _ -> (
      match hd with
      | InsertExp _ ->
          if env.patch_depth = depth then
            let continue_point = find_continue_point_exp h1 tl2 in
            fold_param2 parent depth tl1 continue_point acc
          else []
      | DeleteExp _ ->
          if env.patch_depth = depth then
            let continue_point = find_continue_point_exp h2 tl1 in
            fold_param2 parent depth continue_point tl2 acc
          else []
      | _ -> fold_param2 parent depth tl1 tl2 acc)

and get_diff_param parent depth exp1 exp2 expl1 expl2 left_siblings =
  if Ast.eq_exp exp1 exp2 then []
  else
    get_followup_diff_exp Insertion parent depth exp1 exp2 expl1 expl2
      left_siblings

and fold_param2 parent depth el1 el2 left_sibs =
  let prev_node = List.hd left_sibs |> Ast.exp2ast in
  let func = extract_func_name parent in
  match (el1, el2) with
  | [], [] -> []
  | hd1 :: tl1, hd2 :: tl2 ->
      let es = get_diff_param parent depth hd1 hd2 tl1 tl2 left_sibs in
      let updated_left_sibs = hd1 :: left_sibs in
      if List.is_empty es then
        es @ fold_param2 parent depth tl1 tl2 updated_left_sibs
      else
        es @ fold_continue_point_param parent depth hd1 hd2 tl1 tl2 es left_sibs
  | [], hd :: tl ->
      let env = mk_diff_env depth [] prev_node in
      let context =
        mk_context parent (Ast.exps2path left_sibs) [] (List.length left_sibs)
          func
      in
      (InsertExp (context, hd), env) :: fold_param2 parent depth [] tl left_sibs
  | hd :: tl, [] ->
      let env = mk_diff_env depth [] prev_node in
      let context =
        mk_context parent (Ast.exps2path left_sibs) (Ast.exps2path tl)
          (List.length left_sibs) func
      in
      (DeleteExp (context, hd), env) :: fold_param2 parent depth tl [] left_sibs

let extract_call parent depth lv1 e1 el1 lv2 e2 el2 =
  let func = extract_func_name parent in
  let env = mk_diff_env depth [] Ast.NotApplicable in
  let l_sibs, r_sibs = search_parent_sibs_of_exp parent in
  let ctx =
    mk_context parent (Ast.stmts2path l_sibs) (Ast.stmts2path r_sibs)
      (List.length l_sibs) func
  in
  let lval_diff =
    match (lv1, lv2) with
    | None, Some lv -> [ (InsertLval (ctx, lv), env) ]
    | Some lv, None -> [ (DeleteLval (ctx, lv), env) ]
    | Some l1, Some l2 ->
        if Ast.eq_lval l1 l2 then [] else [ (UpdateLval (ctx, l1, l2), env) ]
    | _ -> []
  in
  let exp_diff =
    if Ast.isom_exp e1 e2 then [] else [ (UpdateExp (ctx, e1, e2), env) ]
  in
  let param_diff = fold_param2 parent 0 el1 el2 [] in
  lval_diff @ exp_diff @ param_diff

let extract_set parent depth lv1 e1 lv2 e2 =
  let func = extract_func_name parent in
  let env = mk_diff_env depth [] Ast.NotApplicable in
  let l_sibs, r_sibs = search_parent_sibs_of_exp parent in
  let ctx =
    mk_context parent (Ast.stmts2path l_sibs) (Ast.stmts2path r_sibs)
      (List.length l_sibs) func
  in
  let lval_diff =
    if Ast.eq_lval lv1 lv2 then [] else [ (UpdateLval (ctx, lv1, lv2), env) ]
  in
  let exp_diff =
    if Ast.eq_exp e1 e2 then [] else [ (UpdateExp (ctx, e1, e2), env) ]
  in
  lval_diff @ exp_diff

(* This is where stmt/instr ends *)

let extract_instr parent depth instr1 instr2 =
  match (instr1, instr2) with
  | Cil.Set (lv1, e1, _), Cil.Set (lv2, e2, _) ->
      extract_set parent depth lv1 e1 lv2 e2
  | Cil.Call (lv1, e1, el1, _), Cil.Call (lv2, e2, el2, _) ->
      extract_call parent depth lv1 e1 el1 lv2 e2 el2
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
      if Ast.eq_stmt stmt1.Cil.skind hd.Cil.skind then hd :: acc
      else find_eq_stmt_in_tl depth stmt1 tl (hd :: acc)

let rec mk_diff_stmt code parent prnt_brnch depth stmt_lst acc_left acc_right =
  let prev_node = List.hd acc_left |> Ast.stmt2ast in
  match stmt_lst with
  | [] -> []
  | hd :: tl -> (
      let func = extract_func_name parent in
      let env = mk_diff_env depth prnt_brnch prev_node in
      let ctx =
        mk_context parent (Ast.stmts2path acc_left) (Ast.stmts2path acc_right)
          (List.length acc_left) func
      in
      let rest_diff =
        mk_diff_stmt code parent prnt_brnch depth tl acc_left acc_right
      in
      match code with
      | Insertion -> (InsertStmt (ctx, hd), env) :: rest_diff
      | Deletion -> (DeleteStmt (ctx, hd), env) :: rest_diff
      | _ -> failwith "mk_diff_stmt: unexpected code")

and fold_continue_point_stmt parent prnt_brnch depth h1 h2 tl1 tl2 es acc =
  match List.rev es with
  | [] -> failwith "fold_continue_point_stmt: unexpected empty list"
  | (hd, env) :: _ -> (
      match hd with
      | InsertStmt _ ->
          if env.patch_depth = depth then
            let continue_point = find_continue_point_stmt h1 tl2 in
            fold_stmts2 parent prnt_brnch depth (h1 :: tl1) continue_point acc
          else []
      | DeleteStmt _ ->
          if env.patch_depth = depth then
            let continue_point = find_continue_point_stmt h2 tl1 in
            fold_stmts2 parent prnt_brnch depth continue_point (h2 :: tl2) acc
          else []
      | _ -> fold_stmts2 parent prnt_brnch depth tl1 tl2 acc)

and compute_right_siblings_stmt diffs rest =
  List.slice rest (List.length diffs) (List.length rest)

and get_followup_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs =
  let prev_node = List.hd left_sibs |> Ast.stmt2ast in
  let func = extract_func_name parent in
  let inserted_stmts = find_eq_stmt_in_tl depth hd1 tl2 [] in
  if List.is_empty inserted_stmts then
    let deleted_stmts = find_eq_stmt_in_tl depth hd2 tl1 [] in
    if List.is_empty deleted_stmts then
      let env = mk_diff_env depth prnt_brnch prev_node in
      let ctx =
        mk_context parent (Ast.stmts2path left_sibs) (Ast.stmts2path tl1)
          (List.length left_sibs) func
      in
      [ (InsertStmt (ctx, hd2), env); (DeleteStmt (ctx, hd1), env) ]
    else
      let deleted_stmts = hd1 :: List.rev (List.tl_exn deleted_stmts) in
      let right_siblings = compute_right_siblings_stmt deleted_stmts tl1 in
      mk_diff_stmt Deletion parent prnt_brnch depth deleted_stmts left_sibs
        right_siblings
  else
    let inserted_stmts = hd2 :: List.rev (List.tl_exn inserted_stmts) in
    (* let right_siblings = compute_right_siblings_stmt inserted_stmts tl1 in *)
    (* prolly have to count the #of delete stmt for right sib *)
    mk_diff_stmt Insertion parent prnt_brnch depth inserted_stmts left_sibs
      (hd1 :: tl1)

and compute_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs =
  match (hd1.Cil.skind, hd2.Cil.skind) with
  | Cil.Instr i1, Cil.Instr i2 ->
      if Ast.eq_instr i1 i2 then
        let instr1, instr2 = (List.hd_exn i1, List.hd_exn i2) in
        let parent = Ast.Stmt hd1 :: parent in
        extract_instr parent depth instr1 instr2
      else
        get_followup_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs
  | Cil.If (c1, t_blck1, eblck1, _), Cil.If (c2, t_blck2, eblck2, _) ->
      let exp_diff =
        if Ast.eq_exp c1 c2 then []
        else
          let parent = Ast.Stmt hd1 :: parent in
          get_followup_diff_exp Update parent 0 c1 c2 [] [] []
      in
      if Ast.eq_stmt hd1.Cil.skind hd2.Cil.skind then
        let parent = Ast.Stmt hd1 :: parent in
        exp_diff
        @ extract_block parent (TrueBranch :: prnt_brnch) (depth + 1) t_blck1
            t_blck2
        @ extract_block parent
            (FalseBranch :: prnt_brnch)
            (depth + 1) eblck1 eblck2
      else
        get_followup_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs
  | Cil.Loop (blk1, _, _, _), Cil.Loop (blk2, _, _, _) ->
      if Ast.eq_stmt hd1.Cil.skind hd2.Cil.skind then
        let parent = Ast.Stmt hd1 :: parent in
        extract_block parent prnt_brnch (depth + 1) blk1 blk2
      else
        get_followup_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs
  | Cil.Return (Some e1, _), Cil.Return (Some e2, _) ->
      if Ast.eq_stmt hd1.skind hd2.skind then []
      else
        let parent = Ast.Stmt hd1 :: parent in
        get_followup_diff_exp Update parent 0 e1 e2 [] [] []
  | Cil.Return (None, _), Cil.Return (None, _) -> []
  | Cil.Block b1, Cil.Block b2 ->
      if Ast.eq_stmt hd1.Cil.skind hd2.Cil.skind then
        extract_block parent prnt_brnch (depth + 1) b1 b2
      else
        get_followup_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs
  | Cil.Goto (dest1, _), Cil.Goto (dest2, _) ->
      if Ast.eq_stmt !dest1.Cil.skind !dest2.Cil.skind then []
      else
        get_followup_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs
  | Cil.TryExcept _, Cil.TryExcept _ | Cil.TryFinally _, Cil.TryFinally _ -> []
  | _ ->
      get_followup_diff_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 left_sibs

and decide_next_step_glob parent prnt_brnch depth diff hd1 hd2 tl1 tl2
    new_l_sibs l_sibs =
  match diff with
  | [] -> fold_stmts2 parent prnt_brnch depth tl1 tl2 new_l_sibs
  | (h, _) :: t -> (
      if List.is_empty t then
        diff
        @ fold_continue_point_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2 diff
            l_sibs
      else
        match (h, List.hd_exn t |> get_diff) with
        | InsertStmt _, DeleteStmt _ ->
            diff @ fold_stmts2 parent prnt_brnch depth tl1 tl2 l_sibs
        | _ ->
            diff
            @ fold_continue_point_stmt parent prnt_brnch depth hd1 hd2 tl1 tl2
                diff l_sibs)

and fold_stmts2 parent prnt_brnch depth stmts1 stmts2 left_sibs =
  let prev_node = List.hd left_sibs |> Ast.stmt2ast in
  let func = extract_func_name parent in
  match (stmts1, stmts2) with
  | [], [] -> []
  | s1 :: ss1, s2 :: ss2 ->
      let updated_left_sibs = s1 :: left_sibs in
      let es =
        compute_diff_stmt parent prnt_brnch depth s1 s2 ss1 ss2 left_sibs
      in
      decide_next_step_glob parent prnt_brnch depth es s1 s2 ss1 ss2
        updated_left_sibs left_sibs
  | [], s2 :: ss2 ->
      let env = mk_diff_env depth prnt_brnch prev_node in
      let ctx =
        mk_context parent (Ast.stmts2path left_sibs) [] (List.length left_sibs)
          func
      in
      (InsertStmt (ctx, s2), env)
      :: fold_stmts2 parent prnt_brnch depth [] ss2 left_sibs
  | s1 :: ss1, [] ->
      let env = mk_diff_env depth prnt_brnch prev_node in
      let ctx =
        mk_context parent (Ast.stmts2path left_sibs) (Ast.stmts2path ss1)
          (List.length left_sibs) func
      in
      (DeleteStmt (ctx, s1), env)
      :: fold_stmts2 parent prnt_brnch depth ss1 [] left_sibs

and extract_block parent prnt_brnch depth block1 block2 =
  let remove_empty_instrs stmts =
    List.fold_left
      ~f:(fun acc x -> if Ast.is_empty_instr x then acc else x :: acc)
      ~init:[] stmts
    |> List.rev
  in
  let stmts1 = remove_empty_instrs block1.Cil.bstmts in
  let stmts2 = remove_empty_instrs block2.Cil.bstmts in
  fold_stmts2 parent prnt_brnch depth stmts1 stmts2 []

let process_cil_glob_list lst =
  List.fold_left ~f:(fun acc glob -> Ast.Global glob :: acc) ~init:[] lst
  |> List.rev

let rec find_eq_glob_in_tl glob1 globals acc =
  match globals with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_global glob1 hd then hd :: acc
      else find_eq_glob_in_tl glob1 tl (hd :: acc)

let rec find_continue_point_glob glob1 globals =
  match globals with
  | [] -> []
  | hd :: tl ->
      if Ast.eq_global glob1 hd then tl else find_continue_point_glob glob1 tl

let rec mk_diff_glob code depth glob_lst acc_left acc_right =
  let prev_node = List.hd acc_left |> Ast.glob2ast in
  match glob_lst with
  | [] -> []
  | hd :: tl -> (
      let parent = [ Ast.NotApplicable ] in
      let env = mk_diff_env depth [] prev_node in
      let ctx =
        mk_context parent (Ast.globs2path acc_left) (Ast.globs2path acc_right)
          (List.length acc_left) "None"
      in
      match code with
      | Insertion ->
          (InsertGlobal (ctx, hd), env)
          :: mk_diff_glob code depth tl acc_left acc_right
      | Deletion ->
          (DeleteGlobal (ctx, hd), env)
          :: mk_diff_glob code depth tl acc_left acc_right
      | _ -> failwith "mk_diff_glob: unexpected code")

and fold_continue_point_glob depth glob1 glob2 es tl1 tl2 =
  match es with
  | [] -> failwith "fold_continue_point_glob: unexpected empty list"
  | (hd, _) :: _ -> (
      match hd with
      | InsertGlobal _ ->
          let continue_point = find_continue_point_glob glob1 tl2 in
          fold_globals2 depth tl1 continue_point
      | DeleteGlobal _ ->
          let continue_point = find_continue_point_glob glob2 tl1 in
          fold_globals2 depth continue_point tl2
      | _ -> fold_globals2 depth tl1 tl2)

and compute_right_siblings_glob diffs rest =
  match List.hd diffs with
  | Some next -> next :: find_continue_point_glob next rest
  | None -> []

and get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sibs =
  let prev_node = List.hd left_sibs |> Ast.glob2ast in
  let inserted_globs = find_eq_glob_in_tl glob1 tl2 [] in
  if List.is_empty inserted_globs then
    let deleted_globs = find_eq_glob_in_tl glob2 tl1 [] in
    if List.is_empty deleted_globs then
      let parent = [ Ast.NotApplicable ] in
      let env = mk_diff_env depth [] prev_node in
      let ctx =
        mk_context parent (Ast.globs2path left_sibs) (Ast.globs2path tl1)
          (List.length left_sibs) "None"
      in
      [ (InsertGlobal (ctx, glob2), env); (DeleteGlobal (ctx, glob1), env) ]
    else
      let deleted_globs = glob1 :: List.tl_exn deleted_globs in
      let right_siblings = compute_right_siblings_glob deleted_globs tl1 in
      mk_diff_glob Deletion depth deleted_globs left_sibs right_siblings
  else
    let inserted_globs = glob2 :: List.tl_exn inserted_globs in
    let right_siblings = compute_right_siblings_glob inserted_globs tl1 in
    mk_diff_glob Insertion depth inserted_globs left_sibs right_siblings

and compute_diff_glob depth glob1 glob2 tl1 tl2 left_sbis =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      if Ast.eq_global glob1 glob2 then
        let parent = [ Ast.glob2ast (Some glob1) ] in
        let depth = depth + 1 in
        extract_block parent [] depth func_info1.sbody func_info2.sbody
      else get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sbis
  | Cil.GVarDecl _, Cil.GVarDecl _ ->
      if Ast.eq_global glob1 glob2 then []
      else get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sbis
  | Cil.GType _, Cil.GType _ ->
      if Ast.eq_global glob1 glob2 then []
      else get_followup_diff_glob depth glob1 glob2 tl1 tl2 left_sbis
  | Cil.GCompTag _, Cil.GCompTag _ -> []
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _ -> []
  | Cil.GEnumTag _, Cil.GEnumTag _ -> []
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _ -> []
  | Cil.GVar _, Cil.GVar _ -> []
  | Cil.GAsm _, Cil.GAsm _ -> []
  | Cil.GPragma _, Cil.GPragma _ -> []
  | Cil.GText _, Cil.GText _ -> []
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

and fold_globals2 depth doner_gobals patch_globals left_sibs =
  let prev_node = List.hd left_sibs |> Ast.glob2ast in
  match (doner_gobals, patch_globals) with
  | [], [] -> []
  | hd1 :: tl1, hd2 :: tl2 ->
      let updated_left_sibs = hd1 :: left_sibs in
      let diff = compute_diff_glob depth hd1 hd2 tl1 tl2 left_sibs in
      decide_next_step_glob depth diff hd1 hd2 tl1 tl2 updated_left_sibs
        left_sibs
  | [], hd2 :: tl2 ->
      let parent = [] in
      let env = mk_diff_env depth [] prev_node in
      let ctx =
        mk_context parent (Ast.globs2path left_sibs) [] (List.length left_sibs)
          "None"
      in
      (InsertGlobal (ctx, hd2), env) :: fold_globals2 depth [] tl2 left_sibs
  | hd1 :: tl1, [] ->
      let parent = [] in
      let env = mk_diff_env depth [] prev_node in
      let ctx =
        mk_context parent (Ast.globs2path left_sibs) (Ast.globs2path tl1)
          (List.length left_sibs) "None"
      in
      (DeleteGlobal (ctx, hd1), env) :: fold_globals2 depth tl1 [] left_sibs

let compare = compare

let define_diff buggy_file patch_file =
  let globs1, globs2 =
    ( H.remove_comments buggy_file.Cil.globals,
      H.remove_comments patch_file.Cil.globals )
  in
  fold_globals2 beginning_idx globs1 globs2 []
