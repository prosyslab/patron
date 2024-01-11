module H = Utils
module J = Yojson.Basic
module StrMap = Map.Make (String)

module CilElement = struct
  type t =
    | Null
    | EGlobal of Cil.global
    | EStmt of Cil.stmt
    | EExp of Cil.exp
    | ELval of Cil.lval

  let glob_to_elem element =
    match element with None -> Null | Some x -> EGlobal x

  let stmt_to_elem element =
    match element with None -> Null | Some x -> EStmt x

  let exp_to_elem element = match element with None -> Null | Some x -> EExp x

  let lval_to_elem element =
    match element with None -> Null | Some x -> ELval x

  let elem_to_stmt element =
    match element with EStmt x -> x | _ -> failwith "Not a statement"

  let string_of_element element =
    match element with
    | EGlobal g -> H.string_of_global g
    | EStmt s -> H.string_of_stmt s
    | EExp e -> H.string_of_exp e
    | ELval l -> H.string_of_lval l
    | Null -> "Null"

  let compare = compare
end

let insertion_code = 0
let deletion_code = 1
let update_code = 2
let true_branch = 1
let false_branch = 0
let no_branch = -1

type context = {
  depth : int;
  parent : CilElement.t list;
  parent_branch : int;
  patch_loc : int;
  patch_loc_node : CilElement.t;
}

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

let pp_diffstmt fmt context stmt =
  H.F.fprintf fmt "%s\n\n===============context=================\n"
    (H.string_of_stmt stmt);
  H.F.fprintf fmt "depth: %d\n" context.depth;
  H.F.fprintf fmt "parents(bottom_up) -> \n";
  List.iter
    (fun x ->
      H.F.fprintf fmt "%s\n" (CilElement.string_of_element x |> H.summarize_pp);
      H.F.fprintf fmt "-------\n")
    context.parent;
  H.F.fprintf fmt "-----------------------------------------\n"

let rec pp_diffexp fmt context exp_lst code =
  match code with
  | 0 | 1 ->
      H.F.fprintf fmt "%s\n\n===============context=================\n"
        (List.hd exp_lst |> H.string_of_exp);
      H.F.fprintf fmt "depth: %d\n" context.depth;
      H.F.fprintf fmt "parents(bottom_up) -> \n";
      List.iter
        (fun x ->
          H.F.fprintf fmt "%s\n"
            (CilElement.string_of_element x |> H.summarize_pp);
          H.F.fprintf fmt "-------\n")
        context.parent;
      H.F.fprintf fmt "-----------------------------------------\n"
  | 2 ->
      H.F.fprintf fmt
        "From ->\n%s\nTo ->%s\n\n===============context=================\n"
        (List.hd exp_lst |> H.string_of_exp)
        (List.hd (List.tl exp_lst) |> H.string_of_exp)
  | _ -> failwith "pp_diffexp: unexpected code"

let pp_action fmt = function
  | InsertGlobal (_, g2) ->
      H.F.fprintf fmt "InsertGlobal: \n%s\n" (H.string_of_global g2)
  | DeleteGlobal (_, g2) ->
      H.F.fprintf fmt "DeleteGlobal: \n%s\n" (H.string_of_global g2)
  | InsertStmt (c, s1) ->
      H.F.fprintf fmt "InsertStmt: \n";
      pp_diffstmt fmt c s1
  | DeleteStmt (c, s1) ->
      H.F.fprintf fmt "DeleteStmt: \n";
      pp_diffstmt fmt c s1
  | InsertExp (c, e1) ->
      H.F.fprintf fmt "InsertExp: \n";
      pp_diffexp fmt c [ e1 ] insertion_code
  | DeleteExp (c, e1) ->
      H.F.fprintf fmt "DeleteExp: \n";
      pp_diffexp fmt c [ e1 ] deletion_code
  | UpdateExp (c, e1, e2) ->
      H.F.fprintf fmt "UpdateExp: \n";
      pp_diffexp fmt c [ e1; e2 ] update_code
  | InsertLval (_, l1) -> H.F.fprintf fmt "InsertLval: %s" (H.string_of_lval l1)
  | DeleteLval (_, l1) -> H.F.fprintf fmt "DeleteLval: %s" (H.string_of_lval l1)
  | UpdateLval (_, l1, l2) ->
      H.F.fprintf fmt "UpdateLval: \n%s\n\nTo->%s\n" (H.string_of_lval l1)
        (H.string_of_lval l2)

let string_of_action action =
  let buf = Buffer.create 16 in
  let fmt = H.F.formatter_of_buffer buf in
  pp_action fmt action;
  H.F.pp_print_flush fmt ();
  Buffer.contents buf

let print_edit_script script =
  List.iter (fun action -> print_endline (string_of_action action)) script

let pp_edit_script fmt script =
  H.F.fprintf fmt "Edit Script Summary:\n";
  H.F.fprintf fmt "Size: %d\n" (List.length script);
  List.fold_left
    (fun acc action ->
      print_endline "$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$";
      H.F.fprintf fmt "Script #%d:\n" (acc + 1);
      H.F.fprintf fmt "%a\n" pp_action action;
      acc + 1)
    0 script
  |> ignore

let process_cil_exp_list lst =
  List.fold_left (fun acc exp -> CilElement.EExp exp :: acc) [] lst |> List.rev

let rec make_diff_exp code parent prev depth width (exp_lst : Cil.exp list) =
  match exp_lst with
  | [] -> []
  | hd :: tl ->
      let context =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = prev;
          parent_branch = no_branch;
        }
      in
      if code = insertion_code then
        InsertExp (context, hd) :: make_diff_exp code parent prev depth width tl
      else
        DeleteExp (context, hd) :: make_diff_exp code parent prev depth width tl

let rec find_continue_point_exp exp1 param =
  match param with
  | [] -> []
  | hd :: tl -> if H.eq_exp hd exp1 then tl else find_continue_point_exp exp1 tl

let rec find_eq_exp_in_tl depth exp1 expl acc =
  match expl with
  | [] -> []
  | hd :: tl ->
      if H.eq_exp hd exp1 then hd :: acc
      else
        let result = find_eq_exp_in_tl depth exp1 tl [ hd ] in
        if result <> [] then result @ acc else []

let extract_exp code parent prev depth width exp1 exp2 expl1 expl2 =
  if code = update_code then
    let ctx =
      {
        depth;
        parent;
        patch_loc = width;
        patch_loc_node = prev;
        parent_branch = no_branch;
      }
    in
    [ UpdateExp (ctx, exp1, exp2) ]
  else
    let insertion = find_eq_exp_in_tl depth exp1 expl2 [] in
    if insertion <> [] then
      let insertion = exp2 :: List.tl insertion in
      make_diff_exp insertion_code parent prev depth width insertion
    else
      let deletion = find_eq_exp_in_tl depth exp2 expl1 [] in
      if deletion <> [] then
        let deletion = exp1 :: List.tl deletion in
        make_diff_exp deletion_code parent prev depth width deletion
      else
        let ctx =
          {
            depth;
            parent;
            patch_loc = width;
            patch_loc_node = prev;
            parent_branch = no_branch;
          }
        in
        [ UpdateExp (ctx, exp1, exp2) ]

let rec fold_continue_point_param parent depth width h1 h2 tl1 tl2 es acc =
  match es with
  | [] -> failwith "fold_continue_point_stmt: unexpected empty list"
  | hd :: _ -> (
      match hd with
      | InsertExp (c, s) ->
          if c.depth = depth then
            let continue_point = find_continue_point_exp h1 tl2 in
            fold_param2 parent (Some s) depth width tl1 continue_point acc
          else []
      | DeleteExp (c, s) ->
          if c.depth = depth then
            let continue_point = find_continue_point_exp h2 tl1 in
            fold_param2 parent (Some s) depth width continue_point tl2 acc
          else []
      | _ -> fold_param2 parent None depth width tl1 tl2 acc)

and get_diff_param parent prev depth width exp1 exp2 expl1 expl2 =
  if H.eq_exp exp1 exp2 then []
  else extract_exp insertion_code parent prev depth width exp1 exp2 expl1 expl2

and fold_param2 parent prev depth width el1 el2 acc =
  let prev_node = CilElement.exp_to_elem prev in
  match (el1, el2) with
  | [], [] -> []
  | hd1 :: tl1, hd2 :: tl2 ->
      let es = get_diff_param parent prev_node depth width hd1 hd2 tl1 tl2 in
      let acc_next = hd1 :: acc in
      if es <> [] then
        es @ fold_continue_point_param parent depth width hd1 hd2 tl1 tl2 es acc
      else es @ fold_param2 parent (Some hd1) depth width tl1 tl2 acc_next
  | [], hd :: tl ->
      let context =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = prev_node;
          parent_branch = no_branch;
        }
      in
      InsertExp (context, hd) :: fold_param2 parent prev depth width [] tl acc
  | hd :: tl, [] ->
      let context =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = prev_node;
          parent_branch = no_branch;
        }
      in
      DeleteExp (context, hd) :: fold_param2 parent prev depth width tl [] acc

let extract_call parent depth width lv1 e1 el1 lv2 e2 el2 =
  let lval_diff =
    match (lv1, lv2) with
    | None, Some lv ->
        let ctx =
          {
            depth;
            parent;
            patch_loc = width;
            patch_loc_node = Null;
            parent_branch = no_branch;
          }
        in
        [ InsertLval (ctx, lv) ]
    | Some lv, None ->
        let ctx =
          {
            depth;
            parent;
            patch_loc = width;
            patch_loc_node = Null;
            parent_branch = no_branch;
          }
        in
        [ DeleteLval (ctx, lv) ]
    | Some l1, Some l2 ->
        if H.eq_lval l1 l2 then []
        else
          let ctx =
            {
              depth;
              parent;
              patch_loc = width;
              patch_loc_node = Null;
              parent_branch = no_branch;
            }
          in
          [ UpdateLval (ctx, l1, l2) ]
    | _ -> []
  in
  let exp_diff =
    if H.eq_exp_conc e1 e2 then []
    else
      let ctx =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = Null;
          parent_branch = no_branch;
        }
      in
      [ UpdateExp (ctx, e1, e2) ]
  in
  let param_diff = fold_param2 parent None 0 width el1 el2 [] in
  lval_diff @ exp_diff @ param_diff

let extract_set parent depth width lv1 e1 lv2 e2 =
  let context =
    {
      depth;
      parent;
      patch_loc = width;
      patch_loc_node = Null;
      parent_branch = no_branch;
    }
  in
  let lval_diff =
    if H.eq_lval lv1 lv2 then [] else [ UpdateLval (context, lv1, lv2) ]
  in
  let exp_diff =
    if H.eq_exp e1 e2 then [] else [ UpdateExp (context, e1, e2) ]
  in
  lval_diff @ exp_diff

(* This is where stmt/instr ends *)

let process_cil_stmt_list lst =
  List.fold_left (fun acc stmt -> CilElement.EStmt stmt :: acc) [] lst
  |> List.rev

let extract_instr parent depth width instr1 instr2 =
  match (instr1, instr2) with
  | Cil.Set (lv1, e1, _), Cil.Set (lv2, e2, _) ->
      extract_set parent depth width lv1 e1 lv2 e2
  | Cil.Call (lv1, e1, el1, _), Cil.Call (lv2, e2, el2, _) ->
      extract_call parent depth width lv1 e1 el1 lv2 e2 el2
  | _ -> []

let rec find_continue_point_stmt stmt1 stmts =
  match stmts with
  | [] -> []
  | hd :: tl ->
      if H.eq_stmt stmt1.Cil.skind hd.Cil.skind then stmts
      else find_continue_point_stmt stmt1 tl

let rec find_eq_stmt_in_tl depth stmt1 stmts acc =
  match stmts with
  | [] -> []
  | hd :: tl ->
      if H.eq_stmt stmt1.Cil.skind hd.Cil.skind then hd :: acc
      else find_eq_stmt_in_tl depth stmt1 tl (hd :: acc)

let rec make_diff_stmt code parent prnt_brnch prev depth width next stmt_lst =
  match stmt_lst with
  | [] -> []
  | hd :: tl ->
      let context =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = prev;
          parent_branch = prnt_brnch;
        }
      in
      let rest_diff =
        make_diff_stmt code parent prnt_brnch prev depth (width + 1) next tl
      in
      if code = insertion_code then InsertStmt (context, hd) :: rest_diff
      else DeleteStmt (context, hd) :: rest_diff

and fold_continue_point_stmt parent prnt_brnch depth width h1 h2 tl1 tl2 es acc
    =
  match List.rev es with
  | [] -> failwith "fold_continue_point_stmt: unexpected empty list"
  | hd :: _ -> (
      match hd with
      | InsertStmt (c, s) ->
          if c.depth = depth then
            let continue_point = find_continue_point_stmt h1 tl2 in
            fold_stmts2 parent prnt_brnch (Some s) depth (width + 1) (h1 :: tl1)
              continue_point acc
          else []
      | DeleteStmt (c, s) ->
          if c.depth = depth then
            let continue_point = find_continue_point_stmt h2 tl1 in
            fold_stmts2 parent prnt_brnch (Some s) depth (width + 1)
              continue_point (h2 :: tl2) acc
          else []
      | _ -> fold_stmts2 parent prnt_brnch (Some h1) depth width tl1 tl2 acc)

and extract_stmt parent prnt_brnch prev depth width stmt1 stmt2 tl1 tl2 =
  let insertion = find_eq_stmt_in_tl depth stmt1 tl2 [] in
  if insertion <> [] then
    let next = CilElement.stmt_to_elem (Some (List.hd insertion)) in
    let insertion = stmt2 :: List.rev (List.tl insertion) in
    make_diff_stmt insertion_code parent prnt_brnch prev depth width next
      insertion
  else
    let deletion = find_eq_stmt_in_tl depth stmt2 tl1 [] in
    if deletion <> [] then
      let next = CilElement.stmt_to_elem (Some (List.hd deletion)) in
      let deletion = stmt1 :: List.rev (List.tl deletion) in
      make_diff_stmt deletion_code parent prnt_brnch prev depth width next
        deletion
    else
      let context =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = prev;
          parent_branch = prnt_brnch;
        }
      in
      [ InsertStmt (context, stmt2); DeleteStmt (context, stmt1) ]

and get_diff_stmt parent prnt_brnch prev depth width stmt1 stmt2
    (stmts1 : Cil.stmt list) (stmts2 : Cil.stmt list) =
  match (stmt1.Cil.skind, stmt2.Cil.skind) with
  | Cil.Instr i1, Cil.Instr i2 ->
      if H.eq_instr i1 i2 then
        let instr1, instr2 = (List.hd i1, List.hd i2) in
        let parent = CilElement.EStmt stmt1 :: parent in
        extract_instr parent depth width instr1 instr2
      else
        extract_stmt parent prnt_brnch prev depth width stmt1 stmt2 stmts1
          stmts2
  | Cil.If (c1, t_blck1, eblck1, _), Cil.If (c2, t_blck2, eblck2, _) ->
      let exp_diff =
        if H.eq_exp c1 c2 then []
        else
          let parent = CilElement.EStmt stmt1 :: parent in
          extract_exp update_code parent CilElement.Null 0 width c1 c2 [] []
      in
      if H.eq_stmt stmt1.Cil.skind stmt2.Cil.skind then
        let parent = CilElement.EStmt stmt1 :: parent in
        exp_diff
        @ extract_block parent true_branch (depth + 1) t_blck1 t_blck2
        @ extract_block parent false_branch (depth + 1) eblck1 eblck2
      else
        extract_stmt parent prnt_brnch prev depth width stmt1 stmt2 stmts1
          stmts2
  | Cil.Loop (blk1, _, _, _), Cil.Loop (blk2, _, _, _) ->
      if H.eq_stmt stmt1.Cil.skind stmt2.Cil.skind then
        let parent = CilElement.EStmt stmt1 :: parent in
        extract_block parent no_branch (depth + 1) blk1 blk2
      else
        extract_stmt parent prnt_brnch prev depth width stmt1 stmt2 stmts1
          stmts2
  | Cil.Return (Some e1, _), Cil.Return (Some e2, _) ->
      if H.eq_stmt stmt1.skind stmt2.skind then []
      else
        let parent = CilElement.EStmt stmt1 :: parent in
        extract_exp update_code parent CilElement.Null 0 width e1 e2 [] []
  | Cil.Return (None, _), Cil.Return (None, _) -> []
  | Cil.Block b1, Cil.Block b2 ->
      if H.eq_stmt stmt1.Cil.skind stmt2.Cil.skind then
        extract_block parent no_branch (depth + 1) b1 b2
      else
        extract_stmt parent prnt_brnch prev depth width stmt1 stmt2 stmts1
          stmts2
  | Cil.Goto (dest1, _), Cil.Goto (dest2, _) ->
      if H.eq_stmt !dest1.Cil.skind !dest2.Cil.skind then []
      else
        extract_stmt parent prnt_brnch prev depth width stmt1 stmt2 stmts1
          stmts2
  | Cil.TryExcept _, Cil.TryExcept _ | Cil.TryFinally _, Cil.TryFinally _ -> []
  | _ ->
      extract_stmt parent prnt_brnch prev depth width stmt1 stmt2 stmts1 stmts2

and fold_stmts2 parent (prnt_brnch : int) (prev : Cil.stmt option) depth width
    stmts1 stmts2 acc =
  let prev_node = CilElement.stmt_to_elem prev in
  match (stmts1, stmts2) with
  | [], [] -> []
  | s1 :: ss1, s2 :: ss2 -> (
      let acc_next = s1 :: acc in
      let es =
        get_diff_stmt parent prnt_brnch prev_node depth (width + 1) s1 s2 ss1
          ss2
      in
      match es with
      | [] ->
          fold_stmts2 parent prnt_brnch (Some s1) depth (width + 1) ss1 ss2
            acc_next
      | h :: t ->
          if t <> [] then
            match (h, List.hd t) with
            | InsertStmt _, DeleteStmt _ ->
                es
                @ fold_stmts2 parent prnt_brnch (Some s1) depth (width + 1) ss1
                    ss2 acc
            | _ ->
                es
                @ fold_continue_point_stmt parent prnt_brnch depth (width + 1)
                    s1 s2 ss1 ss2 es acc
          else
            es
            @ fold_continue_point_stmt parent depth prnt_brnch (width + 1) s1 s2
                ss1 ss2 es acc)
  | [], s2 :: ss2 ->
      let context =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = prev_node;
          parent_branch = prnt_brnch;
        }
      in
      InsertStmt (context, s2)
      :: fold_stmts2 parent prnt_brnch prev depth (width + 1) [] ss2 acc
  | s1 :: ss1, [] ->
      let context =
        {
          depth;
          parent;
          patch_loc = width;
          patch_loc_node = prev_node;
          parent_branch = prnt_brnch;
        }
      in
      DeleteStmt (context, s1)
      :: fold_stmts2 parent prnt_brnch (Some s1) depth (width + 1) ss1 [] acc

and extract_block parent prnt_brnch depth block1 block2 =
  let stmts1 =
    List.fold_left
      (fun acc x -> if H.is_empty_instr x then acc else x :: acc)
      [] block1.Cil.bstmts
    |> List.rev
  in
  let stmts2 =
    List.fold_left
      (fun acc x -> if H.is_empty_instr x then acc else x :: acc)
      [] block2.Cil.bstmts
    |> List.rev
  in
  fold_stmts2 parent prnt_brnch Option.none depth 0 stmts1 stmts2 []

(* this is where global ends *)

let process_cil_glob_list lst =
  List.fold_left (fun acc glob -> CilElement.EGlobal glob :: acc) [] lst
  |> List.rev

let rec find_eq_glob_in_tl glob1 globals acc =
  match globals with
  | [] -> []
  | hd :: tl ->
      if H.eq_global glob1 hd then hd :: acc
      else
        let result = find_eq_glob_in_tl glob1 tl [ hd ] in
        if result <> [] then result @ acc else []

let rec find_continue_point_glob glob1 globals =
  match globals with
  | [] -> []
  | hd :: tl ->
      if H.eq_global glob1 hd then tl else find_continue_point_glob glob1 tl

let rec make_diff_glob code depth prev next glob_lst acc_left acc_right =
  match glob_lst with
  | [] -> []
  | hd :: tl ->
      let parent = [ CilElement.Null ] in
      let context =
        {
          depth;
          parent;
          patch_loc = -1;
          patch_loc_node = CilElement.Null;
          parent_branch = no_branch;
        }
      in
      if code = insertion_code then
        InsertGlobal (context, hd)
        :: make_diff_glob code depth prev next tl acc_left acc_right
      else
        DeleteGlobal (context, hd)
        :: make_diff_glob code depth prev next tl acc_left acc_right

and fold_continue_point_glob depth glob1 glob2 es tl1 tl2 =
  match es with
  | [] -> failwith "fold_continue_point_glob: unexpected empty list"
  | hd :: _ -> (
      match hd with
      | InsertGlobal (_, g) ->
          let continue_point = find_continue_point_glob glob1 tl2 in
          fold_globals2 (Some g) depth tl1 continue_point
      | DeleteGlobal (_, g) ->
          let continue_point = find_continue_point_glob glob2 tl1 in
          fold_globals2 (Some g) depth continue_point tl2
      | _ -> fold_globals2 (Some glob1) depth tl1 tl2)

and extract_global prev depth glob1 glob2 tl1 tl2 acc =
  let insertion = find_eq_glob_in_tl glob1 tl2 [] in
  if insertion <> [] then
    let next = CilElement.glob_to_elem (Some (List.hd insertion)) in
    let insertion = glob2 :: List.tl insertion in
    make_diff_glob insertion_code depth prev next insertion acc tl1
  else
    let deletion = find_eq_glob_in_tl glob2 tl1 [] in
    if deletion <> [] then
      let next = CilElement.glob_to_elem (Some (List.hd deletion)) in
      let deletion = glob1 :: List.tl deletion in
      make_diff_glob deletion_code depth prev next deletion acc tl1
    else
      let _ =
        print_endline "global insertion detected\nglobal deletion detected"
      in
      let parent = [ CilElement.Null ] in
      let context =
        {
          depth;
          parent;
          patch_loc = -1;
          patch_loc_node = CilElement.Null;
          parent_branch = no_branch;
        }
      in
      [ InsertGlobal (context, glob2); DeleteGlobal (context, glob1) ]

and get_diff_glob prev depth glob1 glob2 tl1 tl2 acc =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      if H.eq_global glob1 glob2 then
        let parent = [ CilElement.glob_to_elem (Some glob1) ] in
        let depth = depth + 1 in
        extract_block parent no_branch depth func_info1.sbody func_info2.sbody
      else extract_global prev depth glob1 glob2 tl1 tl2 acc
  | Cil.GVarDecl _, Cil.GVarDecl _ ->
      if H.eq_global glob1 glob2 then []
      else extract_global prev depth glob1 glob2 tl1 tl2 acc
  | Cil.GType _, Cil.GType _ ->
      if H.eq_global glob1 glob2 then []
      else extract_global prev depth glob1 glob2 tl1 tl2 acc
  | Cil.GCompTag _, Cil.GCompTag _ -> []
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _ -> []
  | Cil.GEnumTag _, Cil.GEnumTag _ -> []
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _ -> []
  | Cil.GVar _, Cil.GVar _ -> []
  | Cil.GAsm _, Cil.GAsm _ -> []
  | Cil.GPragma _, Cil.GPragma _ -> []
  | Cil.GText _, Cil.GText _ -> []
  | _ -> extract_global prev depth glob1 glob2 tl1 tl2 acc

and fold_globals2 prev depth doner_gobals patch_globals acc =
  let prev_node = CilElement.glob_to_elem prev in
  match (doner_gobals, patch_globals) with
  | [], [] -> []
  | hd1 :: tl1, hd2 :: tl2 -> (
      let acc_next = hd1 :: acc in
      let es = get_diff_glob prev_node depth hd1 hd2 tl1 tl2 acc in
      match es with
      | [] -> fold_globals2 (Some hd1) depth tl1 tl2 acc_next
      | h :: t ->
          if t <> [] then
            match (h, List.hd t) with
            | InsertGlobal _, DeleteGlobal _ ->
                es @ fold_globals2 (Some hd1) depth tl1 tl2 acc
            | _ -> es @ fold_continue_point_glob depth hd1 hd2 es tl1 tl2 acc
          else es @ fold_continue_point_glob depth hd1 hd2 es tl1 tl2 acc)
  | [], hd2 :: tl2 ->
      let parent = [ CilElement.Null ] in
      (* TODO: patch_loc *)
      let context =
        {
          depth;
          parent;
          patch_loc = -1;
          patch_loc_node = CilElement.Null;
          parent_branch = no_branch;
        }
      in
      InsertGlobal (context, hd2) :: fold_globals2 prev depth [] tl2 acc
  | hd1 :: tl1, [] ->
      let parent = [ CilElement.Null ] in
      let context =
        {
          depth;
          parent;
          patch_loc = -1;
          patch_loc_node = CilElement.Null;
          parent_branch = no_branch;
        }
      in
      DeleteGlobal (context, hd1) :: fold_globals2 prev depth tl1 [] acc

let compare = compare

let define_diff buggy_file patch_file =
  let globs1, globs2 =
    ( H.remove_comments buggy_file.Cil.globals,
      H.remove_comments patch_file.Cil.globals )
  in
  fold_globals2 Option.None 0 globs1 globs2 []
