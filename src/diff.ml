module H = TransformerHelper
module J = Yojson.Basic
module L = Logger
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

module Diff = struct
  let insertion_code = 0
  let deletion_code = 1
  let update_code = 2

  type context = {
    parent : CilElement.t;
    left_sibling : CilElement.t;
    right_sibling : CilElement.t;
    snk : CilElement.t;
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

  let pp_action fmt = function
    | InsertGlobal (c, g2) ->
        H.F.fprintf fmt
          "InsertGlobal: %s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_global g2)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)
    | DeleteGlobal (c, g2) ->
        H.F.fprintf fmt
          "DeleteGlobal: %s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_global g2)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)
    | InsertStmt (c, s1) ->
        H.F.fprintf fmt
          "InsertStmt: %s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_stmt s1)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)
    | DeleteStmt (c, s1) ->
        H.F.fprintf fmt
          "DeleteStmt: %s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_stmt s1)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)
    | InsertExp (c, e1) ->
        H.F.fprintf fmt
          "InsertExp: %s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_exp e1)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)
    | DeleteExp (c, e1) ->
        H.F.fprintf fmt
          "DeleteExp: %s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_exp e1)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)
    | UpdateExp (c, e1, e2) ->
        H.F.fprintf fmt
          "UpdateExp: %s\n\
           \t->%s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_exp e1) (H.string_of_exp e2)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)
    | InsertLval (_, l1) ->
        H.F.fprintf fmt "InsertLval: %s" (H.string_of_lval l1)
    | DeleteLval (_, l1) ->
        H.F.fprintf fmt "DeleteLval: %s" (H.string_of_lval l1)
    | UpdateLval (c, l1, l2) ->
        H.F.fprintf fmt
          "UpdateLval: %s\n\
           \t->%s\n\
           Parent -> %s\n\
           Left -> %s\n\
           Right -> %s\n\
           ================="
          (H.string_of_lval l1) (H.string_of_lval l2)
          (CilElement.string_of_element c.parent)
          (CilElement.string_of_element c.left_sibling)
          (CilElement.string_of_element c.right_sibling)

  let string_of_action action =
    let buf = Buffer.create 16 in
    let fmt = H.F.formatter_of_buffer buf in
    pp_action fmt action;
    H.F.pp_print_flush fmt ();
    Buffer.contents buf

  let print_edit_script script =
    List.iter (fun action -> print_endline (string_of_action action)) script

  let pp_edit_script fmt script =
    List.iter (fun action -> H.F.fprintf fmt "%a\n" pp_action action) script

  let rec make_diff_exp code parent prev next (exp_lst : Cil.exp list) =
    match exp_lst with
    | [] -> []
    | hd :: tl ->
        let context =
          {
            parent;
            left_sibling = prev;
            right_sibling = next;
            snk = CilElement.Null;
          }
        in
        if code = 0 then
          InsertExp (context, hd) :: make_diff_exp code parent prev next tl
        else DeleteExp (context, hd) :: make_diff_exp code parent prev next tl

  let rec find_continue_point_exp exp1 param =
    match param with
    | [] -> []
    | hd :: tl ->
        if H.eq_exp hd exp1 then tl else find_continue_point_exp exp1 tl

  let rec find_eq_exp_in_tl exp1 expl acc =
    match expl with
    | [] -> []
    | hd :: tl ->
        if H.eq_exp hd exp1 then hd :: acc
        else
          let result = find_eq_exp_in_tl exp1 tl [ hd ] in
          if result <> [] then result @ acc else []

  let extract_exp code parent prev exp1 exp2 expl1 expl2 =
    if code = update_code then (
      let _ = L.debug "exp update detected" in
      print_endline "exp update detected";
      [
        UpdateExp
          ( {
              parent;
              left_sibling = Null;
              right_sibling = Null;
              snk = CilElement.Null;
            },
            exp1,
            exp2 );
      ])
    else
      let insertion = find_eq_exp_in_tl exp1 expl2 [] in
      if insertion <> [] then
        let _ = L.debug "exp insertion detected" in
        let next = CilElement.exp_to_elem (Some (List.hd insertion)) in
        let insertion = exp2 :: List.tl insertion in
        make_diff_exp insertion_code parent prev next insertion
      else
        let deletion = find_eq_exp_in_tl exp2 expl1 [] in
        if deletion <> [] then
          let _ = L.debug "exp deletion detected" in
          let next = CilElement.exp_to_elem (Some (List.hd deletion)) in
          let deletion = exp1 :: List.tl deletion in
          make_diff_exp deletion_code parent prev next deletion
        else
          let _ = L.debug "exp update detected" in
          let next =
            if expl1 <> [] then CilElement.exp_to_elem (Some (List.hd expl2))
            else Null
          in
          [
            UpdateExp
              ( {
                  parent;
                  left_sibling = prev;
                  right_sibling = next;
                  snk = CilElement.Null;
                },
                exp1,
                exp2 );
          ]

  let rec fold_continue_point_param parent h1 h2 tl1 tl2 es =
    match es with
    | [] -> failwith "fold_continue_point_stmt: unexpected empty list"
    | hd :: _ -> (
        match hd with
        | InsertExp (_, s) ->
            fold_param2 parent (Some s) tl1 (find_continue_point_exp h1 tl2)
        | DeleteExp (_, s) ->
            fold_param2 parent (Some s) (find_continue_point_exp h2 tl1) tl2
        | _ -> fold_param2 parent None tl1 tl2)

  and get_diff_param parent prev exp1 exp2 expl1 expl2 =
    if H.eq_exp exp1 exp2 then []
    else extract_exp insertion_code parent prev exp1 exp2 expl1 expl2

  and fold_param2 parent prev el1 el2 =
    let prev_node = CilElement.exp_to_elem prev in
    match (el1, el2) with
    | [], [] -> []
    | hd1 :: tl1, hd2 :: tl2 ->
        let es = get_diff_param parent prev_node hd1 hd2 tl1 tl2 in
        if es <> [] then
          es @ fold_continue_point_param parent hd1 hd2 tl1 tl2 es
        else es @ fold_param2 parent (Some hd1) tl1 tl2
    | [], hd :: tl ->
        let context =
          {
            parent;
            left_sibling = prev_node;
            right_sibling = Null;
            snk = CilElement.Null;
          }
        in
        let _ = L.debug "exp insertion detected" in
        InsertExp (context, hd) :: fold_param2 parent prev [] tl
    | hd :: tl, [] ->
        let context =
          {
            parent;
            left_sibling = prev_node;
            right_sibling = Null;
            snk = CilElement.Null;
          }
        in
        DeleteExp (context, hd) :: fold_param2 parent prev tl []

  let extract_call parent lv1 e1 el1 lv2 e2 el2 =
    let lval_diff =
      match (lv1, lv2) with
      | None, Some lv ->
          let _ = L.debug "lval insertion detected" in
          [
            InsertLval
              ( {
                  parent;
                  left_sibling = Null;
                  right_sibling = Null;
                  snk = CilElement.Null;
                },
                lv );
          ]
      | Some lv, None ->
          let _ = L.debug "lval deletion detected" in
          [
            DeleteLval
              ( {
                  parent;
                  left_sibling = Null;
                  right_sibling = Null;
                  snk = CilElement.Null;
                },
                lv );
          ]
      | Some l1, Some l2 ->
          if H.string_of_lval l1 = H.string_of_lval l2 then []
          else
            let _ = L.debug "lval update detected" in
            [
              UpdateLval
                ( {
                    parent;
                    left_sibling = Null;
                    right_sibling = Null;
                    snk = CilElement.Null;
                  },
                  l1,
                  l2 );
            ]
      | _ -> []
    in
    let exp_diff =
      if H.string_of_exp e1 = H.string_of_exp e2 then []
      else
        let _ = L.debug "exp update detected" in
        [
          UpdateExp
            ( {
                parent;
                left_sibling = Null;
                right_sibling = Null;
                snk = CilElement.Null;
              },
              e1,
              e2 );
        ]
    in
    let param_diff = fold_param2 parent Option.None el1 el2 in
    lval_diff @ exp_diff @ param_diff

  let extract_set parent lv1 e1 lv2 e2 =
    let context =
      {
        parent;
        left_sibling = Null;
        right_sibling = Null;
        snk = CilElement.Null;
      }
    in
    let lval_diff =
      if H.string_of_lval lv1 = H.string_of_lval lv2 then []
      else
        let _ = L.debug "lval update detected" in
        [ UpdateLval (context, lv1, lv2) ]
    in
    let exp_diff =
      if H.string_of_exp e1 = H.string_of_exp e2 then []
      else
        let _ = L.debug "exp update detected" in
        [ UpdateExp (context, e1, e2) ]
    in
    lval_diff @ exp_diff

  (* This is where stmt/instr ends *)
  let extract_instr parent instr1 instr2 =
    match (instr1, instr2) with
    | Cil.Set (lv1, e1, _), Cil.Set (lv2, e2, _) ->
        extract_set parent lv1 e1 lv2 e2
    | Cil.Call (lv1, e1, el1, _), Cil.Call (lv2, e2, el2, _) ->
        extract_call parent lv1 e1 el1 lv2 e2 el2
    | _ -> []

  let rec find_continue_point_stmt stmt1 stmts =
    match stmts with
    | [] -> []
    | hd :: tl ->
        if H.eq_stmt stmt1.Cil.skind hd.Cil.skind then tl
        else find_continue_point_stmt stmt1 tl

  let rec find_eq_stmt_in_tl stmt1 stmts acc =
    match stmts with
    | [] -> []
    | hd :: tl ->
        if H.eq_stmt stmt1.Cil.skind hd.Cil.skind then hd :: acc
        else
          let result = find_eq_stmt_in_tl stmt1 tl (hd :: acc) in
          if result <> [] then result @ acc else []

  let rec make_diff_stmt code parent prev next (stmt_lst : Cil.stmt list) =
    match stmt_lst with
    | [] -> []
    | hd :: tl ->
        let context =
          {
            parent;
            left_sibling = prev;
            right_sibling = next;
            snk = CilElement.Null;
          }
        in
        if code = 0 then
          InsertStmt (context, hd) :: make_diff_stmt code parent prev next tl
        else DeleteStmt (context, hd) :: make_diff_stmt code parent prev next tl

  and fold_continue_point_stmt parent h1 h2 tl1 tl2 es =
    match es with
    | [] -> failwith "fold_continue_point_stmt: unexpected empty list"
    | hd :: _ -> (
        match hd with
        | InsertStmt (_, s) ->
            fold_stmts2 parent (Some s) tl1 (find_continue_point_stmt h1 tl2)
        | DeleteStmt (_, s) ->
            fold_stmts2 parent (Some s) (find_continue_point_stmt h2 tl1) tl2
        | _ -> fold_stmts2 parent (Some h1) tl1 tl2)

  and extract_stmt parent prev stmt1 stmt2 tl1 tl2 =
    let insertion = find_eq_stmt_in_tl stmt1 tl2 [] in
    if insertion <> [] then
      let _ = L.debug "stmt insertion detected" in
      let next = CilElement.stmt_to_elem (Some (List.hd insertion)) in
      let insertion = stmt2 :: List.tl insertion in
      make_diff_stmt insertion_code parent prev next insertion
    else
      let deletion = find_eq_stmt_in_tl stmt2 tl1 [] in
      if deletion <> [] then
        let _ = L.debug "stmt deletion detected" in
        let next = CilElement.stmt_to_elem (Some (List.hd deletion)) in
        let deletion = stmt1 :: List.tl deletion in
        make_diff_stmt deletion_code parent prev next deletion
      else
        let _ = L.debug "stmt insertion detected\nstmt deletion detected" in
        let context =
          {
            parent;
            left_sibling = prev;
            right_sibling = CilElement.stmt_to_elem (Some (List.hd tl1));
            snk = CilElement.Null;
          }
        in
        [ InsertStmt (context, stmt2); DeleteStmt (context, stmt1) ]

  and get_diff_stmt parent prev stmt1 stmt2 stmts1 stmts2 =
    match (stmt1.Cil.skind, stmt2.Cil.skind) with
    | Cil.Instr i1, Cil.Instr i2 ->
        let instr1 = List.hd i1 in
        let instr2 = List.hd i2 in
        if H.eq_instr instr1 instr2 then
          extract_instr (CilElement.stmt_to_elem (Some stmt1)) instr1 instr2
        else extract_stmt parent prev stmt1 stmt2 stmts1 stmts2
    | Cil.If (c1, t_blck1, eblck1, _), Cil.If (c2, t_blck2, eblck2, _) ->
        if H.eq_stmt stmt1.Cil.skind stmt2.Cil.skind then
          let exp_diff =
            if H.eq_exp c1 c2 then []
            else extract_exp update_code parent CilElement.Null c1 c2 [] []
          in
          exp_diff
          @ extract_block parent t_blck1 t_blck2
          @ extract_block parent eblck1 eblck2
        else extract_stmt parent prev stmt1 stmt2 stmts1 stmts2
    | Cil.Loop _, Cil.Loop _ ->
        let _ = L.debug "loop detected. loop cannot be analyzed" in
        []
    | Cil.Return (Some e1, _), Cil.Return (Some e2, _) ->
        if H.eq_stmt stmt1.skind stmt2.skind then []
        else extract_exp update_code parent CilElement.Null e1 e2 [] []
    | Cil.Return (None, _), Cil.Return (None, _) -> []
    | Cil.Block _, Cil.Block _ -> []
    | Cil.TryExcept _, Cil.TryExcept _ -> []
    | Cil.TryFinally _, Cil.TryFinally _ -> []
    | _ -> extract_stmt parent prev stmt1 stmt2 stmts1 stmts2

  and fold_stmts2 parent prev stmts1 stmts2 =
    let prev_node = CilElement.stmt_to_elem prev in
    match (stmts1, stmts2) with
    | [], [] -> []
    | s1 :: ss1, s2 :: ss2 -> (
        let es = get_diff_stmt parent prev_node s1 s2 ss1 ss2 in
        match es with
        | [] -> fold_stmts2 parent (Some s1) ss1 ss2
        | h :: t ->
            if t <> [] then
              match (h, List.hd t) with
              | InsertStmt _, DeleteStmt _ ->
                  es @ fold_stmts2 parent (Some s1) ss1 ss2
              | _ -> es @ fold_continue_point_stmt parent s1 s2 ss1 ss2 es
            else es @ fold_continue_point_stmt parent s1 s2 ss1 ss2 es)
    | [], s2 :: ss2 ->
        let context =
          {
            parent;
            left_sibling = prev_node;
            right_sibling = Null;
            snk = CilElement.Null;
          }
        in
        let _ = L.debug "stmt insertion detected" in
        InsertStmt (context, s2) :: fold_stmts2 parent prev [] ss2
    | s1 :: ss1, [] ->
        let context =
          {
            parent;
            left_sibling = prev_node;
            right_sibling = Null;
            snk = CilElement.Null;
          }
        in
        let _ = L.debug "stmt deletion detected" in
        DeleteStmt (context, s1) :: fold_stmts2 parent (Some s1) ss1 []

  and extract_block parent block1 block2 =
    fold_stmts2 parent Option.none block1.Cil.bstmts block2.Cil.bstmts

  (* this is where global ends *)
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

  let rec make_diff_glob code prev next glob_lst =
    match glob_lst with
    | [] -> []
    | hd :: tl ->
        let context =
          {
            parent = Null;
            left_sibling = prev;
            right_sibling = next;
            snk = Null;
          }
        in
        if code = 0 then
          InsertGlobal (context, hd) :: make_diff_glob code prev next tl
        else DeleteGlobal (context, hd) :: make_diff_glob code prev next tl

  and fold_continue_point_glob glob1 glob2 es tl1 tl2 =
    match es with
    | [] -> failwith "fold_continue_point_glob: unexpected empty list"
    | hd :: _ -> (
        match hd with
        | InsertGlobal (_, g) ->
            fold_globals2 (Some g) tl1 (find_continue_point_glob glob1 tl2)
        | DeleteGlobal (_, g) ->
            fold_globals2 (Some g) (find_continue_point_glob glob2 tl1) tl2
        | _ -> fold_globals2 (Some glob1) tl1 tl2)

  and extract_global prev glob1 glob2 tl1 tl2 =
    let insertion = find_eq_glob_in_tl glob1 tl2 [] in
    if insertion <> [] then
      let _ = L.debug "global insertion detected" in
      let next = CilElement.glob_to_elem (Some (List.hd insertion)) in
      let insertion = glob2 :: List.tl insertion in
      make_diff_glob insertion_code prev next insertion
    else
      let deletion = find_eq_glob_in_tl glob2 tl1 [] in
      if deletion <> [] then
        let _ = L.debug "global deletion detected" in
        let next = CilElement.glob_to_elem (Some (List.hd deletion)) in
        let deletion = glob1 :: List.tl deletion in
        make_diff_glob deletion_code prev next deletion
      else
        let _ = L.debug "global insertion detected\nglobal deletion detected" in
        let context =
          {
            parent = Null;
            left_sibling = prev;
            right_sibling = CilElement.glob_to_elem (Some (List.hd tl1));
            snk = Null;
          }
        in
        [ InsertGlobal (context, glob2); DeleteGlobal (context, glob1) ]

  and get_diff_glob prev glob1 glob2 tl1 tl2 =
    match (glob1, glob2) with
    | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
        if H.eq_global glob1 glob2 then
          extract_block
            (CilElement.glob_to_elem (Some glob1))
            func_info1.sbody func_info2.sbody
        else extract_global prev glob1 glob2 tl1 tl2
    | Cil.GVarDecl _, Cil.GVarDecl _ ->
        if H.eq_global glob1 glob2 then []
        else extract_global prev glob1 glob2 tl1 tl2
    | _ -> extract_global prev glob1 glob2 tl1 tl2

  and fold_globals2 prev doner_gobals patch_globals =
    let prev_node = CilElement.glob_to_elem prev in
    match (doner_gobals, patch_globals) with
    | [], [] -> []
    | hd1 :: tl1, hd2 :: tl2 -> (
        let es = get_diff_glob prev_node hd1 hd2 tl1 tl2 in
        match es with
        | [] -> fold_globals2 (Some hd1) tl1 tl2
        | h :: t ->
            if t <> [] then
              match (h, List.hd t) with
              | InsertGlobal _, DeleteGlobal _ ->
                  es @ fold_globals2 (Some hd1) tl1 tl2
              | _ -> es @ fold_continue_point_glob hd1 hd2 es tl1 tl2
            else es @ fold_continue_point_glob hd1 hd2 es tl1 tl2)
    | [], hd2 :: tl2 ->
        let context =
          {
            parent = Null;
            left_sibling = prev_node;
            right_sibling = Null;
            snk = Null;
          }
        in
        let _ = L.debug "global insertion detected" in
        InsertGlobal (context, hd2) :: fold_globals2 prev [] tl2
    | hd1 :: tl1, [] ->
        let context =
          {
            parent = Null;
            left_sibling = prev_node;
            right_sibling = Null;
            snk = Null;
          }
        in
        let _ = L.debug "global deletion detected" in
        DeleteGlobal (context, hd1) :: fold_globals2 prev tl1 []

  let compare = compare
end

class blockVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vblock b =
      let stmts =
        List.fold_left
          (fun l stmt ->
            match stmt.Cil.skind with
            | Cil.Instr il when List.length il > 1 ->
                let new_il = List.map Cil.mkStmtOneInstr (List.tl il) in
                stmt.skind <- Instr [ List.hd il ];
                l @ (stmt :: new_il)
            | _ -> l @ [ stmt ])
          [] b.bstmts
      in
      b.bstmts <- stmts;
      ChangeDoChildrenPost (b, fun x -> x)
  end

let parse_file fname =
  if !Cilutil.printStages then ignore (Logger.info "Parsing %s\n" fname);
  let cil = Frontc.parse fname () in
  Rmtmps.removeUnusedTemps cil;
  Cil.visitCilFile (new blockVisitor) cil;
  cil

let define_diff donor_file patch_file =
  Diff.fold_globals2 Option.None donor_file.Cil.globals patch_file.Cil.globals
