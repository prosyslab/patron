open Core
open AbsDiff
module L = Logger
module Set = Stdlib.Set
module StrSet = Set.Make (String)

type t = Yojson.Safe.t

let string_of_ids ids = StrSet.fold (fun id s -> s ^ id ^ ", ") ids ""

let sbinop_to_sym op =
  match op with
  | SPlusA -> "PlusA"
  | SMinusA -> "MinusA"
  | SMult -> "Mult"
  | SDiv -> "Div"
  | SMod -> "Mod"
  | SLt -> "Lt"
  | SGt -> "Gt"
  | SLe -> "Le"
  | SGe -> "Ge"
  | SEq -> "Eq"
  | SNe -> "Ne"
  | SAnd -> "BAnd"
  | SXor -> "BXor"
  | SOr -> "BOr"
  | SLAnd -> "LAnd"
  | SLOr -> "LOr"
  | SShiftlt -> "Shiftlt"
  | SShiftrt -> "Shiftrt"
  | SPlusPI -> "PlusPI"
  | SIndexPI -> "IndexPI"
  | SMinusPI -> "MinusPI"
  | SMinusPP -> "MinusPP"

let rec styp_to_sym styp =
  match styp with
  | SVoid -> `String "void"
  | SInt -> `String "int"
  | SFloat -> `String "float"
  | SPtr t -> `Assoc [ ("ptr", styp_to_sym t) ]
  | SArray t -> `Assoc [ ("array", styp_to_sym t) ]
  | SNamed t ->
      let tname_json = ("tname", `String t.abs_tname) in
      let typ_json = ("typ", styp_to_sym t.abs_ttype) in
      `Assoc [ ("named", `Assoc [ tname_json; typ_json ]) ]
  | SFun (t, lst, b) ->
      let slist = match lst with Some lst -> lst | None -> [] in
      let typ_json = ("typ", styp_to_sym t) in
      let args_lst =
        List.fold_left
          ~f:(fun acc (s, ty) -> `String s :: styp_to_sym ty :: acc)
          ~init:[] slist
        |> List.rev
      in
      let args_json = ("args", `List args_lst) in
      let body_json = ("body", `Bool b) in
      `Assoc [ ("fun", `Assoc [ typ_json; args_json; body_json ]) ]
  | SComp c ->
      let cname_json = ("cname", `String c.cname) in
      let struct_json = ("struct", `Bool c.cstruct) in
      let comp_json = ("comp", `Assoc [ cname_json; struct_json ]) in
      `Assoc [ comp_json ]
  | _ -> L.error "styp_to_sym - not implemented"

let sunop_to_sym op = match op with SNot -> "LNot" | SNeg -> "Neg"

let rec mk_json_obj saction =
  match saction with
  | SInsertStmt (before, ss, after) ->
      let action_json = ("action", `String "insert_stmt") in
      let bn_id_lst = StrSet.fold (fun id l -> `String id :: l) before [] in
      let before_json = ("before", `List bn_id_lst) in
      let an_id_lst = StrSet.fold (fun id l -> `String id :: l) after [] in
      let after_json = ("after", `List an_id_lst) in
      let change_json = ("change", `List (List.map ~f:sstmt_to_json ss)) in
      `Assoc [ action_json; before_json; change_json; after_json ]
  | SDeleteStmt s ->
      let action_json = ("action", `String "delete_stmt") in
      let change_json = ("change", `String s) in
      `Assoc [ action_json; change_json ]
  | SUpdateStmt (before, ss, after) ->
      let action_json = ("action", `String "update_stmt") in
      let bn_id_lst = StrSet.fold (fun id l -> `String id :: l) before [] in
      let before_json = ("before", `List bn_id_lst) in
      let an_id_lst = StrSet.fold (fun id l -> `String id :: l) after [] in
      let after_json = ("after", `List an_id_lst) in
      let change_json = ("change", `List (List.map ~f:sstmt_to_json ss)) in
      `Assoc [ action_json; before_json; change_json; after_json ]
  | SUpdateExp (_, e1, e2) ->
      let action_json = ("action", `String "update_exp") in
      let change_json =
        ( "change",
          `Assoc [ ("before", sexp_to_json e1); ("after", sexp_to_json e2) ] )
      in
      `Assoc [ action_json; change_json ]
  | _ -> L.error "mk_json_obj - not implemented"

and sexps_to_json lst =
  `List
    (List.fold_left ~f:(fun acc x -> sexp_to_json x :: acc) ~init:[] lst
    |> List.rev)

and sstmts_to_json lst =
  `List
    (List.fold_left ~f:(fun acc x -> sstmt_to_json x :: acc) ~init:[] lst
    |> List.rev)

and sstmt_to_json (sstmt : abs_node) =
  let node = sstmt.ast in
  let stmt =
    match node with
    | AbsStmt (s, _) -> s
    | _ -> L.error "sstmt_to_json - undefined AbsStmt"
  in
  match stmt with
  | SIf (exp1, tb1, eb1) ->
      let cond_json = ("cond", sexp_to_json exp1) in
      let then_json = ("then", sstmts_to_json tb1) in
      let else_json = ("else", sstmts_to_json eb1) in
      let node_json = ("node", `Assoc [ cond_json; then_json; else_json ]) in
      let id_json = ("ids", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let if_json = ("if", `Assoc [ node_json; id_json; literal_json ]) in
      `Assoc [ if_json ]
  | SSet (lv1, e1) ->
      let lval_json = ("lval", slval_to_json lv1) in
      let exp_json = ("exp", sexp_to_json e1) in
      let node_json = ("node", `Assoc [ lval_json; exp_json ]) in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let set_json = ("set", `Assoc [ node_json; id_json; literal_json ]) in
      `Assoc [ set_json ]
  | SCall (Some lv1, e1, es1) ->
      let lval_json = ("lval", slval_to_json lv1) in
      let exp_json = ("exp", sexp_to_json e1) in
      let exps_json = ("exps", sexps_to_json es1) in
      let node_json = ("node", `Assoc [ lval_json; exp_json; exps_json ]) in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let call_json = ("call", `Assoc [ node_json; id_json; literal_json ]) in
      `Assoc [ call_json ]
  | SCall (None, e1, es1) ->
      let lval_json = ("lval", `String "None") in
      let exp_json = ("exp", sexp_to_json e1) in
      let exps_json = ("exps", sexps_to_json es1) in
      let node_json = ("node", `Assoc [ lval_json; exp_json; exps_json ]) in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let call_json = ("call", `Assoc [ node_json; id_json; literal_json ]) in
      `Assoc [ call_json ]
  | SReturn (Some e1) ->
      let exp_json = ("exp", sexp_to_json e1) in
      let node_json = ("node", `Assoc [ exp_json ]) in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let return_json =
        ("return", `Assoc [ node_json; id_json; literal_json ])
      in
      `Assoc [ return_json ]
  | SReturn None ->
      let exp_json = ("exp", `String "None") in
      let node_json = ("node", `Assoc [ exp_json ]) in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let return_json =
        ("return", `Assoc [ node_json; id_json; literal_json ])
      in
      `Assoc [ return_json ]
  | SGoto s1 ->
      let stmt_json = ("stmt", sstmt_to_json s1) in
      let node_json = ("node", `Assoc [ stmt_json ]) in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let goto_json = ("goto", `Assoc [ node_json; id_json; literal_json ]) in
      `Assoc [ goto_json ]
  | SBreak ->
      let node_json = ("node", `String "break") in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let break_json = ("break", `Assoc [ node_json; id_json; literal_json ]) in
      `Assoc [ break_json ]
  | SContinue ->
      let node_json = ("node", `String "continue") in
      let id_json = ("id", `String (string_of_ids sstmt.ids)) in
      let literal_json = ("literal", `String sstmt.literal) in
      let continue_json =
        ("continue", `Assoc [ node_json; id_json; literal_json ])
      in
      `Assoc [ continue_json ]
  | _ -> `Null

and sexp_to_json sexp =
  let node = sexp.ast in
  let exp =
    match node with
    | AbsExp (e, _) -> e
    | _ -> L.error "sexp_to_json - undefined AbsExp"
  in
  match exp with
  | SConst const ->
      let const_json = ("const", sconst_to_json const) in
      let node_json = ("node", `Assoc [ const_json ]) in
      let id_json = ("ids", `String (string_of_ids sexp.ids)) in
      let literal_json = ("literal", `String sexp.literal) in
      `Assoc [ node_json; id_json; literal_json ]
  | SELval l -> `Assoc [ ("lval", slval_to_json l) ]
  | SSizeOfE e1 ->
      let e_json = ("exp", sexp_to_json e1) in
      let sizeof_json = ("sizeof", `Assoc [ e_json ]) in
      let node_json = ("node", `Assoc [ sizeof_json ]) in
      let id_json = ("id", `String (string_of_ids sexp.ids)) in
      let literal_json = ("literal", `String sexp.literal) in
      `Assoc [ node_json; id_json; literal_json ]
  | SBinOp (op1, e1_1, e2_1, typ1) ->
      let op_json = ("op", `String (sbinop_to_sym op1)) in
      let typ_json = ("typ", styp_to_sym typ1) in
      let e1_json = ("e1", sexp_to_json e1_1) in
      let e2_json = ("e2", sexp_to_json e2_1) in
      let binop_json =
        ("binop", `Assoc [ op_json; typ_json; e1_json; e2_json ])
      in
      let node_json = ("node", `Assoc [ binop_json ]) in
      let id_json = ("id", `String (string_of_ids sexp.ids)) in
      let literal_json = ("literal", `String sexp.literal) in
      `Assoc [ node_json; id_json; literal_json ]
  | SCastE (typ, e1) ->
      let typ_json = ("typ", styp_to_sym typ) in
      let e_json = ("e", sexp_to_json e1) in
      let cast_json = ("cast", `Assoc [ typ_json; e_json ]) in
      let node_json = ("node", `Assoc [ cast_json ]) in
      let id_json = ("id", `String (string_of_ids sexp.ids)) in
      let literal_json = ("literal", `String sexp.literal) in
      `Assoc [ node_json; id_json; literal_json ]
  | SUnOp (op1, e1_1, typ1) ->
      let op_json = ("op", `String (sunop_to_sym op1)) in
      let typ_json = ("typ", styp_to_sym typ1) in
      let e_json = ("e", sexp_to_json e1_1) in
      let unop_json = ("unop", `Assoc [ op_json; typ_json; e_json ]) in
      let node_json = ("node", `Assoc [ unop_json ]) in
      let id_json = ("id", `String (string_of_ids sexp.ids)) in
      let literal_json = ("literal", `String sexp.literal) in
      `Assoc [ node_json; id_json; literal_json ]
  | _ ->
      pp_absExp Format.std_formatter exp;
      L.error "sexp_to_json - undefined AbsExp"

and slval_to_json slval =
  let node = slval.ast in
  let lval =
    match node with
    | AbsLval (l, _) -> l
    | _ -> L.error "slval_to_json - undefined AbsLval"
  in
  match lval with
  | SLNull -> `Null
  | Lval (lhost, offset) ->
      let lhost_json = ("lhost", slhost_to_json lhost) in
      let offset_json = ("offset", soffset_to_json offset) in
      let lval_json = ("lval", `Assoc [ lhost_json; offset_json ]) in
      let node_json = ("node", `Assoc [ lval_json ]) in
      let id_json = ("id", `String (string_of_ids slval.ids)) in
      let literal_json = ("literal", `String slval.literal) in
      `Assoc [ node_json; id_json; literal_json ]

and slhost_to_json lhost =
  match lhost with
  | SVar v ->
      let name_json = ("name", `String v.vname) in
      let typ_json = ("typ", styp_to_sym v.vtype) in
      `Assoc [ ("var", `Assoc [ name_json; typ_json ]) ]
  | SMem e -> `Assoc [ ("mem", `Assoc [ ("exp", sexp_to_json e) ]) ]

and soffset_to_json offset =
  match offset with
  | SNoOffset -> `String "nooffset"
  | SField (f, o) ->
      let field_json = ("field", sfield_to_json f) in
      let offset_json = ("offset", soffset_to_json o) in
      `Assoc [ ("field", `Assoc [ field_json; offset_json ]) ]
  | SIndex (e, o) ->
      let exp_json = ("exp", sexp_to_json e) in
      let offset_json = ("offset", soffset_to_json o) in
      `Assoc [ ("index", `Assoc [ exp_json; offset_json ]) ]

and sfield_to_json f =
  let comp_json = ("comp", scomp_to_json f.fcomp) in
  let name_json = ("name", `String f.fname) in
  let typ_json = ("typ", styp_to_sym f.ftype) in
  `Assoc [ ("field", `Assoc [ comp_json; name_json; typ_json ]) ]

and scomp_to_json c =
  let name_json = ("name", `String c.cname) in
  let struct_json = ("struct", `Bool c.cstruct) in
  `Assoc [ ("comp", `Assoc [ name_json; struct_json ]) ]

and sconst_to_json sconst =
  match sconst with
  | SIntConst i ->
      let type_json = ("type", `String "int") in
      let literal_json = ("literal", `String (Int.to_string i)) in
      `Assoc [ type_json; literal_json ]
  | SFloatConst f ->
      let type_json = ("type", `String "float") in
      let literal_json = ("literal", `String (Float.to_string f)) in
      `Assoc [ type_json; literal_json ]
  | SStringConst s ->
      let type_json = ("type", `String "str") in
      let literal_json = ("literal", `String s) in
      `Assoc [ type_json; literal_json ]
  | SCharConst c ->
      let type_json = ("type", `String "char") in
      let literal_json = ("literal", `String (String.make 1 c)) in
      `Assoc [ type_json; literal_json ]

let dump abs_diff out_dir =
  let oc_diff_json = Stdlib.open_out (out_dir ^ "/diff.json") in
  let rec make_json (id : int) abs_diff acc =
    match abs_diff with
    | [] -> acc
    | s_action :: s_rest ->
        let json_obj = mk_json_obj s_action in
        if Yojson.equal json_obj `Null then make_json id abs_diff acc
        else
          let acc = ("diff-" ^ string_of_int id, json_obj) :: acc in
          make_json (id + 1) s_rest acc
  in
  let actions = `Assoc (List.rev (make_json 0 abs_diff [])) in
  let json_obj = `Assoc [ ("diffs", actions) ] in
  Yojson.Safe.pretty_to_channel oc_diff_json json_obj;
  Stdlib.close_out oc_diff_json
