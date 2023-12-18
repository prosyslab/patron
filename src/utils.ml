module J = Yojson.Basic.Util
module F = Format
module StrMap = Map.Make (String)

module ExpMap = Map.Make (struct
  type t = Cil.exp

  let compare = compare
end)

module LvalMap = Map.Make (struct
  type t = Cil.lval

  let compare = compare
end)

type stmt_info = {
  stmt : Cil.stmt;
  lvals : string LvalMap.t;
  exps : string ExpMap.t;
}

type stmt_info_rev = {
  stmt : Cil.stmt;
  lvals : Cil.lval StrMap.t;
  exps : Cil.exp StrMap.t;
}

module InfoMap = Map.Make (struct
  type t = stmt_info

  let compare = compare
end)

let eq_tmpvar str1 str2 =
  let type1 = Str.regexp "in[0-9]+" in
  let type2 = Str.regexp "tmp___[0-9]+" in
  let type3 = Str.regexp "c[0-9]+" in
  let type4 = Str.regexp "v[0-9]+" in
  let type5 = Str.regexp "ret_.*[0-9]+" in
  let type6 = Str.regexp "val[0-9]+" in
  let type7 = Str.regexp "ptr[0-9]+" in
  let type8 = Str.regexp "__cil_tmp[0-9]+" in
  let type9 = Str.regexp "tmp[0-9]+" in
  let regex_lst =
    [ type1; type2; type3; type4; type5; type6; type7; type8; type9 ]
  in
  let rec aux regex_lst =
    match regex_lst with
    | [] -> false
    | hd :: tl ->
        if Str.string_match hd str1 0 && Str.string_match hd str2 0 then true
        else aux tl
  in
  aux regex_lst

let print_ekind exp =
  match exp with
  | Cil.Const _ -> print_endline "Const"
  | Cil.Lval _ -> print_endline "Lval"
  | Cil.SizeOf _ -> print_endline "SizeOf"
  | Cil.SizeOfE _ -> print_endline "SizeOfE"
  | Cil.SizeOfStr _ -> print_endline "SizeOfStr"
  | Cil.AlignOf _ -> print_endline "AlignOf"
  | Cil.AlignOfE _ -> print_endline "AlignOfE"
  | Cil.UnOp _ -> print_endline "UnOp"
  | Cil.BinOp _ -> print_endline "BinOp"
  | Cil.Question _ -> print_endline "Question"
  | Cil.CastE _ -> print_endline "CastE"
  | Cil.AddrOf _ -> print_endline "AddrOf"
  | Cil.AddrOfLabel _ -> print_endline "AddrOfLabel"
  | Cil.StartOf _ -> print_endline "StartOf"

(* pp functions *)

let summarize_pp str =
  let sp = Str.split (Str.regexp "\n") str in
  try List.hd sp with _ -> str

let string_of_file file = Cil.dumpFile !Cil.printerForMaincil stdout "" file

let string_of_global global =
  Cil.printGlobal !Cil.printerForMaincil () global |> Pretty.sprint ~width:80

let string_of_instr instr =
  Cil.printInstr !Cil.printerForMaincil () instr |> Pretty.sprint ~width:80

let string_of_stmt stmt =
  Cil.printStmt !Cil.printerForMaincil () stmt |> Pretty.sprint ~width:80

let string_of_exp exp = Cil.d_exp () exp |> Pretty.sprint ~width:80
let string_of_typ typ = Cil.d_type () typ |> Pretty.sprint ~width:80
let string_of_lval lval = Cil.d_lval () lval |> Pretty.sprint ~width:80
let string_of_constant const = Cil.d_const () const |> Pretty.sprint ~width:80

let print_bool b =
  if b = true then print_endline "true" else print_endline "false"

let eq_var s1 s2 = if not (eq_tmpvar s1 s2) then s1 = s2 else true

let eq_stmt_conc s1 s2 =
  let s1_str = string_of_stmt s1 in
  let s2_str = string_of_stmt s2 in
  s1_str = s2_str

let eq_exp_conc e1 e2 =
  let e1_str = string_of_exp e1 in
  let e2_str = string_of_exp e2 in
  eq_var e1_str e2_str

let eq_lval_conc l1 l2 =
  let l1_str = string_of_lval l1 in
  let l2_str = string_of_lval l2 in
  eq_var l1_str l2_str

let eq_typ typ_info1 typ_info2 =
  match (typ_info1, typ_info2) with
  | Cil.TVoid _, Cil.TVoid _
  | Cil.TInt _, Cil.TInt _
  | Cil.TFloat _, Cil.TFloat _
  | Cil.TPtr _, Cil.TPtr _
  | Cil.TArray _, Cil.TArray _
  | Cil.TFun _, Cil.TFun _
  | Cil.TNamed _, Cil.TNamed _
  | Cil.TComp _, Cil.TComp _
  | Cil.TEnum _, Cil.TEnum _ ->
      true
  | _ -> string_of_typ typ_info1 = string_of_typ typ_info2

let rec eq_exp (a : Cil.exp) (b : Cil.exp) =
  match (a, b) with
  | Lval (Var a, NoOffset), Lval (Var b, NoOffset) -> eq_var a.vname b.vname
  | Lval (Mem a, NoOffset), Lval (Mem b, NoOffset) -> eq_exp a b
  | BinOp (a, b, c, _), BinOp (d, e, f, _) -> a = d && eq_exp b e && eq_exp c f
  | UnOp (a, b, _), UnOp (c, d, _) -> a = c && eq_exp b d
  | CastE (a, b), CastE (c, d) -> eq_typ a c && eq_exp b d
  | AddrOf (Var a, NoOffset), AddrOf (Var b, NoOffset) -> eq_var a.vname b.vname
  | AddrOf (Mem a, NoOffset), AddrOf (Mem b, NoOffset) -> eq_exp a b
  | StartOf (Var a, NoOffset), StartOf (Var b, NoOffset) ->
      eq_var a.vname b.vname
  | StartOf (Mem a, NoOffset), StartOf (Mem b, NoOffset) -> eq_exp a b
  | Cil.SizeOfE a, Cil.SizeOfE b -> eq_exp a b
  | Const a, Const b -> a = b
  | Lval (Var a, NoOffset), StartOf (Var b, NoOffset)
  | StartOf (Var a, NoOffset), Lval (Var b, NoOffset) ->
      eq_var a.vname b.vname
  | Question (a, b, c, _), Question (d, e, f, _) ->
      eq_exp a d && eq_exp b e && eq_exp c f
  | _ -> eq_exp_conc a b

let eq_lval (l1 : Cil.lval) (l2 : Cil.lval) =
  match (l1, l2) with
  | (host1, _), (host2, _) -> (
      match (host1, host2) with
      | Var vinfo1, Var vinfo2 ->
          eq_var vinfo1.vname vinfo2.vname && eq_typ vinfo1.vtype vinfo2.vtype
      | Mem mem1, Mem mem2 -> eq_exp mem1 mem2
      | _ -> false)

let eq_instr i1 i2 =
  if i1 = [] && i2 = [] then true
  else if i1 = [] || i2 = [] then false
  else
    let instr1 = List.hd i1 in
    let instr2 = List.hd i2 in
    match (instr1, instr2) with
    | Cil.Set (lv1, _, _), Cil.Set (lv2, _, _) -> eq_lval lv1 lv2
    | Cil.Call (lv1, _, _, _), Cil.Call (lv2, _, _, _) -> (
        match (lv1, lv2) with
        | None, None -> true
        | Some lv1, Some lv2 -> eq_lval_conc lv1 lv2
        | _ -> false)
    | Cil.Asm _, Cil.Asm _ -> true
    | _ -> false

let rec eq_stmt skind1 skind2 =
  match (skind1, skind2) with
  | Cil.Instr i1, Cil.Instr i2 -> eq_instr i1 i2
  | Cil.Return (Some e1, _), Cil.Return (Some e2, _) -> eq_exp_conc e1 e2
  | Cil.Return (None, _), Cil.Return (None, _) -> true
  | Cil.Goto (dest1, _), Cil.Goto (dest2, _) ->
      if eq_stmt !dest1.skind !dest2.skind then true else false
  | Cil.If (cond1, _, _, _), Cil.If (cond2, _, _, _) -> eq_exp cond1 cond2
  | Cil.Loop _, Cil.Loop _
  | Cil.ComputedGoto _, Cil.ComputedGoto _
  | Cil.Block _, Cil.Block _
  | Cil.TryExcept _, Cil.TryExcept _
  | Cil.TryFinally _, Cil.TryFinally _
  | Cil.Break _, Cil.Break _
  | Cil.Continue _, Cil.Continue _ ->
      true
  | _ -> false

let eq_stmt_line sk1 sk2 =
  match (sk1, sk2) with
  | Cil.Instr i1, Cil.Instr i2 -> (
      if i1 = [] || i2 = [] then false
      else
        match (List.hd i1, List.hd i2) with
        | Cil.Set (_, _, loc), Cil.Set (_, _, loc2) -> loc.line = loc2.line
        | Cil.Call (_, _, _, loc), Cil.Call (_, _, _, loc2) ->
            loc.line = loc2.line
        | _ -> false)
  | Cil.Return (_, loc), Cil.Return (_, loc') -> loc.line = loc'.line
  | Cil.Goto (_, loc), Cil.Goto (_, loc') -> loc.line = loc'.line
  | Cil.If (_, _, _, loc), Cil.If (_, _, _, loc') -> loc.line = loc'.line
  | Cil.Loop (_, loc, _, _), Cil.Loop (_, loc', _, _) -> loc.line = loc'.line
  | Cil.ComputedGoto (_, loc), Cil.ComputedGoto (_, loc') ->
      loc.line = loc'.line
  | Cil.Block _, Cil.Block _ -> false
  | Cil.TryExcept (_, _, _, loc), Cil.TryExcept (_, _, _, loc') ->
      loc.line = loc'.line
  | Cil.TryFinally (_, _, loc), Cil.TryFinally (_, _, loc') ->
      loc.line = loc'.line
  | Cil.Break loc, Cil.Break loc' -> loc.line = loc'.line
  | Cil.Continue loc, Cil.Continue loc' -> loc.line = loc'.line
  | _ -> false

let eq_global glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      eq_typ func_info1.svar.vtype func_info2.svar.vtype
      && func_info1.svar.vname = func_info2.svar.vname
  | Cil.GType (typinfo1, _), Cil.GType (typinfo2, _) ->
      typinfo1.tname = typinfo2.tname && eq_typ typinfo1.ttype typinfo2.ttype
  | Cil.GCompTag _, Cil.GCompTag _
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _
  | Cil.GEnumTag _, Cil.GEnumTag _
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _ ->
      true
  | Cil.GVarDecl (v1, _), Cil.GVarDecl (v2, _) -> v1.vname = v2.vname
  | Cil.GVar _, Cil.GVar _
  | Cil.GAsm _, Cil.GAsm _
  | Cil.GPragma _, Cil.GPragma _
  | Cil.GText _, Cil.GText _ ->
      true
  | _ -> false

let remove_comments globs =
  List.rev
    (List.fold_left
       (fun acc glob -> match glob with Cil.GText _ -> acc | _ -> glob :: acc)
       [] globs)

let eq_stmt_kind skind1 skind2 =
  match (skind1, skind2) with
  | Cil.Instr _, Cil.Instr _
  | Cil.Return _, Cil.Return _
  | Cil.Goto _, Cil.Goto _
  | Cil.ComputedGoto _, Cil.ComputedGoto _
  | Cil.Break _, Cil.Break _
  | Cil.Continue _, Cil.Continue _
  | Cil.If _, Cil.If _
  | Cil.Loop _, Cil.Loop _
  | Cil.Block _, Cil.Block _
  | Cil.TryExcept _, Cil.TryExcept _
  | Cil.TryFinally _, Cil.TryFinally _ ->
      true
  | _ -> false

let print_exp_type exp =
  match exp with
  | Cil.Lval _ -> print_endline "Lval"
  | Cil.SizeOf _ -> print_endline "SizeOf"
  | Cil.SizeOfE _ -> print_endline "SizeOfE"
  | Cil.SizeOfStr _ -> print_endline "SizeOfStr"
  | Cil.AlignOf _ -> print_endline "AlignOf"
  | Cil.AlignOfE _ -> print_endline "AlignOfE"
  | Cil.UnOp _ -> print_endline "UnOp"
  | Cil.BinOp _ -> print_endline "BinOp"
  | Cil.Question _ -> print_endline "Question"
  | Cil.CastE _ -> print_endline "CastE"
  | Cil.AddrOf _ -> print_endline "AddrOf"
  | Cil.AddrOfLabel _ -> print_endline "AddrOfLabel"
  | Cil.StartOf _ -> print_endline "StartOf"
  | Cil.Const _ -> print_endline "Const"

let eq_global_type glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GType _, Cil.GType _
  | Cil.GCompTag _, Cil.GCompTag _
  | Cil.GCompTagDecl _, Cil.GCompTagDecl _
  | Cil.GEnumTag _, Cil.GEnumTag _
  | Cil.GEnumTagDecl _, Cil.GEnumTagDecl _
  | Cil.GVar _, Cil.GVar _
  | Cil.GVarDecl _, Cil.GVarDecl _
  | Cil.GFun _, Cil.GFun _
  | Cil.GAsm _, Cil.GAsm _
  | Cil.GPragma _, Cil.GPragma _ ->
      true
  | _ -> false

let print_global_type glob =
  match glob with
  | Cil.GType _ -> print_endline "GType"
  | Cil.GCompTag _ -> print_endline "GCompTag"
  | Cil.GCompTagDecl _ -> print_endline "GCompTagDecl"
  | Cil.GEnumTag _ -> print_endline "GEnumTag"
  | Cil.GEnumTagDecl _ -> print_endline "GEnumTagDecl"
  | Cil.GVar _ -> print_endline "GVar"
  | Cil.GVarDecl _ -> print_endline "GVarDecl"
  | Cil.GFun _ -> print_endline "GFun"
  | Cil.GAsm _ -> print_endline "GAsm"
  | Cil.GPragma _ -> print_endline "GPragma"
  | _ -> print_endline "Other"

let trim_node_str str =
  Str.global_replace (Str.regexp " ") ""
    (Str.global_replace (Str.regexp "?") "\\\\"
       (Str.global_replace (Str.regexp "\\\\") ""
          (Str.global_replace (Str.regexp "\\\\\\") "?" str)))

let explode s =
  let rec exp i l = if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []

let rev =
  let rec rev_append acc l =
    match l with [] -> acc | h :: t -> rev_append (h :: acc) t
  in
  fun l -> rev_append [] l

let rec search_seq s1 s2 =
  match s2 with
  | [] -> true
  | hd :: tl ->
      let rec search s1 s2 =
        match s1 with
        | [] -> false
        | hd1 :: tl1 -> if hd1 = hd then search_seq tl1 tl else search tl1 s2
      in
      search s1 s2

(* is s2 in s1? *)
let subset s1 s2 =
  let simplify s =
    Str.global_replace (Str.regexp "->") "" s
    |> Str.global_replace (Str.regexp " ") ""
    |> Str.global_replace (Str.regexp "(") ""
    |> Str.global_replace (Str.regexp ")") ""
  in
  let s1 = simplify s1 in
  let s2 = simplify s2 in
  let set1 = explode s1 in
  let set2 = explode s2 in
  search_seq set1 set2

let print_ikind instr =
  match instr with
  | Cil.Call _ -> print_endline "Call"
  | Cil.Set _ -> print_endline "Set"
  | Cil.Asm _ -> print_endline "Asm"

let pp_skind sk =
  match sk with
  | Cil.Instr _ -> "Instr"
  | Cil.Return _ -> "Return"
  | Cil.Goto _ -> "Goto"
  | Cil.ComputedGoto _ -> "ComputedGoto"
  | Cil.Break _ -> "Break"
  | Cil.Continue _ -> "Continue"
  | Cil.If _ -> "If"
  | Cil.Loop _ -> "Loop"
  | Cil.Block _ -> "Block"
  | Cil.TryExcept _ -> "TryExcept"
  | Cil.TryFinally _ -> "TryFinally"
  | Cil.Switch _ -> "Switch"

let rec parse_strmap file map =
  match file with
  | [] -> map
  | hd :: tl ->
      let splited = Str.split (Str.regexp "\t") hd in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      parse_strmap tl
        (StrMap.add
           (Str.global_replace (Str.regexp " ") "" (trim_node_str key))
           (Str.global_replace (Str.regexp " ") "" (trim_node_str value))
           map)

let contains s1 s2 =
  let re = Str.regexp_string s2 in
  try
    ignore (Str.search_forward re s1 0);
    true
  with Not_found -> false

let print_map_exp map =
  StrMap.iter
    (fun k v ->
      print_string "\t";
      print_string (k ^ " -> ");
      print_string (string_of_exp v);
      print_endline "")
    map

let print_map_str map =
  StrMap.iter
    (fun k v ->
      print_string "\t";
      print_string (k ^ " -> ");
      print_string v;
      print_endline "")
    map

let read_lines name =
  let file = open_in name in
  let rec read_lines acc =
    match input_line file with
    | line -> read_lines (line :: acc)
    | exception End_of_file -> List.rev acc
  in
  let lines = read_lines [] in
  close_in file;
  lines

let make_str_map_rev path =
  let lines = read_lines path in
  List.fold_left
    (fun map line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      StrMap.add value key map)
    StrMap.empty lines

let make_cil_str_map path =
  let lines = read_lines path in
  List.fold_left
    (fun map line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      StrMap.add (trim_node_str value) (trim_node_str key) map)
    StrMap.empty lines

let append_before_elt_exp elt exp lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_exp elt = string_of_exp hd then aux (elt :: exp :: acc) tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst + 1 then result
  else failwith "exp_list append error"

let append_after_elt_exp elt exp lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_exp elt = string_of_exp hd then aux (exp :: elt :: acc) tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst + 1 then result
  else failwith "exp_list append error"

let append_before_elt_stmt elt stmt lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_stmt elt = string_of_stmt hd then
          aux (elt :: stmt :: acc) tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst + 1 then result
  else failwith "stmt_list append error"

let append_after_elt_stmt elt stmt lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_stmt elt = string_of_stmt hd then
          aux (stmt :: elt :: acc) tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst + 1 then result
  else failwith "stmt_list append error"

let delete_elt_stmt elt list =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_stmt elt = string_of_stmt hd then aux acc tl
        else aux (hd :: acc) tl
  in
  let result = aux [] list in
  if List.length result = List.length list - 1 then result
  else failwith "stmt_list delete error"

let delete_before_elt_stmt elt lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_stmt elt = string_of_stmt hd then
          let new_acc = match acc with [] -> [] | _ :: tl -> tl in
          aux (elt :: new_acc) tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst - 1 then result
  else failwith "stmt_list delete error"

let delete_after_elt_stmt elt lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_stmt elt = string_of_stmt hd then
          let new_tl = match tl with [] -> [] | _ :: tl -> tl in
          aux (elt :: acc) new_tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst - 1 then result
  else failwith "stmt_list delete error"

let delete_elt_exp elt list =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_exp elt = string_of_exp hd then aux acc tl
        else aux (hd :: acc) tl
  in
  let result = aux [] list in
  if List.length result = List.length list - 1 then result
  else failwith "exp_list delete error"

let delete_before_elt_exp elt lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_exp elt = string_of_exp hd then
          let new_acc = match acc with [] -> [] | _ :: tl -> tl in
          aux (elt :: new_acc) tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst - 1 then result
  else failwith "exp_list delete error"

let delete_after_elt_exp elt lst =
  let rec aux acc = function
    | [] -> List.rev acc
    | hd :: tl ->
        if string_of_exp elt = string_of_exp hd then
          let new_tl = match tl with [] -> [] | _ :: tl -> tl in
          aux (elt :: acc) new_tl
        else aux (hd :: acc) tl
  in
  let result = aux [] lst in
  if List.length result = List.length lst - 1 then result
  else failwith "exp_list delete error"

let parse_facts facts_path =
  let lines = read_lines facts_path in
  List.fold_left
    (fun map line ->
      let keyval = Str.split (Str.regexp "\t") line in
      let id = List.hd keyval in
      let elmt = List.tl keyval in
      StrMap.add id elmt map)
    StrMap.empty lines

let parse_map path map =
  let path = path ^ "/Exp.map" in
  let lines = read_lines path in
  List.iter
    (fun line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      Hashtbl.add map key value)
    lines

let parse_call_facts facts_path =
  let lines = read_lines facts_path in
  List.fold_left
    (fun map line ->
      let keyval = Str.split (Str.regexp "\t") line in
      let id = List.hd keyval in
      let arg = List.nth keyval 2 in
      if not (String.contains arg 'C') then map
      else StrMap.add id (List.tl keyval) map)
    StrMap.empty lines

let parse_args_facts facts_path =
  let lines = read_lines facts_path in
  let result =
    List.fold_left
      (fun map line ->
        let keyval = Str.split (Str.regexp "\t") line in
        let id = List.hd keyval in
        match StrMap.find_opt id map with
        | None -> StrMap.add id [ List.nth keyval 1 ] map
        | Some lst ->
            StrMap.update id (fun _ -> Some (List.nth keyval 1 :: lst)) map)
      StrMap.empty lines
  in
  StrMap.map (fun lst -> List.rev lst) result

let parse_node_json sparrow_dir =
  let file = Yojson.Basic.from_file (sparrow_dir ^ "/node.json") in
  let nodes = J.member "nodes" file in
  let key_list = J.keys nodes in
  List.fold_left
    (fun acc key ->
      let cont = J.member key nodes in
      let cmd =
        J.to_list (J.member "cmd" cont)
        |> List.fold_left
             (fun acc y ->
               try J.to_string y :: acc
               with _ -> (
                 try
                   let bool = J.to_bool y in
                   if bool then "true" :: acc else "false" :: acc
                 with _ -> "null" :: acc))
             []
        |> List.rev
      in
      let loc = J.member "loc" cont |> J.to_string in
      (key, cmd, loc) :: acc)
    [] key_list

let cil_stmts = ref []

class copyStmtVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vstmt stmt =
      cil_stmts := stmt :: !cil_stmts;
      DoChildren
  end

let stmt_lst = ref []
let target_func = ref ""

class functionVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vfunc func =
      if func.svar.vname = !target_func then (
        stmt_lst := func.sbody.bstmts;
        SkipChildren)
      else DoChildren
  end

let extract_target_func_stmt_lst file target =
  target_func := target;
  let vis = new functionVisitor in
  ignore (Cil.visitCilFile vis file);
  !stmt_lst

let extract_node file =
  cil_stmts := [];
  let vis = new copyStmtVisitor in
  ignore (Cil.visitCilFile vis file);
  (file.globals, !cil_stmts)

let extract_stmts file =
  cil_stmts := [];
  let vis = new copyStmtVisitor in
  ignore (Cil.visitCilFile vis file);
  !cil_stmts

let is_empty_instr stmt =
  match stmt.Cil.skind with Cil.Instr [] -> true | _ -> false

let print_info (info : stmt_info) =
  print_endline (string_of_stmt info.stmt);
  ExpMap.iter
    (fun exp e -> print_endline ("\t" ^ string_of_exp exp ^ " -> " ^ e))
    info.exps;
  LvalMap.iter
    (fun lval lv -> print_endline ("\t" ^ string_of_lval lval ^ " -> " ^ lv))
    info.lvals

let print_info_map info_map =
  InfoMap.iter
    (fun info id ->
      print_endline id;
      print_info info)
    info_map

let get_info_key stmt cil_map =
  let lst =
    InfoMap.fold
      (fun key _ acc -> if key.stmt = stmt then key :: acc else acc)
      cil_map []
  in
  List.hd lst

let rev_expmap map =
  ExpMap.fold (fun k v acc -> StrMap.add v k acc) map StrMap.empty

let rev_lvalmap map =
  LvalMap.fold (fun k v acc -> StrMap.add v k acc) map StrMap.empty

let extract_snk path =
  let lst = read_lines path in
  let donee_srcsnk = List.nth lst 1 in
  let donee_srcsnk = Str.split (Str.regexp " ") donee_srcsnk in
  List.nth donee_srcsnk 1

let compare_files (file1 : Cil.file) (file2 : Cil.file) =
  string_of_file file1 = string_of_file file2

let get_first_nth_lines n str =
  let rec aux acc n str =
    if n = 0 then List.rev acc
    else
      let idx = String.index str '\n' in
      let line = String.sub str 0 idx in
      let str = String.sub str (idx + 1) (String.length str - idx - 1) in
      aux (line :: acc) (n - 1) str
  in
  aux [] n str

let flip f y x = f x y
let list_fold f list init = List.fold_left (flip f) init list
let link_by_sep sep s acc = if acc = "" then s else acc ^ sep ^ s

let string_of_list ?(first = "[") ?(last = "]") ?(sep = ";") string_of_v list =
  let add_string_of_v v acc = link_by_sep sep (string_of_v v) acc in
  first ^ list_fold add_string_of_v list "" ^ last

let get_loc_filename (loc : Cil.location) =
  try
    let idx = String.rindex loc.file '/' in
    let len = String.length loc.file in
    String.sub loc.file (idx + 1) (len - idx - 1)
  with _ -> loc.file

let get_loc_line (loc : Cil.location) = loc.line

let get_global_loc glob =
  match glob with
  | Cil.GFun (_, loc)
  | Cil.GVar (_, _, loc)
  | Cil.GType (_, loc)
  | Cil.GCompTag (_, loc)
  | Cil.GCompTagDecl (_, loc)
  | Cil.GEnumTag (_, loc)
  | Cil.GEnumTagDecl (_, loc)
  | Cil.GVarDecl (_, loc)
  | Cil.GAsm (_, loc)
  | Cil.GPragma (_, loc) ->
      loc
  | _ -> failwith "get_global_loc error"

let s_location (loc : Cil.location) =
  get_loc_filename loc ^ ":" ^ string_of_int loc.line

let get_target_file target_dir =
  Sys.readdir target_dir |> Array.to_list
  |> List.filter (fun x -> Filename.check_suffix x ".c")
  |> List.hd |> Filename.concat target_dir

let parse_model path =
  let lines = read_lines path in
  List.fold_left
    (fun map line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      (key, value) :: map)
    [] lines

module SparrowParser = struct
  open Cil

  let tostring s = Escape.escape_string (Pretty.sprint ~width:0 s)

  let rec s_exps es = string_of_list ~first:"(" ~last:")" ~sep:", " s_exp es

  and s_exp = function
    | Const c -> s_const c
    | Lval l -> s_lv l
    | SizeOf t -> "SizeOf(" ^ s_type t ^ ")"
    | SizeOfE e -> "SizeOfE(" ^ s_exp e ^ ")"
    | SizeOfStr s -> "SizeOfStr(" ^ s ^ ")"
    | AlignOf t -> "AlignOf(" ^ s_type t ^ ")"
    | AlignOfE e -> "AlignOfE(" ^ s_exp e ^ ")"
    | UnOp (u, e, _) -> s_uop u ^ s_exp_paren e
    | BinOp (b, e1, e2, _) -> s_exp_paren e1 ^ s_bop b ^ s_exp_paren e2
    | Question (c, e1, e2, _) ->
        s_exp_paren c ^ " ? " ^ s_exp_paren e1 ^ " : " ^ s_exp_paren e2
    | CastE (t, e) -> "(" ^ s_type t ^ ")" ^ s_exp_paren e
    | AddrOf l -> "&" ^ s_lv l
    | AddrOfLabel _ -> invalid_arg "AddrOfLabel is not supported."
    | StartOf l -> "StartOf(" ^ s_lv l ^ ")"

  and s_exp_paren e =
    match e with
    | UnOp _ | BinOp _ | Question _ | CastE _ -> "(" ^ s_exp e ^ ")"
    | _ -> s_exp e

  and s_const c = tostring (d_const () c)
  and s_type typ = tostring (d_type () typ)
  and s_stmt s = tostring (d_stmt () s)
  and s_lv (lh, offset) = s_lhost lh ^ s_offset offset

  and s_lhost = function
    | Var vi -> (if vi.vglob then "@" else "") ^ vi.vname
    | Mem e -> "*" ^ s_exp_paren2 e

  and s_exp_paren2 e =
    match e with
    | Lval (_, NoOffset) -> s_exp e
    | Lval _ | UnOp _ | BinOp _ | Question _ | CastE _ -> "(" ^ s_exp e ^ ")"
    | _ -> s_exp e

  and s_offset = function
    | NoOffset -> ""
    | Field (fi, offset) -> "." ^ fi.fname ^ s_offset offset
    | Index (e, offset) -> "[" ^ s_exp e ^ "]" ^ s_offset offset

  and s_uop u = tostring (d_unop () u)
  and s_bop b = tostring (d_binop () b)

  and s_instr i =
    match i with
    | Set (lv, exp, _) -> "Set(" ^ s_lv lv ^ "," ^ s_exp exp ^ ")"
    | Call (Some lv, fexp, params, _) ->
        s_lv lv ^ ":= Call(" ^ s_exp fexp ^ s_exps params ^ ")"
    | Call (None, fexp, params, _) -> "Call(" ^ s_exp fexp ^ s_exps params ^ ")"
    | Asm _ -> "Asm"

  and s_instrs instrs = List.fold_left (fun s i -> s ^ s_instr i) "" instrs
end

let reverse_hashtbl tbl =
  let rev_tbl_init = Hashtbl.create 1000 in
  Hashtbl.iter (fun k v -> Hashtbl.add rev_tbl_init v k) tbl;
  rev_tbl_init
