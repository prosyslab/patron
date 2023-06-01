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

(* pp functions *)
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

let print_bool b =
  if b = true then print_endline "true" else print_endline "false"

let eq_instr instr1 instr2 =
  match (instr1, instr2) with
  | Cil.Set (lv1, _, _), Cil.Set (lv2, _, _) ->
      string_of_lval lv1 = string_of_lval lv2
  | Cil.Call (lv1, _, _, _), Cil.Call (lv2, _, _, _) -> (
      match (lv1, lv2) with
      | None, None -> true
      | Some lv1, Some lv2 -> string_of_lval lv1 = string_of_lval lv2
      | _ -> false)
  | Cil.Asm _, Cil.Asm _ -> true
  | _ -> false

let eq_stmt skind1 skind2 =
  match (skind1, skind2) with
  | Cil.Instr i1, Cil.Instr i2 -> eq_instr (List.hd i1) (List.hd i2)
  | Cil.Return (Some e1, _), Cil.Return (Some e2, _) ->
      string_of_exp e1 = string_of_exp e2
  | Cil.Return (None, _), Cil.Return (None, _) -> true
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
  | _ -> false

let eq_global glob1 glob2 =
  match (glob1, glob2) with
  | Cil.GFun (func_info1, _), Cil.GFun (func_info2, _) ->
      eq_typ func_info1.svar.vtype func_info2.svar.vtype
      && func_info1.svar.vname = func_info2.svar.vname
  | Cil.GType _, Cil.GType _
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

let rec eq_exp (a : Cil.exp) (b : Cil.exp) =
  match (a, b) with
  | Lval (Var a, NoOffset), Lval (Var b, NoOffset) -> a.vname = b.vname
  | Lval (Mem a, NoOffset), Lval (Mem b, NoOffset) -> eq_exp a b
  | BinOp (a, b, c, _), BinOp (d, e, f, _) -> a = d && eq_exp b e && eq_exp c f
  | UnOp (a, b, _), UnOp (c, d, _) -> a = c && eq_exp b d
  | CastE (a, b), CastE (c, d) -> a = c && eq_exp b d
  | AddrOf (Var a, NoOffset), AddrOf (Var b, NoOffset) -> a.vname = b.vname
  | AddrOf (Mem a, NoOffset), AddrOf (Mem b, NoOffset) -> eq_exp a b
  | StartOf (Var a, NoOffset), StartOf (Var b, NoOffset) -> a.vname = b.vname
  | StartOf (Mem a, NoOffset), StartOf (Mem b, NoOffset) -> eq_exp a b
  | Cil.SizeOfE a, Cil.SizeOfE b -> eq_exp a b
  | Const a, Const b -> a = b
  | Lval (Var a, NoOffset), StartOf (Var b, NoOffset)
  | StartOf (Var a, NoOffset), Lval (Var b, NoOffset) ->
      a.vname = b.vname
  | Question (a, b, c, _), Question (d, e, f, _) ->
      eq_exp a d && eq_exp b e && eq_exp c f
  | _ -> false

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
  let set1 = explode s1 in
  let set2 = explode s2 in
  search_seq set1 set2

let print_ikind instr =
  match instr with
  | Cil.Call _ -> print_endline "Call"
  | Cil.Set _ -> print_endline "Set"
  | Cil.Asm _ -> print_endline "Asm"

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

let print_skind skind =
  match skind with
  | Cil.Instr _ -> print_endline "Instr"
  | Cil.Return _ -> print_endline "Return"
  | Cil.Goto _ -> print_endline "Goto"
  | Cil.Break _ -> print_endline "Break"
  | Cil.Continue _ -> print_endline "Continue"
  | Cil.If _ -> print_endline "If"
  | Cil.Switch _ -> print_endline "Switch"
  | Cil.Loop _ -> print_endline "Loop"
  | Cil.Block _ -> print_endline "Block"
  | Cil.TryExcept _ -> print_endline "TryExcept"
  | Cil.TryFinally _ -> print_endline "TryFinally"
  | Cil.ComputedGoto _ -> print_endline "ComputedGoto"

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
  let ic = open_in name in
  let try_read () = try Some (input_line ic) with End_of_file -> None in
  let rec loop acc =
    match try_read () with
    | Some s -> loop (s :: acc)
    | None ->
        close_in ic;
        List.rev acc
  in
  loop []

let make_str_map path =
  let lines = read_lines path in
  List.fold_left
    (fun map line ->
      let splited = Str.split (Str.regexp "\t") line in
      let key = List.hd splited in
      let value = List.hd (List.tl splited) in
      StrMap.add key value map)
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

type loc = { file : string; line : int }

type cmd =
  | Cnone
  | Cset of string * string * loc (* (lv, e, loc) *)
  | Cexternal of string * loc (*(lv, loc)*)
  | Calloc of string * string * loc (*(lv, Array e, _, loc) *)
  | Csalloc of string * string * loc (*(lv, s, loc) *)
  | Cfalloc of string * string * loc (*(lv, f, loc) *)
  | Ccall1 of
      string * string * string list * loc (*(Some lv, fexp, params, loc)*)
  | Ccall2 of string * string list * loc (*(None, fexp, params, loc)*)
  | Creturn1 of string * loc (*(Some e, loc) *)
  | Creturn2 of loc (*(None, loc) *)
  | Cif of loc (*(_, _, _, loc) *)
  | Cassume of string * loc (*(e, _, loc) *)
  | CLoop of loc (*loc *)
  | Casm of loc (*(_, _, _, _, _, loc) *)
  | Cskip of loc (*(_, loc)*)

let print_cmd cmd =
  match cmd with
  | Cset (lv, e, loc) ->
      print_endline
        ("set\t" ^ lv ^ "\t" ^ e ^ "\t" ^ loc.file ^ ":"
       ^ string_of_int loc.line)
  | Cexternal (lv, loc) ->
      print_endline
        ("external\t" ^ lv ^ "\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Calloc (lv, e, loc) ->
      print_endline
        ("alloc\t" ^ lv ^ "\t" ^ e ^ "\t" ^ loc.file ^ ":"
       ^ string_of_int loc.line)
  | Csalloc (lv, s, loc) ->
      print_endline
        ("salloc\t" ^ lv ^ "\t" ^ s ^ "\t" ^ loc.file ^ ":"
       ^ string_of_int loc.line)
  | Cfalloc (lv, f, loc) ->
      print_endline
        ("falloc\t" ^ lv ^ "\t" ^ f ^ "\t" ^ loc.file ^ ":"
       ^ string_of_int loc.line)
  | Ccall1 (lv, fexp, params, loc) ->
      print_endline
        ("call\t" ^ lv ^ "\t" ^ fexp ^ "\t" ^ String.concat "," params ^ "\t"
       ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Ccall2 (fexp, params, loc) ->
      print_endline
        ("call\t" ^ "null" ^ "\t" ^ fexp ^ "\t" ^ String.concat "," params
       ^ "\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Creturn1 (e, loc) ->
      print_endline
        ("return\t" ^ e ^ "\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Creturn2 loc ->
      print_endline
        ("return\t" ^ "null" ^ "\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Cif loc -> print_endline ("if\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Cassume (e, loc) ->
      print_endline
        ("assume\t" ^ e ^ "\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | CLoop loc ->
      print_endline ("loop\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Casm loc -> print_endline ("asm\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | Cskip loc ->
      print_endline ("skip\t" ^ loc.file ^ ":" ^ string_of_int loc.line)
  | _ -> ()

module CmdMap = Map.Make (struct
  type t = cmd

  let compare = compare
end)

let parse_loc loc =
  let parsed = Str.split (Str.regexp ":") loc in
  if List.length parsed <> 2 then { file = ""; line = -1 }
  else { file = List.nth parsed 0; line = int_of_string (List.nth parsed 1) }

let parse_facts facts_path =
  let lines = read_lines facts_path in
  List.fold_left
    (fun map line ->
      let keyval = Str.split (Str.regexp "\t") line in
      let id = List.hd keyval in
      let elmt = List.tl keyval in
      StrMap.add id elmt map)
    StrMap.empty lines

let parse_args_facts facts_path =
  let lines = read_lines facts_path in
  let result =
    List.fold_left
      (fun map line ->
        let keyval = Str.split (Str.regexp "\t") line in
        let id = List.hd keyval in
        match StrMap.find_opt id map with
        | None -> StrMap.add id [ List.nth keyval 2 ] map
        | Some lst ->
            StrMap.update id (fun _ -> Some (List.nth keyval 2 :: lst)) map)
      StrMap.empty lines
  in
  StrMap.map (fun lst -> List.rev lst) result

let parse_sparrow sparrow_dir =
  let node_json = Yojson.Basic.from_file (sparrow_dir ^ "/node.json") in
  let return_facts =
    parse_facts (sparrow_dir ^ "/interval/datalog/Return.facts")
  in
  let call_facts =
    StrMap.union
      (fun _ _ y -> Some y)
      (parse_facts (sparrow_dir ^ "/interval/datalog/Call.facts"))
      (parse_facts (sparrow_dir ^ "/interval/datalog/LibCall.facts"))
  in
  let args_facts =
    parse_args_facts (sparrow_dir ^ "/interval/datalog/Arg.facts")
  in
  let assume_facts =
    parse_facts (sparrow_dir ^ "/interval/datalog/Assume.facts")
  in
  let salloc_facts =
    parse_facts (sparrow_dir ^ "/interval/datalog/SAlloc.facts")
  in
  let assign_facts =
    parse_facts (sparrow_dir ^ "/interval/datalog/Assign.facts")
  in
  let alloc_facts =
    parse_facts (sparrow_dir ^ "/interval/datalog/Alloc.facts")
  in
  let nodes = J.member "nodes" node_json in
  let key_list = J.keys nodes in
  List.fold_left
    (fun acc k ->
      let cont = J.member k nodes in
      let cmd = J.to_list (J.member "cmd" cont) in
      let loc = J.member "loc" cont in
      let cmd =
        match J.to_string (List.hd cmd) with
        | "skip" -> Cskip (parse_loc (J.to_string loc))
        | "return" ->
            let arg = StrMap.find k return_facts in
            if arg <> [] then Creturn1 (List.hd arg, parse_loc (J.to_string loc))
            else Creturn2 (parse_loc (J.to_string loc))
        | "call" -> (
            let arg = StrMap.find k call_facts in
            let arg_lst = StrMap.find_opt (List.nth arg 2) args_facts in
            let arg_lst = if arg_lst = None then [] else Option.get arg_lst in
            match List.hd arg with
            | "null" ->
                Ccall2 (List.nth arg 1, arg_lst, parse_loc (J.to_string loc))
            | _ ->
                Ccall1
                  ( List.hd arg,
                    List.nth arg 1,
                    arg_lst,
                    parse_loc (J.to_string loc) ))
        | "assume" ->
            let arg = StrMap.find k assume_facts in
            Cassume (List.hd arg, parse_loc (J.to_string loc))
        | "salloc" ->
            let arg = StrMap.find k salloc_facts in
            let str =
              Str.global_replace (Str.regexp "\\\"") ""
                (J.to_string (List.nth cmd 2))
            in
            Csalloc (List.hd arg, str, parse_loc (J.to_string loc))
        | "set" ->
            let arg = StrMap.find k assign_facts in
            Cset (List.hd arg, List.nth arg 1, parse_loc (J.to_string loc))
        | "alloc" -> (
            let arg = StrMap.find_opt k alloc_facts in
            match arg with
            | None -> Cnone
            | Some arg ->
                Calloc (List.hd arg, List.nth arg 1, parse_loc (J.to_string loc))
            )
        | "falloc" -> Cnone
        | _ -> failwith "Unknown Command"
      in
      match cmd with Cnone -> acc | _ -> CmdMap.add cmd k acc)
    CmdMap.empty key_list

let extract_stmt_lst file =
  let extract_stmt stmt =
    match stmt.Cil.skind with
    | Cil.If (_, t_b, e_b, _) -> t_b.bstmts @ e_b.bstmts
    | Cil.Loop (b, _, _, _) -> b.bstmts
    | Cil.Block b -> b.bstmts
    | _ -> []
  in
  let fold_glob glob =
    match glob with
    | Cil.GFun (fdec, _) ->
        List.fold_left
          (fun acc stmt -> acc @ [ stmt ] @ extract_stmt stmt)
          [] fdec.Cil.sbody.Cil.bstmts
    | _ -> []
  in
  List.fold_left (fun acc g -> acc @ fold_glob g) [] file.Cil.globals

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
