open Core
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module L = Logger
module F = Format
module Sys = Stdlib.Sys

let parse_facts facts func_name =
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply (f, lst) when String.equal f func_name ->
          if String.equal func_name "LvalExp" then List.rev lst :: acc
          else lst :: acc
      | _ -> acc)
    facts []

let extract_str = function
  | Chc.Elt.Const z -> Z.to_string z
  | Chc.Elt.Var s -> s
  | Chc.Elt.FDNumeral s -> s
  | _ -> failwith "find_fact_opt - not implemented"

let find_in_fact key (fact : Chc.Elt.t list list) =
  List.fold_left
    ~f:(fun acc lst ->
      let key_in_fact = List.hd_exn lst |> extract_str in
      if String.equal key_in_fact key then
        (List.tl_exn lst
        |> List.fold_left ~init:[] ~f:(fun acc s -> extract_str s :: acc)
        |> List.rev)
        @ acc
      else acc)
    ~init:[] fact

let get_facts facts func_name =
  List.find_exn facts ~f:(fun (f, _) -> String.equal f func_name) |> snd

class blockVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vblock b =
      let stmts =
        List.fold_left ~init:[]
          ~f:(fun l stmt ->
            match stmt.Cil.skind with
            | Cil.Instr il when List.length il > 1 ->
                let new_il = List.map ~f:Cil.mkStmtOneInstr (List.tl_exn il) in
                stmt.skind <- Instr [ List.hd_exn il ];
                l @ (stmt :: new_il)
            | Cil.Instr il when List.length il = 0 -> l
            | _ -> l @ [ stmt ])
          b.bstmts
      in
      b.bstmts <- stmts;
      ChangeDoChildrenPost (b, fun x -> x)
  end

let parse_ast target_dir inline_funcs =
  let file = Utils.get_target_file target_dir in
  if !Cilutil.printStages then ignore ();
  let cil = Frontc.parse file () in
  Rmtmps.removeUnusedTemps cil;
  Cil.visitCilFile (new blockVisitor) cil;
  let post_processed_cil =
    if List.length inline_funcs <> 0 then Inline.perform inline_funcs cil
    else cil
  in
  if List.length !Ast.buggy_ast = 1 then
    Ast.buggy_ast := post_processed_cil :: !Ast.buggy_ast;
  post_processed_cil

let mk_term s =
  if Z3utils.is_binop s || Z3utils.is_unop s then Chc.Elt.FDNumeral s
  else
    try Chc.Elt.Const (Z.of_string s)
    with _ ->
      let splitted = String.split ~on:'-' s in
      if List.length splitted = 1 then Chc.Elt.Var s
      else (
        incr Z3env.sort_size;
        Chc.Elt.FDNumeral s)

let file2func = function
  | "AllocExp.facts" -> "AllocExp"
  | "Arg.facts" -> "Arg"
  | "Set.facts" -> "Set"
  | "BinOpExp.facts" -> "BinOpExp"
  | "UnOpExp.facts" -> "UnOpExp"
  | "CallExp.facts" -> "CallExp"
  | "CFPath.facts" -> "CFPath"
  | "DetailedDUEdge.facts" -> "DetailedDUEdge"
  | "DUEdge.facts" -> "DUEdge"
  | "DUPath.facts" -> "DUPath"
  | "GlobalVar.facts" | "LocalVar.facts" -> "Var"
  | "Index.facts" -> "Index"
  | "Mem.facts" -> "Mem"
  | "AddrOf.facts" -> "AddrOf"
  | "LibCallExp.facts" -> "LibCallExp"
  | "LvalExp.facts" -> "LvalExp"
  | "Return.facts" -> "Return"
  | "SAllocExp.facts" -> "SAlloc"
  | "Skip.facts" -> "Skip"
  | "EvalLv.facts" -> "EvalLv"
  | "Assume.facts" -> "Assume"
  | f -> L.error "file2func - wrong filename: %s" f

type facts4sparrow = {
  set_facts : Chc.elt list list;
  callexp_facts : Chc.elt list list;
  libcall_facts : Chc.elt list list;
  args_facts : Chc.elt list list;
  alloc_exp_facts : Chc.elt list list;
  return_facts : Chc.elt list list;
  assume_facts : Chc.elt list list;
  mem_facts : Chc.elt list list;
  lvexp_facts : Chc.elt list list;
  evallv_facts : Chc.elt list list;
  binopexp_facts : Chc.elt list list;
  unopexp_facts : Chc.elt list list;
  addr_of_facts : Chc.elt list list;
  index_facts : Chc.elt list list;
}

let parse_du_facts datalog_dir fact_file =
  let func_name = file2func fact_file in
  let fact_file_path = Filename.concat datalog_dir fact_file in
  let elt_lst =
    In_channel.read_lines fact_file_path
    |> List.fold_left ~init:[] ~f:(fun lst line ->
           let arg_lst = String.split ~on:'\t' line in
           let args = List.map ~f:mk_term arg_lst in
           let elt = Chc.Elt.FuncApply (func_name, args) in
           elt :: lst)
  in
  List.rev elt_lst |> Chc.of_list

let make_du_facts work_dir =
  List.fold_left ~init:Chc.empty
    ~f:(fun facts file ->
      let chc = parse_du_facts work_dir file in
      Chc.union facts chc)
    Z3env.fact_files

let rec sexp2chc = function
  | Sexp.List [ Sexp.Atom "Lt"; e1; e2 ] ->
      Chc.Elt.CLt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Gt"; e1; e2 ] -> CGt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Le"; e1; e2 ] -> CLe (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Ge"; e1; e2 ] -> CGe (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Eq"; e1; e2 ] -> CEq (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Ne"; e1; e2 ] -> CNe (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvshl"; e1; e2 ] -> BvShl (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvshr"; e1; e2 ] -> BvShr (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvand"; e1; e2 ] -> BvAnd (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvor"; e1; e2 ] -> BvOr (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "bvxor"; e1; e2 ] -> BvXor (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "<"; e1; e2 ] -> Lt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom ">"; e1; e2 ] -> Gt (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "<="; e1; e2 ] -> Le (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom ">="; e1; e2 ] -> Ge (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "PlusPI"; _; _ ] ]
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "IndexPI"; _; _ ] ]
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "MinusPI"; _; _ ] ]
  | Sexp.List [ Sexp.Atom "="; _; Sexp.List [ Sexp.Atom "MinusPP"; _; _ ] ] ->
      Eq (Var "y", Var "y")
  | Sexp.List [ Sexp.Atom "="; e1; e2 ] -> Eq (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "!="; e1; e2 ] -> Ne (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "PlusA"; e1; e2 ] -> Add (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "MinusA"; e1; e2 ] -> Sub (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Mult"; e1; e2 ] -> Mul (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Div"; e1; e2 ] -> Div (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "Mod"; e1; e2 ] -> Mod (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "and"; e1; e2 ] -> And (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "or"; e1; e2 ] -> Or (sexp2chc e1, sexp2chc e2)
  | Sexp.List [ Sexp.Atom "BNot"; e ] -> CBNot (sexp2chc e)
  | Sexp.List [ Sexp.Atom "LNot"; e ] -> CLNot (sexp2chc e)
  | Sexp.List [ Sexp.Atom "Neg"; e ] -> CNeg (sexp2chc e)
  | Sexp.List [ Sexp.Atom "not"; e ] -> Not (sexp2chc e)
  | Sexp.List (Sexp.Atom f :: es) -> FuncApply (f, List.map ~f:sexp2chc es)
  | Sexp.List ((Sexp.List (Sexp.Atom _ :: _) as hd) :: tl) ->
      Implies (List.map ~f:sexp2chc tl, sexp2chc hd)
  | Sexp.Atom s -> mk_term s
  | _ -> failwith "Unsupported Sexp"

let parse_chc chc_file =
  In_channel.read_lines chc_file
  |> List.fold_left ~init:[] ~f:(fun chc_list rule ->
         try (Sexp.of_string rule |> sexp2chc) :: chc_list with _ -> chc_list)
  |> Chc.of_list

let mk_parent_tuples globs stmts =
  let mk_glob_parents parent stmts acc =
    let parent = Ast.glob2ast (Some parent) in
    List.fold_left ~init:acc
      ~f:(fun a s -> (parent, Ast.stmt2ast (Some s)) :: a)
      stmts
  in
  let mk_stmt_parents parent stmts acc =
    let parent = Ast.stmt2ast (Some parent) in
    List.fold_left ~init:acc
      ~f:(fun a s -> (parent, Ast.stmt2ast (Some s)) :: a)
      stmts
  in
  let glob_tuples =
    List.fold_left ~init:[]
      ~f:(fun acc g ->
        match g with
        | Cil.GFun (f, _) -> mk_glob_parents g f.sbody.bstmts acc
        | _ -> acc)
      globs
  in
  let stmt_tuples =
    List.fold_left ~init:[]
      ~f:(fun acc s ->
        match s.Cil.skind with
        | Cil.Block b | Cil.Loop (b, _, _, _) -> mk_stmt_parents s b.bstmts acc
        | Cil.If (_, tb, eb, _) ->
            acc |> mk_stmt_parents s tb.bstmts |> mk_stmt_parents s eb.bstmts
        | _ -> acc)
      stmts
  in
  glob_tuples @ stmt_tuples

let match_stmt_id loc_map = function
  | Cil.Instr (Cil.Set (_, _, loc) :: _)
  | Cil.Instr (Cil.Call (_, _, _, loc) :: _)
  | Cil.Return (_, loc)
  | Cil.If (_, _, _, loc)
  | Cil.Loop (_, loc, _, _) ->
      Hashtbl.find_opt loc_map { Maps.file = loc.file; line = loc.line }
  | _ -> None

let match_eq_nodes fmt maps ast_node =
  let ast_num = Hashtbl.find maps.Maps.ast_map ast_node |> string_of_int in
  let ast_id = "AstNode-" ^ ast_num in
  let ast_term = mk_term ast_id in
  let stmt = Ast.ast2stmt ast_node in
  let dug_id_opt = match_stmt_id maps.Maps.loc_map stmt.skind in
  if Option.is_some dug_id_opt then (
    let dug_id = Option.value_exn dug_id_opt in
    let dug_term = mk_term dug_id in
    F.fprintf fmt "%s\t%s\n" dug_id ast_id;
    Hashtbl.add maps.Maps.node_map dug_id ast_num;
    [ Chc.Elt.FuncApply ("EqNode", [ dug_term; ast_term ]) ])
  else []

let astnode_cnt = ref 1

let new_astnode_id maps stmt =
  let id = "AstNode-" ^ string_of_int !astnode_cnt in
  incr astnode_cnt;
  Hashtbl.add maps.Maps.ast_map stmt !astnode_cnt;
  id

let ast2astid maps ast =
  if Hashtbl.mem maps.Maps.ast_map ast then
    let n = Hashtbl.find maps.ast_map ast in
    "AstNode-" ^ string_of_int n
  else new_astnode_id maps ast

let mk_ast_rels parent_fmt eqnode_fmt maps acc (parent, child)
    (parent_id, child_id) =
  F.fprintf parent_fmt "%s\t%s\n" parent_id child_id;
  let parent_term = mk_term parent_id in
  let child_term = mk_term child_id in
  let parent_rel =
    Chc.Elt.FuncApply ("AstParent", [ parent_term; child_term ])
  in
  if match parent with Ast.Stmt _ -> false | _ -> true then parent_rel :: acc
  else
    let eqnode_rels =
      match_eq_nodes eqnode_fmt maps parent
      @ match_eq_nodes eqnode_fmt maps child
    in
    (parent_rel :: eqnode_rels) @ acc

let make_parent_facts work_dir maps (globs, stmts) =
  let parent_tups = mk_parent_tuples globs stmts in
  let parent_oc =
    Filename.concat work_dir "AstParent.facts" |> Out_channel.create
  in
  let eqnode_oc =
    Filename.concat work_dir "EqNode.facts" |> Out_channel.create
  in
  let parent_fmt = F.formatter_of_out_channel parent_oc in
  let eqnode_fmt = F.formatter_of_out_channel eqnode_oc in
  let facts =
    List.fold_left ~init:[]
      ~f:(fun acc (parent, child) ->
        let parent_id = ast2astid maps parent in
        let child_id = ast2astid maps child in
        (parent_id, child_id) :: acc)
      parent_tups
    |> List.fold2_exn ~init:[]
         ~f:(mk_ast_rels parent_fmt eqnode_fmt maps)
         parent_tups
    |> Chc.of_list
  in
  F.pp_print_flush parent_fmt ();
  F.pp_print_flush eqnode_fmt ();
  Out_channel.close parent_oc;
  Out_channel.close eqnode_oc;
  facts

let read_and_split file =
  In_channel.read_lines file |> List.map ~f:(fun l -> String.split ~on:'\t' l)

exception Not_impl_alarm_comps

let get_alarm_comps alarm splited filename =
  (* TODO: add expression relation that have error e.g. DivExp --> Div relation *)
  match (Filename.basename filename |> Filename.chop_extension, splited) with
  | "AlarmArrayExp", [ a; l; e ] when String.equal a alarm ->
      Chc.of_list [ Chc.Elt.FDNumeral l; Chc.Elt.FDNumeral e ]
  | "AlarmAllocSize", [ a; e ]
  | "AlarmDerefExp", [ a; e ]
  | "AlarmPrintf", [ a; e ]
  | "AlarmDivExp", [ a; _; e ]
    when String.equal a alarm ->
      Chc.singleton (Chc.Elt.FDNumeral e)
  | "AlarmIOExp", [ a; e1; e2 ]
  | "AlarmMemchr", [ a; e1; e2 ]
  | "AlarmSprintf", [ a; e1; e2 ]
  | "AlarmStrcat", [ a; e1; e2 ]
  | "AlarmStrcpy", [ a; e1; e2 ]
    when String.equal a alarm ->
      Chc.of_list [ Chc.Elt.FDNumeral e1; Chc.Elt.FDNumeral e2 ]
  | "AlarmMemcpy", [ a; e1; e2; e3 ]
  | "AlarmMemmove", [ a; e1; e2; e3 ]
  | "AlarmStrncmp", [ a; e1; e2; e3 ]
  | "AlarmStrncpy", [ a; e1; e2; e3 ]
    when String.equal a alarm ->
      Chc.of_list
        [ Chc.Elt.FDNumeral e1; Chc.Elt.FDNumeral e2; Chc.Elt.FDNumeral e3 ]
  | f, _ -> Logger.error "get_alarm_comps - not implemented: %s" f

let get_alarm work_dir =
  let src, snk, alarm =
    match
      Filename.concat work_dir "SparrowAlarm.facts"
      |> read_and_split |> List.hd_exn
    with
    | [ src; snk; alarm_id ] -> (src, snk, alarm_id)
    | _ -> L.error ~to_console:true "get_alarm: invalid format"
  in
  let alarm_exp_files =
    Sys.readdir work_dir
    |> Array.filter ~f:(fun f ->
           Filename.basename f
           |> String.is_substring_at ~pos:0 ~substring:"Alarm")
  in
  let alarm_compss =
    Array.fold
      ~f:(fun alarm_comps file ->
        match Filename.concat work_dir file |> read_and_split with
        | hd :: [] -> get_alarm_comps alarm hd file
        | [] -> alarm_comps
        | _ -> alarm_comps)
      ~init:Chc.empty alarm_exp_files
  in
  (src, snk, alarm_compss)

let make_facts target_dir target_alarm ast out_dir =
  let maps = Maps.create_maps () in
  Maps.reset_maps maps;
  let spo_dir = Filename.concat target_dir "sparrow-out" in
  let alarm_dir = Filename.concat spo_dir ("taint/datalog/" ^ target_alarm) in
  L.info "Making facts from %sth alarm" (Filename.basename alarm_dir);
  Utils.parse_map alarm_dir "Exp.map" maps.Maps.exp_map;
  Utils.parse_map alarm_dir "Lval.map" maps.Maps.lval_map;
  Utils.parse_node_json spo_dir maps.Maps.loc_map maps.Maps.cmd_map;
  let ast_nodes = (Ast.extract_globs ast, Ast.extract_stmts ast) in
  let du_facts = make_du_facts alarm_dir in
  let parent_facts = make_parent_facts alarm_dir maps ast_nodes in
  let facts = Chc.union du_facts parent_facts in
  Chc.pretty_dump (Filename.concat out_dir target_alarm) facts;
  Chc.sexp_dump (Filename.concat out_dir target_alarm) facts;
  (du_facts, parent_facts, get_alarm alarm_dir, maps)
