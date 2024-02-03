open Core
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module L = Logger
module F = Format
module Sys = Stdlib.Sys

let parse_loc loc =
  let parsed = Str.split (Str.regexp ":") loc in
  if List.length parsed <> 2 then { Maps.CfgNode.file = ""; line = -1 }
  else
    {
      file = List.nth_exn parsed 0;
      line = int_of_string (List.nth_exn parsed 1);
    }

let parse_facts facts func_name =
  Chc.fold
    (fun c acc ->
      match c with
      | Chc.Elt.FuncApply (f, lst) when String.equal f func_name -> lst :: acc
      | _ -> acc)
    facts []

let extract_str = function
  | Chc.Elt.Const z -> Z.to_string z
  | Chc.Elt.Var s -> s
  | Chc.Elt.FDNumeral s -> s
  | _ -> failwith "find_fact_opt - not implemented"

let find_fact_opt key (fact : Chc.Elt.t list list) =
  let arg_opt =
    List.find
      ~f:(fun lst ->
        let key_in_fact = List.hd_exn lst |> extract_str in
        String.equal key_in_fact key)
      fact
  in
  if Option.is_none arg_opt then None
  else
    let out =
      Option.value ~default:[] arg_opt
      |> List.tl_exn
      |> List.fold_left ~init:[] ~f:(fun acc s -> extract_str s :: acc)
      |> List.rev
    in
    Some out

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
  if List.length inline_funcs <> 0 then Inline.perform inline_funcs cil else cil

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
  | "LibCallExp.facts" -> "LibCallExp"
  | "LvalExp.facts" -> "LvalExp"
  | "Return.facts" -> "Return"
  | "SAllocExp.facts" -> "SAlloc"
  | "Skip.facts" -> "Skip"
  | "EvalLv.facts" -> "EvalLv"
  | "Assume.facts" -> "Assume"
  | f -> L.error "file2func - wrong filename: %s" f

let parse_sparrow nodes map chc =
  let set_facts = parse_facts chc "Set" in
  let call_facts = parse_facts chc "Call" in
  let args_facts = parse_facts chc "Arg" in
  let alloc_exp_facts = parse_facts chc "Alloc" in
  let return_facts = parse_facts chc "Return" in
  let assume_facts = parse_facts chc "Assume" in
  List.iter
    ~f:(fun (key, cmd, loc) ->
      let cmd =
        match List.hd_exn cmd with
        | "skip" -> Maps.CfgNode.CSkip (parse_loc loc)
        | "return" ->
            let arg_opt = find_fact_opt key return_facts in
            if Option.is_none arg_opt then CNone
            else
              let arg = Option.value ~default:[] arg_opt in
              if List.length arg <> 0 then
                CReturn1 (List.hd_exn arg, parse_loc loc, cmd)
              else CReturn2 (parse_loc loc)
        | "call" ->
            let arg_opt = find_fact_opt key call_facts in
            if Option.is_none arg_opt then CNone
            else
              let arg = Option.value ~default:[] arg_opt in
              let call_exp = List.nth_exn arg 1 in
              let lval = List.nth_exn arg 0 in
              let arg_lst = find_fact_opt call_exp args_facts in
              let arg_lst =
                if Option.is_none arg_lst then []
                else Option.value ~default:[] arg_lst
              in
              CCall
                ( List.hd_exn arg,
                  CCallExp (lval, arg_lst, parse_loc loc),
                  parse_loc loc,
                  cmd )
        | "assume" ->
            let arg_opt = find_fact_opt key assume_facts in
            if Option.is_none arg_opt then CNone
            else
              let arg = Option.value ~default:[] arg_opt in
              if List.hd_exn arg |> String.equal "true" then
                CAssume (true, List.nth_exn arg 1, parse_loc loc)
              else if List.hd_exn arg |> String.equal "false" then
                CAssume (false, List.nth_exn arg 1, parse_loc loc)
              else failwith "parse_sparrow: incorrect assume fact format"
        | "set" ->
            let arg = find_fact_opt key set_facts in
            if Option.is_none arg then CNone
            else
              let arg = Option.value ~default:[] arg in
              CSet (List.hd_exn arg, List.nth_exn arg 1, parse_loc loc, cmd)
        | "alloc" -> (
            let arg = find_fact_opt key alloc_exp_facts in
            match arg with
            | None -> CNone
            | Some arg ->
                CAlloc (List.hd_exn arg, List.nth_exn arg 1, parse_loc loc, cmd)
            )
        | "falloc" -> CNone
        | "salloc" -> CNone
        | _ -> L.error "parse_sparrow: unknown command %s" (List.hd_exn cmd)
      in
      match cmd with CNone | CSkip _ -> () | _ -> Hashtbl.add map cmd key)
    nodes

let parse_cf_facts datalog_dir fact_file =
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

let make_cf_facts work_dir cfg map =
  let cf_facts =
    List.fold_left ~init:Chc.empty
      ~f:(fun facts file ->
        let chc = parse_cf_facts work_dir file in
        Chc.union facts chc)
      Z3env.fact_files
  in
  parse_sparrow cfg map cf_facts;
  cf_facts

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

let eq_instrs ast_instr cfg_instr =
  match (ast_instr, cfg_instr) with
  | [ Cil.Call (_, _, _, loc) ], Maps.CfgNode.CCall (_, _, cloc, _) ->
      SymDiff.eq_line loc cloc
  | [ Cil.Set (lv, _, loc) ], Maps.CfgNode.CSet (_, _, cloc, cmd)
  | [ Cil.Set (lv, _, loc) ], Maps.CfgNode.CAlloc (_, _, cloc, cmd)
  | [ Cil.Set (lv, _, loc) ], Maps.CfgNode.CSalloc (_, _, cloc, cmd)
  | [ Cil.Set (lv, _, loc) ], Maps.CfgNode.CFalloc (_, _, cloc, cmd) ->
      SymDiff.eq_line loc cloc
      && String.equal (Ast.s_lv lv) (List.nth_exn cmd 1)
  | _ -> false

let lookup_eq_nodes ast_node cfg =
  let stmt_node = Ast.ast2stmt ast_node in
  Hashtbl.fold
    (fun cnode id acc ->
      (match (stmt_node.Cil.skind, cnode) with
      | Cil.Instr i, cn -> eq_instrs i cn
      | Cil.If (_, _, _, loc), Maps.CfgNode.CIf cloc
      | Cil.If (_, _, _, loc), Maps.CfgNode.CAssume (_, _, cloc) ->
          SymDiff.eq_line loc cloc
      | Cil.Return (_, loc), Maps.CfgNode.CReturn1 (_, cloc, _)
      | Cil.Return (_, loc), Maps.CfgNode.CReturn2 cloc ->
          SymDiff.eq_line loc cloc
      | _ -> false)
      |> fun bool -> if bool then id :: acc else acc)
    cfg []
  |> fun x -> if List.length x = 0 then None else Some (List.hd_exn x)

let match_eq_nodes fmt maps ast_node =
  let ast_num = Hashtbl.find maps.Maps.ast_map ast_node |> string_of_int in
  let ast_id = "AstNode-" ^ ast_num in
  let ast_term = mk_term ast_id in
  let cfg_id_opt = lookup_eq_nodes ast_node maps.Maps.cfg_map in
  if Option.is_some cfg_id_opt then (
    let cfg_id = Option.value_exn cfg_id_opt in
    let cfg_term = mk_term cfg_id in
    F.fprintf fmt "%s\t%s\n" cfg_id ast_id;
    Hashtbl.add maps.Maps.node_map cfg_id ast_num;
    [ Chc.Elt.FuncApply ("EqNode", [ cfg_term; ast_term ]) ])
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
  let eqnode_rels =
    if match parent with Ast.Global _ -> true | _ -> false then
      match_eq_nodes eqnode_fmt maps child
    else
      match_eq_nodes eqnode_fmt maps parent
      @ match_eq_nodes eqnode_fmt maps child
  in
  (parent_rel :: eqnode_rels) @ acc

let make_ast_facts work_dir maps (globs, stmts) =
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

exception Not_impl_aexp

let get_aexp alarm splited filename =
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
  | f, _ ->
      Logger.warn "get_aexp - not implemented: %s" f;
      raise Not_impl_aexp

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
  let aexps =
    Array.fold
      ~f:(fun aexps file ->
        match Filename.concat work_dir file |> read_and_split with
        | hd :: [] -> get_aexp alarm hd file
        | [] -> aexps
        | _ -> aexps (* TEMP *))
      ~init:Chc.empty alarm_exp_files
  in
  (src, snk, aexps)

let make_facts buggy_dir target_alarm ast cfg out_dir (maps : Maps.t) =
  let alarm_dir =
    Filename.concat buggy_dir ("sparrow-out/taint/datalog/" ^ target_alarm)
  in
  L.info "Making facts from %sth alarm" (Filename.basename alarm_dir);
  Utils.parse_map alarm_dir maps.exp_map;
  let ast_nodes = (Ast.extract_globs ast, Ast.extract_stmts ast) in
  let cf_facts = make_cf_facts alarm_dir cfg maps.cfg_map in
  let ast_facts = make_ast_facts alarm_dir maps ast_nodes in
  let facts = Chc.union cf_facts ast_facts in
  Chc.pretty_dump (Filename.concat out_dir target_alarm) facts;
  Chc.sexp_dump (Filename.concat out_dir target_alarm) facts;
  (facts, get_alarm alarm_dir)
