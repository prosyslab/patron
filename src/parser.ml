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
  | _ -> L.error "find_fact_opt - not implemented"

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
  post_processed_cil

let mk_term s =
  if Z3utils.is_binop s || Z3utils.is_unop s then Chc.Elt.FDNumeral s
  else
    try Chc.Elt.Const (Z.of_string s)
    with _ ->
      let splitted = String.split ~on:'-' s in
      if List.length splitted = 1 then Chc.Elt.Var s else Chc.Elt.FDNumeral s

let file2func = function
  | "AllocExp.facts" -> "AllocExp"
  | "Arg.facts" -> "Arg"
  | "Set.facts" -> "Set"
  | "Copy.facts" -> "Copy"
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
  | "Field.facts" -> "Field"
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
  | _ -> L.error "Unsupported Sexp"

let parse_chc chc_file =
  In_channel.read_lines chc_file
  |> List.fold_left ~init:[] ~f:(fun chc_list rule ->
         try (Sexp.of_string rule |> sexp2chc) :: chc_list with _ -> chc_list)
  |> Chc.of_list

let add_to_ast_map maps key of_cil cil_obj =
  let ast = of_cil (Some cil_obj) in
  Hashtbl.add maps.Maps.ast_map key ast;
  Hashtbl.add maps.Maps.ast_rev_map ast key

let find_node_id loc_map loc =
  let file = String.split ~on:'/' loc.Cil.file |> List.last_exn in
  let line = loc.line in
  Hashtbl.find_all loc_map { Maps.file; line }

let map_node_cil cmd maps loc of_cil cil_obj =
  find_node_id maps.Maps.loc_map loc
  |> List.iter ~f:(fun id ->
         if Hashtbl.find maps.Maps.cmd_map id |> Maps.equal_cmd cmd then
           add_to_ast_map maps id of_cil cil_obj)

class mkAstMap maps =
  object
    inherit Cil.nopCilVisitor

    method! vglob g =
      match g with
      | Cil.GType (_, loc)
      | Cil.GCompTag (_, loc)
      | Cil.GCompTagDecl (_, loc)
      | Cil.GEnumTag (_, loc)
      | Cil.GEnumTagDecl (_, loc)
      | Cil.GVar (_, _, loc)
      | Cil.GVarDecl (_, loc)
      | Cil.GFun (_, loc)
      | Cil.GAsm (_, loc)
      | Cil.GPragma (_, loc) ->
          map_node_cil Maps.Etc maps loc Ast.of_glob g;
          DoChildren
      | Cil.GText _ -> DoChildren

    method! vstmt s =
      let open Option in
      match s.Cil.skind with
      | Cil.Instr (Cil.Set (lv, e, loc) :: _) ->
          let cmd = Maps.Set (Ast.s_lv lv, Ast.s_exp e) in
          map_node_cil cmd maps loc Ast.of_stmt s;
          DoChildren
      | Cil.Instr (Cil.Call (lvo, f, e, loc) :: _) ->
          let cmd = Maps.Call (lvo >>| Ast.s_lv, Ast.s_exp f, Ast.s_exps e) in
          map_node_cil cmd maps loc Ast.of_stmt s;
          DoChildren
      | Cil.Return (eo, loc) ->
          let cmd = Maps.Return (eo >>| Ast.s_exp) in
          map_node_cil cmd maps loc Ast.of_stmt s;
          DoChildren
      | Cil.If (_, _, _, loc) ->
          map_node_cil (Maps.Assume true) maps loc Ast.of_stmt s;
          DoChildren
      | Cil.Break loc
      | Cil.Continue loc
      | Cil.Switch (_, _, _, loc)
      | Cil.Loop (_, loc, _, _)
      | Cil.TryFinally (_, _, loc)
      | Cil.TryExcept (_, _, _, loc) ->
          map_node_cil Maps.Etc maps loc Ast.of_stmt s;
          DoChildren
      | _ -> DoChildren

    method! vlval lv =
      Ast.s_lv lv
      |> Hashtbl.find_all maps.Maps.lval_rev_map
      |> List.iter ~f:(fun id -> add_to_ast_map maps id Ast.of_lval lv);
      DoChildren

    method! vexpr e =
      Ast.s_exp e
      |> Hashtbl.find_all maps.Maps.exp_rev_map
      |> List.iter ~f:(fun id -> add_to_ast_map maps id Ast.of_exp e);
      DoChildren
  end

let get_alarm_comps alarm splited filename =
  match (Filename.basename filename |> Filename.chop_extension, splited) with
  | "AlarmArrayExp", a :: l :: e :: lvs when String.equal a alarm ->
      ( Chc.of_list [ Chc.Elt.FDNumeral l; Chc.Elt.FDNumeral e ],
        List.map ~f:Chc.Elt.numer lvs |> Chc.of_list )
  | "AlarmAllocSize", a :: e :: lvs
  | "AlarmDerefExp", a :: e :: lvs
  | "AlarmPrintf", a :: e :: lvs
  | "AlarmDivExp", a :: _ :: e :: lvs
  | ("AlarmCastExp" | "AlarmCastIOExp"), a :: e :: lvs
  | "AlarmFread", a :: _ :: e :: lvs
    when String.equal a alarm ->
      ( Chc.singleton (Chc.Elt.FDNumeral e),
        List.map ~f:Chc.Elt.numer lvs |> Chc.of_list )
  | ("AlarmPlusExp" | "AlarmPlusIOExp"), a :: e1 :: e2 :: lvs
  | ("AlarmMinusExp" | "AlarmMinusIOExp"), a :: e1 :: e2 :: lvs
  | ("AlarmMultExp" | "AlarmMultIOExp"), a :: e1 :: e2 :: lvs
  | ("AlarmShiftExp" | "AlarmShiftIOExp"), a :: e1 :: e2 :: lvs
  | "AlarmMemchr", a :: e1 :: e2 :: lvs
  | "AlarmSprintf", a :: e1 :: e2 :: lvs
  | "AlarmStrcat", a :: e1 :: e2 :: lvs
  | "AlarmStrcpy", a :: e1 :: e2 :: lvs
    when String.equal a alarm ->
      ( Chc.of_list [ Chc.Elt.FDNumeral e1; Chc.Elt.FDNumeral e2 ],
        List.map ~f:Chc.Elt.numer lvs |> Chc.of_list )
  | "AlarmMemcpy", a :: e1 :: e2 :: e3 :: lvs
  | "AlarmMemmove", a :: e1 :: e2 :: e3 :: lvs
  | "AlarmStrncmp", a :: e1 :: e2 :: e3 :: lvs
  | "AlarmStrncpy", a :: e1 :: e2 :: e3 :: lvs
    when String.equal a alarm ->
      ( Chc.of_list
          [ Chc.Elt.FDNumeral e1; Chc.Elt.FDNumeral e2; Chc.Elt.FDNumeral e3 ],
        List.map ~f:Chc.Elt.numer lvs |> Chc.of_list )
  | f, _ -> Logger.error "get_alarm_comps - not implemented: %s" f

let read_and_split file =
  In_channel.read_lines file |> List.map ~f:(fun l -> String.split ~on:'\t' l)

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
  let alarm_exps, alarm_lvs =
    Array.fold
      ~f:(fun alarm_comps file ->
        match (file, Filename.concat work_dir file |> read_and_split) with
        | "AlarmTaint.facts", _ | "AlarmBufferOverrunLib.facts", _ ->
            alarm_comps
        | _, hd :: [] -> get_alarm_comps alarm hd file
        | _ -> alarm_comps)
      ~init:(Chc.empty, Chc.empty) alarm_exp_files
  in
  (src, snk, alarm_exps, alarm_lvs)

let make_facts target_dir target_alarm ast out_dir =
  let maps = Maps.create_maps () in
  Maps.reset_maps maps;
  let spo_dir = Filename.concat target_dir "sparrow-out" in
  let alarm_dir = Filename.concat spo_dir ("taint/datalog/" ^ target_alarm) in
  L.info "Making facts from %sth alarm" (Filename.basename alarm_dir);
  Utils.parse_map ~rev_too:true alarm_dir "Exp.map" maps.Maps.exp_map
    ~rev_map:(Some maps.Maps.exp_rev_map);
  Utils.parse_map ~rev_too:true alarm_dir "Lval.map" maps.Maps.lval_map
    ~rev_map:(Some maps.Maps.lval_rev_map);
  Utils.parse_node_json spo_dir maps.Maps.loc_map maps.Maps.cmd_map;
  Cil.visitCilFile (new mkAstMap maps) ast;
  let du_facts = make_du_facts alarm_dir in
  Chc.pretty_dump (Filename.concat out_dir target_alarm) du_facts;
  Chc.sexp_dump (Filename.concat out_dir target_alarm) du_facts;
  (du_facts, get_alarm alarm_dir, maps)
