open Core
open Z3env
module Hashtbl = Stdlib.Hashtbl
module Map = Stdlib.Map
module L = Logger
module Sys = Stdlib.Sys

module ASTMap = struct
  module Key = struct
    type t = Cil.stmt

    let compare x y =
      String.compare (Utils.string_of_stmt x) (Utils.string_of_stmt y)
  end

  module M = Map.Make (Key)

  type t = string M.t

  let make_map stmts =
    let _, map =
      List.fold_left ~init:(1, M.empty)
        ~f:(fun (id, map) stmt ->
          let next_id = id + 1 in
          (next_id, M.add stmt (id |> string_of_int) map))
        stmts
    in
    map
end

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

let find_fact_opt key (fact : Chc.Elt.t list list) =
  let extract_str = function
    | Chc.Elt.Const z -> Z.to_string z
    | Chc.Elt.Var s -> s
    | Chc.Elt.FDNumeral s -> s
    | _ -> failwith "find_fact_opt - not implemented"
  in
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
                CReturn1 (List.hd_exn arg, parse_loc loc)
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
                  parse_loc loc )
        | "assume" ->
            let arg_opt = find_fact_opt key assume_facts in
            if Option.is_none arg_opt then CNone
            else
              let arg = Option.value ~default:[] arg_opt in
              CAssume (List.hd_exn arg, parse_loc loc)
        | "set" ->
            let arg = find_fact_opt key set_facts in
            if Option.is_none arg then CNone
            else
              let arg = Option.value ~default:[] arg in
              CSet (List.hd_exn arg, List.nth_exn arg 1, parse_loc loc)
        | "alloc" -> (
            let arg = find_fact_opt key alloc_exp_facts in
            match arg with
            | None -> CNone
            | Some arg ->
                CAlloc (List.hd_exn arg, List.nth_exn arg 1, parse_loc loc))
        | "falloc" -> CNone
        | "salloc" -> CNone
        | _ ->
            print_endline "----------";
            print_endline (List.hd_exn cmd);
            print_endline "----------";
            failwith "Unknown Command"
      in
      match cmd with CNone | CSkip _ -> () | _ -> Hashtbl.add map cmd key)
    nodes

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
            | _ -> l @ [ stmt ])
          b.bstmts
      in
      b.bstmts <- stmts;
      ChangeDoChildrenPost (b, fun x -> x)
  end

let parse_ast target_dir =
  let file = Utils.get_target_file target_dir in
  if !Cilutil.printStages then ignore ();
  let cil = Frontc.parse file () in
  Rmtmps.removeUnusedTemps cil;
  Cil.visitCilFile (new blockVisitor) cil;
  cil

let mk_term s =
  if Z3utils.is_binop s || Z3utils.is_unop s then Chc.Elt.FDNumeral s
  else
    try Chc.Elt.Const (Z.of_string s)
    with _ ->
      let splitted = String.split ~on:'-' s in
      if List.length splitted = 1 then Chc.Elt.Var s
      else (
        incr numer_cnt;
        Chc.Elt.FDNumeral s)

(* TODO: Add Assume.facts *)
let file2func = function
  | "AllocExp.facts" -> "Alloc"
  | "Arg.facts" -> "Arg"
  | "Set.facts" -> "Set"
  | "BinOpExp.facts" -> "BinOp"
  | "UnOpExp.facts" -> "UnOp"
  | "CallExp.facts" -> "Call"
  | "CFPath.facts" -> "CFPath"
  | "DetailedDUEdge.facts" -> "DetailedDUEdge"
  | "DUEdge.facts" -> "DUEdge"
  | "DUPath.facts" -> "DUPath"
  | "GlobalVar.facts" | "LocalVar.facts" -> "Var"
  | "LibCallExp.facts" -> "LibCall"
  | "LvalExp.facts" -> "LvalExp"
  | "Return.facts" -> "Return"
  | "SAllocExp.facts" -> "SAlloc"
  | "Skip.facts" -> "Skip"
  | "EvalLv.facts" -> "EvalLv"
  | "Assume.facts" -> "Assume"
  | f -> L.error "file2func - wrong filename: %s" f

let parse_cf_facts datalog_dir fact_file =
  let func_name = file2func fact_file in
  let fact_file_path = Filename.concat datalog_dir fact_file in
  let elt_lst =
    In_channel.read_lines fact_file_path
    |> List.fold_left ~init:[] ~f:(fun lst line ->
           let arg_lst = String.split ~on:'\t' line in
           let args = List.map ~f:mk_term arg_lst in
           let elt = Chc.Elt.FuncApply (func_name, args) in
           (* let map =
                Utils.StrMap.add (List.hd_exn arg_lst) (List.tl_exn arg_lst) map
              in *)
           elt :: lst)
  in
  List.rev elt_lst |> Chc.of_list

(* TODO: combine symdiff making process and make_cf_facts wrt the file IO *)
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

let mk_parent_tuples parent stmts =
  List.fold_left ~init:[] ~f:(fun acc s -> (parent, s) :: acc) stmts

let match_eq_nodes ast_node maps =
  let cfg = maps.Maps.cfg_map in
  let ast_map = maps.Maps.ast_map in
  let node_map = maps.Maps.node_map in
  let ast_id = Hashtbl.find ast_map ast_node |> string_of_int in
  let cfg_id =
    Hashtbl.fold
      (fun cnode id acc ->
        let bool =
          match (ast_node.Cil.skind, cnode) with
          | Cil.Instr i, cn -> (
              if List.length i = 0 then false
              else
                match (List.hd_exn i, cn) with
                | Cil.Call (_, _, _, loc), Maps.CfgNode.CCall (_, _, cloc) ->
                    SymDiff.SDiff.eq_line loc cloc
                | Cil.Set (_, _, loc), Maps.CfgNode.CSet (_, _, cloc)
                | Cil.Set (_, _, loc), Maps.CfgNode.CAlloc (_, _, cloc)
                | Cil.Set (_, _, loc), Maps.CfgNode.CSalloc (_, _, cloc)
                | Cil.Set (_, _, loc), Maps.CfgNode.CFalloc (_, _, cloc) ->
                    SymDiff.SDiff.eq_line loc cloc
                | _ -> false)
          | Cil.If (_, _, _, loc), Maps.CfgNode.CIf cloc ->
              SymDiff.SDiff.eq_line loc cloc
          | Cil.Return (_, loc), Maps.CfgNode.CReturn1 (_, cloc)
          | Cil.Return (_, loc), Maps.CfgNode.CReturn2 cloc ->
              SymDiff.SDiff.eq_line loc cloc
          | _ -> false
        in
        if bool then id :: acc else acc)
      cfg []
    |> fun x -> if List.length x = 0 then None else Some (List.hd_exn x)
  in
  if Option.is_none cfg_id then None
  else (
    Hashtbl.add node_map (Option.value_exn cfg_id) ast_id;
    Some
      (Chc.Elt.FuncApply
         ( "EqNode",
           [
             FDNumeral (Option.value_exn cfg_id); FDNumeral ("AstNode-" ^ ast_id);
           ] )))

let make_ast_facts (maps : Maps.t) stmts =
  let parent_tups =
    List.fold_left ~init:[]
      ~f:(fun acc s ->
        match s.Cil.skind with
        | Cil.Block b | Cil.Loop (b, _, _, _) ->
            mk_parent_tuples s b.bstmts @ acc
        | Cil.If (_, tb, eb, _) ->
            mk_parent_tuples s tb.bstmts @ mk_parent_tuples s eb.bstmts @ acc
        | _ -> acc)
      stmts
    |> List.fold_left ~init:[] ~f:(fun acc (parent, child) ->
           let parent =
             Hashtbl.find maps.ast_map parent |> string_of_int |> fun n ->
             [ "AstNode"; n ] |> String.concat ~sep:"-"
           in
           let child =
             Hashtbl.find maps.ast_map child |> string_of_int |> fun n ->
             [ "AstNode"; n ] |> String.concat ~sep:"-"
           in
           (parent, child) :: acc)
  in
  let parent_rel =
    List.fold_left ~init:[]
      ~f:(fun acc (parent, child) ->
        Chc.Elt.FuncApply ("AstParent", [ FDNumeral parent; FDNumeral child ])
        :: acc)
      parent_tups
    |> Chc.of_list
  in
  let eqnode_rel =
    List.fold_left ~init:[]
      ~f:(fun acc stmt ->
        match_eq_nodes stmt maps |> fun x ->
        if Option.is_none x then acc else Option.value_exn x :: acc)
      stmts
    |> Chc.of_list
  in
  Chc.union parent_rel eqnode_rel

let read_and_split file =
  In_channel.read_lines file |> List.map ~f:(fun l -> String.split ~on:'\t' l)

exception Not_impl_aexp

let get_aexp alarm splited filename =
  match Filename.basename filename |> Filename.chop_extension with
  | "AlarmDivExp" -> (
      match splited with
      | [ a; _; divisor ] when String.equal a alarm ->
          Chc.singleton (Chc.Elt.FDNumeral divisor)
      | _ -> Chc.empty)
  | f ->
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
  Utils.parse_map alarm_dir maps.exp_map;
  let stmts = Utils.extract_stmts ast in
  Maps.make_ast_map stmts maps.ast_map;
  let facts =
    make_cf_facts alarm_dir cfg maps.cfg_map
    |> Chc.union (make_ast_facts maps stmts)
  in
  Chc.pretty_dump (Filename.concat out_dir target_alarm) facts;
  Chc.sexp_dump (Filename.concat out_dir target_alarm) facts;
  (facts, get_alarm alarm_dir)
