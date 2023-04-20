open Core
open Z3env
module F = Format
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map
module Sys = Stdlib.Sys
module StrMap = Map.Make (String)

module RuleSet = Set.Make (struct
  type t = Z3.Expr.expr list

  let compare = compare_list Stdlib.compare
end)

module ExprSet = struct
  include Set.Make (struct
    type t = Z3.Expr.expr

    let compare = Z3.Expr.compare
  end)

  let pp fmt es =
    fold (fun e s -> s ^ Z3.Expr.to_string e ^ "\n") es "" |> F.fprintf fmt "%s"
end

let set2list set = ExprSet.fold (fun elt lst -> elt :: lst) set []
let z3env = mk_env ()
let cnt = ref 0

let new_numer () =
  cnt := !cnt + 1;
  !cnt

let new_ign () = "IGN-" ^ string_of_int (new_numer ())
let new_argid () = "ArgId-" ^ string_of_int (new_numer ())
let const_map = Hashtbl.create 1000
let fixed_exps = Bag.create ()
let var_bag = Bag.create ()

type maps = {
  sym_map : (string, Z3.Expr.expr) Hashtbl.t;
  node_map : (string, Z3.Expr.expr) Hashtbl.t;
  numeral_map : (int, string) Hashtbl.t;
  exp_map : (string, string) Hashtbl.t;
  binop_map : (string, string) Hashtbl.t;
  unop_map : (string, string) Hashtbl.t;
}

let create_maps () =
  {
    sym_map = Hashtbl.create 1000;
    node_map = Hashtbl.create 1000;
    numeral_map = Hashtbl.create 1000;
    exp_map = Hashtbl.create 1000;
    binop_map = Hashtbl.create 100;
    unop_map = Hashtbl.create 100;
  }

let reset_maps maps =
  Hashtbl.reset maps.sym_map;
  Hashtbl.reset maps.node_map;
  Hashtbl.reset maps.numeral_map;
  Hashtbl.reset maps.exp_map;
  Hashtbl.reset maps.binop_map;
  Hashtbl.reset maps.unop_map

let dump_smt ver_name solver out_dir =
  let solver_file = ver_name ^ ".smt2" |> Filename.concat out_dir in
  let solver_oc = Out_channel.create solver_file in
  Z3.Fixedpoint.to_string solver |> Out_channel.output_string solver_oc;
  Out_channel.close solver_oc

let dump_sym_map ver_name sym_map out_dir =
  let sym_map_file = ver_name ^ "_sym.map" |> Filename.concat out_dir in
  let sym_map_oc = Out_channel.create sym_map_file in
  Hashtbl.iter
    (fun sym z3sym ->
      Printf.fprintf sym_map_oc "%s\t%s\n" sym (Z3.Expr.to_string z3sym))
    sym_map;
  Out_channel.close sym_map_oc

let dump_node_map ver_name node_map out_dir =
  let sym_map_file = ver_name ^ "_node.map" |> Filename.concat out_dir in
  let sym_map_oc = Out_channel.create sym_map_file in
  Hashtbl.iter
    (fun sym z3sym ->
      Printf.fprintf sym_map_oc "%s\t%s\n" sym (Z3.Expr.to_string z3sym))
    node_map;
  Out_channel.close sym_map_oc

let dump_const_map const_map out_dir =
  let sym_map_file = "const.map" |> Filename.concat out_dir in
  let sym_map_oc = Out_channel.create sym_map_file in
  Hashtbl.iter
    (fun sym z3sym ->
      Printf.fprintf sym_map_oc "%s\t%s\n" sym (Z3.Expr.to_string z3sym))
    const_map;
  Out_channel.close sym_map_oc

let dump_str_map map_name ver_name map out_dir =
  let sym_map_file =
    ver_name ^ "_" ^ map_name ^ ".map" |> Filename.concat out_dir
  in
  let sym_map_oc = Out_channel.create sym_map_file in
  Hashtbl.iter (fun sym n -> Printf.fprintf sym_map_oc "%s\t%s\n" sym n) map;
  Out_channel.close sym_map_oc

let dump_exp_map = dump_str_map "exp"
let dump_binop_map = dump_str_map "binop"
let dump_unop_map = dump_str_map "unop"

let dump mode maps solver out_dir =
  dump_smt mode solver out_dir;
  dump_sym_map mode maps.sym_map out_dir;
  dump_node_map mode maps.node_map out_dir;
  dump_exp_map mode maps.exp_map out_dir;
  dump_binop_map mode maps.binop_map out_dir;
  dump_unop_map mode maps.unop_map out_dir;
  dump_const_map const_map out_dir

let mk_numer fix_exp maps sym sort =
  if
    (Z3.Sort.equal sort z3env.expr && fix_exp)
    || List.mem ~equal:Z3.Sort.equal [ z3env.binop_sort; z3env.unop_sort ] sort
  then (
    let map =
      if Z3.Sort.equal sort z3env.expr then maps.exp_map
      else if Z3.Sort.equal sort z3env.binop_sort then maps.binop_map
      else maps.unop_map
    in
    let const = Hashtbl.find map sym in
    if Hashtbl.mem const_map const then (
      let z3numer = Hashtbl.find const_map const in
      let nn = z3numer |> Z3.Expr.to_string |> int_of_string in
      Hashtbl.add maps.numeral_map nn sym;
      z3numer)
    else
      let nn = new_numer () in
      let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx nn sort in
      Hashtbl.add const_map const z3numer;
      Hashtbl.add maps.sym_map sym z3numer;
      Hashtbl.add maps.numeral_map nn sym;
      Bag.add_unit fixed_exps sym;
      z3numer)
  else if Hashtbl.mem maps.sym_map sym then Hashtbl.find maps.sym_map sym
  else
    let nn = new_numer () in
    let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx nn sort in
    Hashtbl.add maps.sym_map sym z3numer;
    Hashtbl.add maps.numeral_map nn sym;
    if Z3.Sort.equal sort z3env.node then Hashtbl.add maps.node_map sym z3numer;
    z3numer

type sem_cons =
  | Lt of sem_cons * sem_cons
  | Gt of sem_cons * sem_cons
  | FuncApply of string * sem_cons list
  | Add of sem_cons list
  | Mul of sem_cons list
  | Var of string
  | Const of Z.t

let rec parse_sem_cons = function
  | Sexp.List [ Sexp.Atom "<"; e1; e2 ] ->
      Lt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List [ Sexp.Atom ">"; e1; e2 ] ->
      Gt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List (Sexp.Atom "+" :: es) -> Add (List.map ~f:parse_sem_cons es)
  | Sexp.List (Sexp.Atom "*" :: es) -> Mul (List.map ~f:parse_sem_cons es)
  | Sexp.List (Sexp.Atom f :: es) -> FuncApply (f, List.map ~f:parse_sem_cons es)
  | Sexp.Atom s -> ( try Const (Z.of_string s) with _ -> Var s)
  | _ -> failwith "Unsupported Sexp"

type mode = Var | Numer

let rec sc2z3 mode maps = function
  | Lt (sc1, sc2) ->
      Z3.Arithmetic.mk_lt z3env.z3ctx (sc2z3 mode maps sc1)
        (sc2z3 mode maps sc2)
  | Gt (sc1, sc2) ->
      Z3.Arithmetic.mk_gt z3env.z3ctx (sc2z3 mode maps sc1)
        (sc2z3 mode maps sc2)
  | FuncApply ("SizeOf", args) ->
      Z3.FuncDecl.apply z3env.sizeof (List.map ~f:(sc2z3 mode maps) args)
  | FuncApply ("StrLen", args) ->
      Z3.FuncDecl.apply z3env.strlen (List.map ~f:(sc2z3 mode maps) args)
  | FuncApply ("IntVal", args) ->
      Z3.FuncDecl.apply z3env.intval (List.map ~f:(sc2z3 mode maps) args)
  | Add scs ->
      Z3.Arithmetic.mk_add z3env.z3ctx (List.map ~f:(sc2z3 mode maps) scs)
  | Mul scs ->
      Z3.Arithmetic.mk_mul z3env.z3ctx (List.map ~f:(sc2z3 mode maps) scs)
  | Var s -> (
      match mode with
      | Var -> Z3.Expr.mk_const_s z3env.z3ctx s z3env.value
      | Numer -> mk_numer false maps s z3env.value)
  | Const i -> Z3.Arithmetic.Integer.mk_numeral_s z3env.z3ctx (Z.to_string i)
  | _ -> failwith "Unsupported Semantic Constraint"

module AlarmMap = Map.Make (struct
  type t = String.t * String.t

  let compare (s1, t1) (s2, t2) =
    let cmp = String.compare s1 s2 in
    if cmp = 0 then String.compare t1 t2 else cmp
end)
(* (src node id, snk node id) -> error constraint *)

let mk_alarm_map work_dir =
  let io_err_cons_file =
    Filename.concat work_dir "sparrow-out/taint/datalog/IOErrorConstraint.facts"
  in
  try
    let alarms =
      In_channel.read_lines io_err_cons_file
      |> List.map ~f:(fun alarm ->
             match String.split ~on:'\t' alarm with
             | [ src; snk; err_cons ] -> (src, snk, err_cons)
             | _ -> Logger.error ~to_console:true "mk_alarm_map: invalid format")
    in
    List.fold_left ~init:AlarmMap.empty
      ~f:(fun am (src, snk, err_cons) ->
        AlarmMap.add (src, snk) (Sexp.of_string err_cons |> parse_sem_cons) am)
      alarms
  with _ ->
    Logger.debug "Empty Semantic Constraint";
    AlarmMap.empty

let mk_sem_cons ?(add_var_too = false) maps solver work_dir =
  let alarm_map = mk_alarm_map work_dir in
  let (src, snk), sem_cons = AlarmMap.choose alarm_map in
  let sc_numer = sc2z3 Numer maps sem_cons in
  Z3.Fixedpoint.add_rule solver sc_numer None;
  let src_numer = Hashtbl.find maps.node_map src in
  let snk_numer = Hashtbl.find maps.node_map snk in
  add_fact solver z3env.alarm [ src_numer; snk_numer ];
  if add_var_too then (
    let sc_var = sc2z3 Var maps sem_cons in
    Z3.Fixedpoint.add_rule z3env.pattern_solver sc_var None;
    let src_var = Z3.Expr.mk_const_s z3env.z3ctx src z3env.node in
    let snk_var = Z3.Expr.mk_const_s z3env.z3ctx snk z3env.node in
    add_fact z3env.pattern_solver z3env.alarm [ src_var; snk_var ])

let make_map ic map =
  let rec loop () =
    let line = In_channel.input_line ic in
    if Option.is_some line then (
      let pair = Option.value_exn line |> String.split ~on:'\t' in
      Hashtbl.add map (List.nth_exn pair 0) (List.nth_exn pair 1);
      loop ())
  in
  loop ();
  In_channel.close ic

let mk_args add_var_too maps ~fix_exp (numeral_args, var_args) sym sort =
  if Z3.Sort.equal sort z3env.int_sort then (
    let z3int =
      Z3.Arithmetic.Integer.mk_numeral_i z3env.z3ctx (int_of_string sym)
    in
    let z3int_var = Z3.Expr.mk_const_s z3env.z3ctx (new_argid ()) sort in
    Bag.add_unit var_bag z3int_var;
    (z3int :: numeral_args, z3int_var :: var_args))
  else
    let z3numer = mk_numer fix_exp maps sym sort in
    let var_args =
      if add_var_too then (
        if Z3.Sort.equal sort z3env.expr && fix_exp then z3numer :: var_args
        else if Bag.mem fixed_exps ~equal:String.equal sym then
          Hashtbl.find maps.sym_map sym :: var_args
        else
          let z3var = Z3.Expr.mk_const_s z3env.z3ctx sym sort in
          Bag.add_unit var_bag z3var;
          z3var :: var_args)
      else var_args
    in
    (z3numer :: numeral_args, var_args)

let apply_fact add_var_too maps datalog_dir solver (fact_file, func, arg_sorts)
    =
  let fact_file_path = Filename.concat datalog_dir fact_file in
  let ic = In_channel.create fact_file_path in
  let rec loop () =
    let line = In_channel.input_line ic in
    if Option.is_some line then (
      let line = Option.value_exn line in
      let numeral_args, var_args =
        List.fold2_exn ~init:([], [])
          ~f:
            (mk_args add_var_too maps
               ~fix_exp:(String.equal fact_file "LibCall.facts"))
          (String.split ~on:'\t' line)
          arg_sorts
      in
      let numeral_args = List.rev numeral_args in
      let var_args = List.rev var_args in
      add_fact solver func numeral_args;
      if add_var_too then add_fact z3env.pattern_solver func var_args;
      loop ())
  in
  loop ();
  In_channel.close ic

let mk_facts ?(add_var_too = false) ~maps solver work_dir =
  let datalog_dir = Filename.concat work_dir "sparrow-out/taint/datalog" in
  let open_in_datalog fn =
    fn |> Filename.concat datalog_dir |> In_channel.create
  in
  let exp_map_ic = open_in_datalog "Exp.map" in
  make_map exp_map_ic maps.exp_map;
  let binop_map_ic = open_in_datalog "Bop.map" in
  make_map binop_map_ic maps.binop_map;
  let unop_map_ic = open_in_datalog "Uop.map" in
  make_map unop_map_ic maps.unop_map;
  List.iter ~f:(apply_fact add_var_too maps datalog_dir solver) z3env.facts
(* TODO: generalize *)
(* mk_sem_cons ~add_var_too maps solver work_dir *)

let match_rule facts pattern =
  let solver = mk_fixedpoint z3env.z3ctx in
  reg_rel_to_solver z3env solver;
  let bug = Z3.FuncDecl.apply z3env.bug [] in
  let cond = Z3.Boolean.mk_and z3env.z3ctx (set2list pattern) in
  let vars_for_all = Bag.to_list var_bag in
  let bug_pattern_rule =
    mk_rule z3env.z3ctx vars_for_all
      (Z3.Boolean.mk_implies z3env.z3ctx cond bug)
  in
  List.iter ~f:(fun fact -> Z3.Fixedpoint.add_rule solver fact None) facts;
  Z3.Fixedpoint.add_rule solver bug_pattern_rule None;
  let status = Z3.Fixedpoint.query solver (Z3.FuncDecl.apply z3env.bug []) in
  match status with
  | Z3.Solver.UNSATISFIABLE -> None
  | Z3.Solver.SATISFIABLE -> Z3.Fixedpoint.get_answer solver
  | Z3.Solver.UNKNOWN -> None

let is_what subs rel =
  if Z3.Expr.to_string rel |> String.is_substring ~substring:subs then true
  else false

let is_cfpath = is_what "(CFPath"
let is_dupath = is_what "(DUPath"
let is_alloc = is_what "(Alloc"
let is_salloc = is_what "(SAlloc"
let is_set = is_what "(Set"
let is_call = is_what "(Call"
let is_libcall = is_what "(LibCall"
let is_var = is_what "(Var"
let is_skip = is_what "(Skip"
let is_ret = is_what "(Return"
let is_eval = is_what "(Eval"
let is_evallv = is_what "(EvalLv"
let is_memory = is_what "(Memory"
let is_sizeof = is_what "(SizeOf"
let is_strlen = is_what "(StrLen"
let is_intval = is_what "(IntVal"
let is_alarm = is_what "(Alarm"
let is_let = is_what "(let"
let is_binop = is_what "(BinOp"
let is_unop = is_what "(UnOp"
let is_cast = is_what "(Cast"
let is_arg = is_what "(Arg"
let ( ||| ) f1 f2 x = f1 x || f2 x
let is_sem_cons = is_sizeof ||| is_strlen ||| is_intval
let is_sem_rels = is_eval ||| is_evallv ||| is_memory

let is_node_rels =
  is_sem_rels ||| is_alloc ||| is_alloc ||| is_salloc ||| is_set ||| is_call
  ||| is_libcall ||| is_ret

let neg f x = not (f x)

let rec get_args_rec expr =
  Z3.Expr.get_args expr
  |> List.fold_left ~init:[] ~f:(fun args a ->
         if Z3.Expr.is_const a then a :: args else get_args_rec a @ args)
  |> List.rev

let collect_vars =
  Fun.flip
    (ExprSet.fold (fun r vars ->
         get_args_rec r |> List.fold_left ~init:vars ~f:(Fun.flip ExprSet.add)))
    ExprSet.empty

let collect_sem_vars =
  Fun.flip
    (ExprSet.fold (fun r vars ->
         get_args_rec r |> List.tl_exn
         |> List.fold_left ~init:vars ~f:(Fun.flip ExprSet.add)))
    ExprSet.empty

let collect_children var rels =
  ExprSet.filter
    (fun r ->
      get_args_rec r
      |> (if is_sem_rels r then (Fun.flip List.nth_exn) 1 else List.hd_exn)
      |> Z3.Expr.equal var)
    rels

let collect_correls var rels =
  ExprSet.filter
    (fun r ->
      get_args_rec r |> List.tl_exn
      |> (Fun.flip List.mem ~equal:Z3.Expr.equal) var)
    rels

let collect_rels var rels =
  ExprSet.filter
    (fun r -> get_args_rec r |> List.exists ~f:(Z3.Expr.equal var))
    rels

let collect_cfpath rels = ExprSet.filter is_cfpath rels
let collect_dupath rels = ExprSet.filter is_dupath rels

let is_removable rels rel =
  let have_no_child =
    List.for_all ~f:(fun var ->
        if
          Z3.Expr.get_sort var |> Z3.Sort.equal z3env.int_sort
          && Z3.Expr.is_numeral var
        then true
        else collect_children var rels |> ExprSet.cardinal = 0)
  in
  let vars = get_args_rec rel in
  if (is_cfpath ||| is_dupath) rel then
    List.exists
      ~f:(fun var ->
        let rels = collect_children var rels in
        ExprSet.filter (is_cfpath ||| is_dupath |> neg) rels
        |> ExprSet.cardinal = 0)
      vars
  else if is_binop rel then
    let v1 = List.nth_exn vars 1 in
    let v2 = List.nth_exn vars 2 in
    collect_children v1 rels |> ExprSet.cardinal = 0
    || collect_children v2 rels |> ExprSet.cardinal = 0
  else if is_unop rel then
    collect_children (List.nth_exn vars 1) rels |> ExprSet.cardinal = 0
  else if is_node_rels rel then
    match vars with
    | node_var :: tl_vars ->
        let alarm_rel = ExprSet.filter is_alarm rels |> ExprSet.choose in
        let src_snk = get_args_rec alarm_rel in
        let src_node, snk_node =
          (List.hd_exn src_snk, List.nth_exn src_snk 1)
        in
        (Z3.Expr.equal src_node ||| Z3.Expr.equal snk_node) node_var |> not
        && have_no_child tl_vars
    | _ -> Logger.error "is_removable: Invalid arguments"
  else List.tl_exn vars |> have_no_child

let subs_ign ~must_rel var rel rels =
  if ExprSet.mem rel must_rel then (rels, rel)
  else
    let rels' = ExprSet.remove rel rels in
    let func = Z3.Expr.get_func_decl rel in
    let rel' =
      get_args_rec rel
      |> List.map ~f:(fun arg ->
             if Z3.Expr.equal arg var then (
               let ign =
                 Z3.Expr.mk_const_s z3env.z3ctx (new_ign ())
                   (Z3.Expr.get_sort var)
               in
               Bag.add_unit var_bag ign;
               ign)
             else arg)
      |> Z3.FuncDecl.apply func
    in
    (ExprSet.add rel' rels', rel')

let rec elim_rel ~remove_cands ~must_rel ~must_var except_sem_cons sem_cons
    patch_facts =
  Logger.info "Try Matching... Elim Phase - # of rel: %d"
    (ExprSet.cardinal except_sem_cons);
  let rc = ExprSet.diff remove_cands must_rel in
  if ExprSet.is_empty rc then except_sem_cons
  else
    let selected = ExprSet.min_elt rc in
    Logger.debug "selected: %s" (Z3.Expr.to_string selected);
    let rc' = ExprSet.remove selected rc in
    let except_sem_cons' = ExprSet.remove selected except_sem_cons in
    let patch_matched = match_rule patch_facts except_sem_cons' in
    if Option.is_some patch_matched then (
      Logger.info "Patch Matched: selected rel is %s"
        (Z3.Expr.to_string selected);
      elim_rel ~remove_cands:rc
        ~must_rel:(ExprSet.add selected must_rel)
        ~must_var except_sem_cons sem_cons patch_facts)
    else (
      Logger.info "Patch Not Matched: removed rel is %s"
        (Z3.Expr.to_string selected);
      let new_remove_cand_vars = get_args_rec selected in
      let new_rcc =
        List.fold_left ~init:ExprSet.empty
          ~f:(fun rcc var ->
            collect_rels var except_sem_cons' |> ExprSet.union rcc)
          new_remove_cand_vars
      in
      let pat_cand' = ExprSet.union except_sem_cons' sem_cons in
      let new_rc = ExprSet.filter (is_removable pat_cand') new_rcc in
      elim_rel ~remove_cands:(ExprSet.union rc' new_rc) ~must_rel ~must_var
        except_sem_cons' sem_cons patch_facts)

and ignore_var ~ignore_cands ~must_rel ~must_var pat_cand
    pat_cand_except_sem_cons patch_facts =
  Logger.info "Try Matching... Ignore Phase";
  let ic = ExprSet.diff ignore_cands must_var in
  Logger.debug "ic: %s"
    (set2list ic |> List.map ~f:Z3.Expr.to_string |> String.concat ~sep:" ");
  if ExprSet.is_empty ic then pat_cand_except_sem_cons
  else
    let selected_var = ExprSet.min_elt ic in
    let sem_cons = ExprSet.diff pat_cand pat_cand_except_sem_cons in
    let correls =
      collect_correls selected_var pat_cand_except_sem_cons
      |> (Fun.flip ExprSet.diff) must_rel
    in
    if ExprSet.is_empty correls then
      ignore_var
        ~ignore_cands:(ExprSet.remove selected_var ic)
        ~must_rel
        ~must_var:(ExprSet.add selected_var must_var)
        pat_cand pat_cand_except_sem_cons patch_facts
    else
      let selected_rel = ExprSet.min_elt correls in
      let pat_cand_except_sem_cons', subst_rel =
        subs_ign ~must_rel selected_var selected_rel pat_cand_except_sem_cons
      in
      let pat_cand' = ExprSet.union pat_cand_except_sem_cons' sem_cons in
      Logger.debug "Current Patch Cand:\n%s"
        (set2list pat_cand'
        |> List.map ~f:Z3.Expr.to_string
        |> String.concat ~sep:"\n");
      let patch_matched = match_rule patch_facts pat_cand_except_sem_cons' in
      if Option.is_some patch_matched then (
        Logger.info "Patch Matched: Selected Var is %s"
          (Z3.Expr.to_string selected_var);
        ignore_var ~ignore_cands:ic ~must_rel
          ~must_var:(ExprSet.add selected_var must_var)
          pat_cand pat_cand_except_sem_cons patch_facts)
      else (
        Logger.info
          "Patch Not Matched: Ignored Var is %s\nSubstituted Rel is %s"
          (Z3.Expr.to_string selected_var)
          (Z3.Expr.to_string selected_rel);
        let remove_cands =
          ExprSet.filter (is_removable pat_cand') pat_cand_except_sem_cons'
        in
        let pcesc =
          elim_rel ~remove_cands ~must_rel ~must_var pat_cand_except_sem_cons'
            sem_cons patch_facts
        in
        if ExprSet.mem subst_rel pcesc then
          let pcesc' =
            ExprSet.map
              (fun rel ->
                if Z3.Expr.equal rel subst_rel then selected_rel else rel)
              pcesc
          in
          let pc' = ExprSet.union pcesc' sem_cons in
          ignore_var ~ignore_cands:ic
            ~must_rel:(ExprSet.add selected_rel must_rel)
            ~must_var pc' pcesc' patch_facts
        else
          let pc' = ExprSet.union pcesc sem_cons in
          let vars = collect_vars pc' in
          let ic' =
            ExprSet.filter
              (fun var ->
                collect_correls var pat_cand_except_sem_cons
                |> ExprSet.cardinal > 1)
              vars
          in
          ignore_var ~ignore_cands:ic' ~must_rel ~must_var pc' pcesc patch_facts)

let collect_nodes_after_alarm node cfpaths =
  let afters =
    ExprSet.fold
      (fun du nodes ->
        let from_to = Z3.Expr.get_args du in
        let _from, _to = (List.hd_exn from_to, List.nth_exn from_to 1) in
        if Z3.Expr.equal node _from then ExprSet.add _to nodes else nodes)
      cfpaths ExprSet.empty
  in
  let fliped_path n after = Z3.FuncDecl.apply z3env.cfpath [ after; n ] in
  ExprSet.filter
    (fun after ->
      fliped_path node after |> (Fun.flip ExprSet.mem) cfpaths |> not)
    afters

let collect_after_alarm node rels =
  let cfpaths = ExprSet.filter is_cfpath rels in
  let rels_except_cfpaths = ExprSet.diff rels cfpaths in
  let afters = collect_nodes_after_alarm node cfpaths in
  ExprSet.fold
    (fun after rs ->
      collect_children after rels_except_cfpaths |> ExprSet.union rs)
    afters ExprSet.empty

let remove_rels_after_alarms alarm syn_rels sem_rels =
  let except_sem_cons = ExprSet.union syn_rels sem_rels in
  let alarm_node = get_args_rec alarm |> List.tl_exn |> List.hd_exn in
  let after_rels = collect_after_alarm alarm_node except_sem_cons in
  ExprSet.diff except_sem_cons after_rels

let collect_sem_deps sem_rels sem_cons =
  let rec fixedpoint deps =
    let vars = collect_sem_vars deps in
    let new_deps =
      ExprSet.fold
        (fun var deps -> collect_rels var sem_rels |> ExprSet.union deps)
        vars deps
    in
    if ExprSet.equal new_deps deps then new_deps else fixedpoint new_deps
  in
  let must_vars = collect_vars sem_cons in
  let deps =
    ExprSet.fold
      (fun var deps -> collect_rels var sem_rels |> ExprSet.union deps)
      must_vars ExprSet.empty
  in
  fixedpoint deps

let remove_no_deps_from_sem_cons except_sem_cons sem_cons =
  let sem_rels = ExprSet.filter is_sem_rels except_sem_cons in
  let syn_rels = ExprSet.diff except_sem_cons sem_rels in
  let sem_deps = collect_sem_deps sem_rels sem_cons in
  (syn_rels, sem_deps)

let abstract_bug_pattern out_dir =
  let patch_facts = Z3.Fixedpoint.get_rules z3env.patch_solver in
  let pat_cand =
    Z3.Fixedpoint.get_rules z3env.pattern_solver
    |> List.filter ~f:(neg (is_skip ||| is_ret))
    |> ExprSet.of_list
  in
  let alarm =
    ExprSet.filter is_alarm pat_cand |> ExprSet.choose (* TODO: iteration *)
  in
  let sem_cons = ExprSet.filter is_sem_cons pat_cand in
  let sem_rels = ExprSet.filter is_sem_rels pat_cand in
  let syn_rels =
    ExprSet.filter (neg (is_alarm ||| is_sem_rels ||| is_sem_cons)) pat_cand
    |> ExprSet.add alarm
  in
  let except_sem_cons = remove_rels_after_alarms alarm syn_rels sem_rels in
  let syn_rels', sem_rels' =
    remove_no_deps_from_sem_cons except_sem_cons sem_cons
  in
  let except_sem_cons' = ExprSet.union syn_rels' sem_rels' in
  let pat_cand = ExprSet.union except_sem_cons' sem_cons in
  Logger.info "Pattern Candidate:\n%a\n" ExprSet.pp pat_cand;
  let remove_cands = ExprSet.filter (is_removable pat_cand) except_sem_cons' in
  let syn_rels'' =
    elim_rel ~remove_cands ~must_rel:sem_rels' ~must_var:ExprSet.empty
      except_sem_cons' sem_cons patch_facts
  in
  let except_sem_cons'' = ExprSet.union syn_rels'' sem_rels' in
  let pattern_smt_file = Filename.concat out_dir "pattern.smt" in
  let oc = Out_channel.create pattern_smt_file in
  ExprSet.union except_sem_cons'' sem_cons
  |> set2list
  |> List.map ~f:Z3.Expr.to_string
  |> String.concat ~sep:"\n"
  |> (fun s ->
       Logger.info "Bug Pattern Rule:\n%s" s;
       s)
  |> Out_channel.output_string oc;
  Out_channel.close oc;
  except_sem_cons''

let match_bug ver_name solver pattern out_dir =
  let facts =
    Z3.Fixedpoint.get_rules solver |> List.filter ~f:(neg is_sem_cons)
    (* Temporarily remove semantic constraint when match bug pattern *)
  in
  let sol = match_rule facts pattern in
  if Option.is_some sol then (
    let sol_smt_file = Filename.concat out_dir (ver_name ^ "_sol.smt") in
    let oc = Out_channel.create sol_smt_file in
    Option.value_exn sol |> Z3.Expr.to_string
    |> (fun s ->
         Logger.info "%s Matched - Sol:\n%s" ver_name s;
         s)
    |> Out_channel.output_string oc;
    Out_channel.close oc)
  else Logger.info "%s not Matched" ver_name

let atom2int = function
  | Sexp.Atom s -> int_of_string s
  | _ -> failwith "Invalid argument in atom2str"

let rec parse_sol = function
  | Sexp.List [ Sexp.Atom "asserted"; Sexp.List (Sexp.Atom rel :: args) ]
    when List.mem z3env.rels rel ~equal:String.equal ->
      [ (rel, List.map ~f:atom2int args) ]
  | Sexp.List ls ->
      List.fold_left ~f:(fun facts sexp -> facts @ parse_sol sexp) ~init:[] ls
  | _ -> []

let match_donor_donee donor_maps donee_maps out_dir =
  let donee_sol_file = Filename.concat out_dir "donee_sol.smt" in
  if Sys.file_exists donee_sol_file then (
    let oc = Filename.concat out_dir "sol.map" |> Out_channel.create in
    let fmt = F.formatter_of_out_channel oc in
    let donee_sol = Sexp.load_sexp donee_sol_file |> parse_sol in
    let donor_sol_file = Filename.concat out_dir "donor_sol.smt" in
    let donor_sol = Sexp.load_sexp donor_sol_file |> parse_sol in
    List.fold2_exn ~init:[]
      ~f:(fun mapped (donor_fun, donor_args) (donee_fun, donee_args) ->
        assert (String.equal donor_fun donee_fun);
        if String.equal donee_fun "Arg" then
          (List.nth_exn donor_args 0, List.nth_exn donee_args 0)
          :: (List.nth_exn donor_args 2, List.nth_exn donee_args 2)
          :: mapped
        else mapped @ List.zip_exn donor_args donee_args)
      donor_sol donee_sol
    |> List.map ~f:(fun (donor_num, donee_num) ->
           let donor_var = Hashtbl.find donor_maps.numeral_map donor_num in
           let donee_var = Hashtbl.find donee_maps.numeral_map donee_num in
           (donor_var, donee_var))
    |> List.dedup_and_sort ~compare:(fun (s1, _) (s1', _) ->
           String.compare s1 s1')
    |> List.iter ~f:(fun (donor_var, donee_var) ->
           F.fprintf fmt "%s\t%s\n" donor_var donee_var);
    F.pp_print_flush fmt ();
    Out_channel.close oc)

let pattern_match donor_dir patch_dir donee_dir =
  let out_dir = Filename.concat donee_dir !Cmdline.out_dir in
  Logger.info "Pattern matching...";
  let donor_maps, patch_maps, donee_maps =
    (create_maps (), create_maps (), create_maps ())
  in
  reset_maps donor_maps;
  reset_maps patch_maps;
  reset_maps donee_maps;
  Hashtbl.reset const_map;
  Bag.clear fixed_exps;
  Bag.clear var_bag;
  mk_facts ~add_var_too:true ~maps:donor_maps z3env.donor_solver donor_dir;
  mk_sem_cons ~add_var_too:true donor_maps z3env.donor_solver donor_dir;
  mk_facts ~maps:patch_maps z3env.patch_solver patch_dir;
  mk_facts ~maps:donee_maps z3env.donee_solver donee_dir;
  mk_sem_cons donee_maps z3env.donee_solver donee_dir;
  dump "donor" donor_maps z3env.donor_solver out_dir;
  dump "patch" patch_maps z3env.patch_solver out_dir;
  dump "donee" donee_maps z3env.donee_solver out_dir;
  Logger.info "Make facts done";
  let pattern = abstract_bug_pattern out_dir in
  match_bug "donor" z3env.donor_solver pattern out_dir;
  match_bug "donee" z3env.donee_solver pattern out_dir;
  match_donor_donee donor_maps donee_maps out_dir;
  Logger.info "Make pattern done"
