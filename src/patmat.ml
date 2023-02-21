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

module ExprSet = Set.Make (struct
  type t = Z3.Expr.expr

  let compare = Stdlib.compare
end)

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
  numeral_map : (Z3.Expr.expr, string) Hashtbl.t;
  exp_map : (string, string) Hashtbl.t;
  exp_map_inv : (string, string) Hashtbl.t;
}

let create_maps () =
  {
    sym_map = Hashtbl.create 1000;
    node_map = Hashtbl.create 1000;
    numeral_map = Hashtbl.create 1000;
    exp_map = Hashtbl.create 1000;
    exp_map_inv = Hashtbl.create 1000;
  }

let reset_maps maps =
  Hashtbl.reset maps.sym_map;
  Hashtbl.reset maps.node_map;
  Hashtbl.reset maps.numeral_map;
  Hashtbl.reset maps.exp_map;
  Hashtbl.reset maps.exp_map_inv

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

let dump_exp_map ver_name exp_map out_dir =
  let sym_map_file = ver_name ^ "_exp.map" |> Filename.concat out_dir in
  let sym_map_oc = Out_channel.create sym_map_file in
  Hashtbl.iter
    (fun sym exp -> Printf.fprintf sym_map_oc "%s\t%s\n" sym exp)
    exp_map;
  Out_channel.close sym_map_oc

let dump mode maps solver out_dir =
  dump_smt mode solver out_dir;
  dump_sym_map mode maps.sym_map out_dir;
  dump_node_map mode maps.node_map out_dir;
  dump_exp_map mode maps.exp_map out_dir;
  dump_const_map const_map out_dir

let mk_numer fix_exp maps sym sort =
  if Z3.Sort.equal sort z3env.expr && fix_exp then (
    let const = Hashtbl.find maps.exp_map sym in
    if Hashtbl.mem const_map const then Hashtbl.find const_map const
    else
      let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx (new_numer ()) sort in
      Hashtbl.add const_map const z3numer;
      Hashtbl.add maps.sym_map sym z3numer;
      Hashtbl.add maps.numeral_map z3numer sym;
      Bag.add_unit fixed_exps sym;
      z3numer)
  else if Hashtbl.mem maps.sym_map sym then Hashtbl.find maps.sym_map sym
  else
    let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx (new_numer ()) sort in
    Hashtbl.add maps.sym_map sym z3numer;
    Hashtbl.add maps.numeral_map z3numer sym;
    if Z3.Sort.equal sort z3env.node then Hashtbl.add maps.node_map sym z3numer;
    z3numer

type sem_cons =
  | Lt of sem_cons * sem_cons
  | FuncApply of string * sem_cons list
  | Add of sem_cons list
  | Var of string

let rec parse_sem_cons = function
  | Sexp.List [ Sexp.Atom "<"; e1; e2 ] ->
      Lt (parse_sem_cons e1, parse_sem_cons e2)
  | Sexp.List (Sexp.Atom "+" :: es) -> Add (List.map ~f:parse_sem_cons es)
  | Sexp.List (Sexp.Atom f :: es) -> FuncApply (f, List.map ~f:parse_sem_cons es)
  | Sexp.Atom s -> Var s
  | _ -> failwith "Unsupported Sexp"

let rec sc2z3_var maps = function
  | Lt (sc1, sc2) ->
      Z3.Arithmetic.mk_lt z3env.z3ctx (sc2z3_var maps sc1) (sc2z3_var maps sc2)
  | FuncApply ("SizeOf", args) ->
      Z3.FuncDecl.apply z3env.sizeof (List.map ~f:(sc2z3_var maps) args)
  | FuncApply ("StrLen", args) ->
      Z3.FuncDecl.apply z3env.strlen (List.map ~f:(sc2z3_var maps) args)
  | Add scs ->
      Z3.Arithmetic.mk_add z3env.z3ctx (List.map ~f:(sc2z3_var maps) scs)
  | Var s -> Z3.Expr.mk_const_s z3env.z3ctx s z3env.value
  | _ -> failwith "Unsupported Semantic Constraint"

let rec sc2z3_numer maps = function
  | Lt (sc1, sc2) ->
      Z3.Arithmetic.mk_lt z3env.z3ctx (sc2z3_numer maps sc1)
        (sc2z3_numer maps sc2)
  | FuncApply ("SizeOf", args) ->
      Z3.FuncDecl.apply z3env.sizeof (List.map ~f:(sc2z3_numer maps) args)
  | FuncApply ("StrLen", args) ->
      Z3.FuncDecl.apply z3env.strlen (List.map ~f:(sc2z3_numer maps) args)
  | Add scs ->
      Z3.Arithmetic.mk_add z3env.z3ctx (List.map ~f:(sc2z3_numer maps) scs)
  | Var s -> mk_numer false maps s z3env.value
  | _ -> failwith "Unsupported Semantic Constraint"

let mk_sem_cons ?(add_var_too = false) maps solver work_dir =
  let sprintf_err_cons_file =
    Filename.concat work_dir
      "sparrow-out/interval/datalog/SprintfErrorConstraint.facts"
  in
  try
    let sem_cons = Sexp.load_sexp sprintf_err_cons_file |> parse_sem_cons in
    let sc_numer = sc2z3_numer maps sem_cons in
    Z3.Fixedpoint.add_rule solver sc_numer None;
    if add_var_too then
      let sc_var = sc2z3_var maps sem_cons in
      Z3.Fixedpoint.add_rule z3env.pattern_solver sc_var None
  with _ -> Logger.debug "Empty Semantic Constraint"

let make_exp_map ic exp_map exp_map_inv =
  let rec loop () =
    let line = In_channel.input_line ic in
    if Option.is_some line then (
      let pair = Option.value_exn line |> String.split ~on:'\t' in
      Hashtbl.add exp_map (List.nth_exn pair 0) (List.nth_exn pair 1);
      Hashtbl.add exp_map_inv (List.nth_exn pair 1) (List.nth_exn pair 0);
      loop ())
  in
  loop ()

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
  let datalog_dir = Filename.concat work_dir "sparrow-out/interval/datalog" in
  let exp_map_ic = Filename.concat datalog_dir "Exp.map" |> In_channel.create in
  make_exp_map exp_map_ic maps.exp_map maps.exp_map_inv;
  In_channel.close exp_map_ic;
  List.iter ~f:(apply_fact add_var_too maps datalog_dir solver) z3env.facts;
  mk_sem_cons ~add_var_too maps solver work_dir

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

let is_dupath = is_what "(DUPath"
let is_var = is_what "(Var"
let is_skip = is_what "(Skip"
let is_ret = is_what "(Return"
let is_sizeof = is_what "(SizeOf"
let is_formatstr = is_what "(FormatStr"
let ( ||| ) f1 f2 x = f1 x || f2 x
let is_sem_cons = is_sizeof ||| is_formatstr
let neg f x = not (f x)

let collect_vars =
  Fun.flip
    (ExprSet.fold (fun r vars ->
         Z3.Expr.get_args r
         |> List.fold_left ~init:vars ~f:(Fun.flip ExprSet.add)))
    ExprSet.empty

let collect_children var rels =
  ExprSet.filter
    (fun r -> Z3.Expr.get_args r |> List.hd_exn |> Z3.Expr.equal var)
    rels

let collect_correls var rels =
  ExprSet.filter
    (fun r ->
      Z3.Expr.get_args r |> List.tl_exn
      |> (Fun.flip List.mem ~equal:Z3.Expr.equal) var)
    rels

let collect_rels var rels =
  ExprSet.filter
    (fun r -> Z3.Expr.get_args r |> List.exists ~f:(Z3.Expr.equal var))
    rels

let collect_dupath rels = ExprSet.filter is_dupath rels

let is_removable rel rels =
  let vars = Z3.Expr.get_args rel in
  if is_dupath rel then
    List.exists
      ~f:(fun var ->
        let rels = collect_children var rels in
        let dupaths = collect_dupath rels in
        ExprSet.diff rels dupaths |> ExprSet.cardinal = 0)
      vars
  else
    List.tl_exn vars
    |> List.for_all ~f:(fun var ->
           if
             Z3.Expr.get_sort var |> Z3.Sort.equal z3env.int_sort
             && Z3.Expr.is_numeral var
           then true
           else collect_children var rels |> ExprSet.cardinal = 0)

let subs_ign ~must_rel var rel rels =
  if ExprSet.mem rel must_rel then (rels, rel)
  else
    let rels' = ExprSet.remove rel rels in
    let func = Z3.Expr.get_func_decl rel in
    let rel' =
      Z3.Expr.get_args rel
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

let rec elim_rel ~remove_cands ~must_rel ~must_var pat_cand
    pat_cand_except_sem_cons patch_facts =
  Logger.info "Try Matching... Elim Phase - # of rel: %d"
    (ExprSet.cardinal pat_cand_except_sem_cons);
  let rc = ExprSet.diff remove_cands must_rel in
  if ExprSet.is_empty rc then
    let vars = collect_vars pat_cand in
    let cand_vars =
      ExprSet.filter
        (fun var ->
          collect_correls var pat_cand_except_sem_cons |> ExprSet.cardinal > 1)
        vars
    in
    ignore_var ~ignore_cands:cand_vars ~must_rel ~must_var pat_cand
      pat_cand_except_sem_cons patch_facts
  else
    let selected = ExprSet.min_elt rc in
    let rc' = ExprSet.remove selected rc in
    (* Logger.debug "rc':\n%s" *)
    (*   (set2list rc' |> List.map ~f:Z3.Expr.to_string |> String.concat ~sep:"\n"); *)
    let pat_cand' = ExprSet.remove selected pat_cand in
    let pat_cand_except_sem_cons' =
      ExprSet.remove selected pat_cand_except_sem_cons
    in
    let patch_matched = match_rule patch_facts pat_cand_except_sem_cons' in
    if Option.is_some patch_matched then (
      Logger.info "Patch Matched: selected rel is %s"
        (Z3.Expr.to_string selected);
      elim_rel ~remove_cands:rc
        ~must_rel:(ExprSet.add selected must_rel)
        ~must_var pat_cand pat_cand_except_sem_cons patch_facts)
    else (
      Logger.info "Patch Not Matched: removed rel is %s"
        (Z3.Expr.to_string selected);
      let new_remove_cand_vars = Z3.Expr.get_args selected in
      (* Logger.debug "nrcv:%s" *)
      (*   (new_remove_cand_vars *)
      (*   |> List.map ~f:Z3.Expr.to_string *)
      (*   |> String.concat ~sep:" "); *)
      let new_rcc =
        List.fold_left ~init:ExprSet.empty
          ~f:(fun rcc var ->
            collect_rels var pat_cand_except_sem_cons' |> ExprSet.union rcc)
          new_remove_cand_vars
      in
      (* Logger.debug "new_rcc:\n%s" *)
      (*   (new_rcc |> set2list *)
      (*   |> List.map ~f:Z3.Expr.to_string *)
      (*   |> String.concat ~sep:"\n"); *)
      let new_rc = ExprSet.filter ((Fun.flip is_removable) pat_cand') new_rcc in
      (* Logger.debug "new_rc:\n%s" *)
      (*   (set2list new_rc *)
      (*   |> List.map ~f:Z3.Expr.to_string *)
      (*   |> String.concat ~sep:"\n"); *)
      elim_rel ~remove_cands:(ExprSet.union rc' new_rc) ~must_rel ~must_var
        pat_cand' pat_cand_except_sem_cons' patch_facts)

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
          ExprSet.filter
            ((Fun.flip is_removable) pat_cand')
            pat_cand_except_sem_cons'
        in
        let pcesc =
          elim_rel ~remove_cands ~must_rel ~must_var pat_cand'
            pat_cand_except_sem_cons' patch_facts
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

let abstract_bug_pattern () =
  let patch_facts = Z3.Fixedpoint.get_rules z3env.patch_solver in
  let pat_cand =
    Z3.Fixedpoint.get_rules z3env.pattern_solver
    |> List.filter ~f:(neg (is_skip ||| is_ret))
  in
  let pat_cand_except_sem_cons = List.filter ~f:(neg is_sem_cons) pat_cand in
  Logger.info "Pattern Candidate:\n%s\n"
    (pat_cand |> List.map ~f:Z3.Expr.to_string |> String.concat ~sep:"\n");
  let pat_cand_set = ExprSet.of_list pat_cand in
  let pat_cand_except_sem_cons_set = ExprSet.of_list pat_cand_except_sem_cons in
  let sem_cons_set = ExprSet.diff pat_cand_set pat_cand_except_sem_cons_set in
  let remove_cands =
    List.filter
      ~f:((Fun.flip is_removable) pat_cand_set)
      pat_cand_except_sem_cons
    |> ExprSet.of_list
  in
  let pattern =
    elim_rel ~remove_cands ~must_rel:sem_cons_set ~must_var:ExprSet.empty
      pat_cand_set pat_cand_except_sem_cons_set patch_facts
  in
  let pattern_include_sem_cons = ExprSet.union pattern sem_cons_set in
  pattern_include_sem_cons |> set2list
  |> List.map ~f:Z3.Expr.to_string
  |> String.concat ~sep:"\n"
  |> Logger.info "Bug Pattern Rule:\n%s";
  pattern

let match_bug_with_donee pattern =
  let donee_facts = Z3.Fixedpoint.get_rules z3env.donee_solver in
  let sol = match_rule donee_facts pattern in
  if Option.is_some sol then
    Option.value_exn sol |> Z3.Expr.to_string
    |> Logger.info "Donee Matched - Sol:\n%s"
  else Logger.info "Donee not Matched"

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
  mk_facts ~maps:patch_maps z3env.patch_solver patch_dir;
  mk_facts ~maps:donee_maps z3env.donee_solver donee_dir;
  dump "donor" donor_maps z3env.donor_solver out_dir;
  dump "patch" donor_maps z3env.patch_solver out_dir;
  dump "donee" donor_maps z3env.donee_solver out_dir;
  Logger.info "Make facts done";
  let pattern = abstract_bug_pattern () in
  match_bug_with_donee pattern;
  Logger.info "Make pattern done"
