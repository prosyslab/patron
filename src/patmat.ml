open Core
open Z3env
module F = Format
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set
module Map = Stdlib.Map

let cnt = ref 0
let sym_map = Hashtbl.create 1000
let node_map = Hashtbl.create 1000
let numeral_map = Hashtbl.create 1000
let const_map = Hashtbl.create 1000
let var_bag = Bag.create ()

let dump ver_name sym_map solver out_dir =
  let sym_map_file = ver_name ^ "_symbol.map" |> Filename.concat out_dir in
  let sym_map_oc = Out_channel.create sym_map_file in
  Hashtbl.iter
    (fun sym z3sym ->
      Printf.fprintf sym_map_oc "%s\t%s\n" (Z3.Expr.to_string z3sym) sym)
    sym_map;
  Out_channel.close sym_map_oc;
  let solver_file = ver_name ^ ".smt2" |> Filename.concat out_dir in
  let solver_oc = Out_channel.create solver_file in
  Z3.Fixedpoint.to_string solver |> Out_channel.output_string solver_oc;
  Out_channel.close solver_oc

module ExpMap = Map.Make (String)

let mk_facts ?(add_var_too = false) z3env solver work_dir =
  Hashtbl.reset sym_map;
  Hashtbl.reset node_map;
  let datalog_dir = Filename.concat work_dir "sparrow-out/interval/datalog" in
  let exp_map_ic = Filename.concat datalog_dir "Exp.map" |> In_channel.create in
  let rec loop exp_map =
    let line = In_channel.input_line exp_map_ic in
    if Option.is_some line then
      let pair = Option.value_exn line |> String.split ~on:'\t' in
      ExpMap.add (List.nth_exn pair 0) (List.nth_exn pair 1) exp_map |> loop
    else exp_map
  in
  let exp_map = loop ExpMap.empty in
  In_channel.close exp_map_ic;
  let z3_add_symbol ~fix_exp (numeral_args, var_args) sym sort =
    if Z3.Sort.equal sort z3env.int_sort then
      let z3int =
        Z3.Arithmetic.Integer.mk_numeral_i z3env.z3ctx (int_of_string sym)
      in
      (z3int :: numeral_args, z3int :: var_args)
    else
      let z3numer =
        if Z3.Sort.equal sort z3env.expr && fix_exp then (
          let const = ExpMap.find sym exp_map in
          if Hashtbl.mem const_map const then Hashtbl.find const_map const
          else
            let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx !cnt sort in
            Hashtbl.add const_map const z3numer;
            Hashtbl.add sym_map sym z3numer;
            Hashtbl.add numeral_map z3numer sym;
            if Z3.Sort.equal sort z3env.node then
              Hashtbl.add node_map sym z3numer;
            incr cnt;
            z3numer)
        else if Hashtbl.mem sym_map sym then Hashtbl.find sym_map sym
        else
          let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx !cnt sort in
          Hashtbl.add sym_map sym z3numer;
          Hashtbl.add numeral_map z3numer sym;
          if Z3.Sort.equal sort z3env.node then Hashtbl.add node_map sym z3numer;
          incr cnt;
          z3numer
      in
      let var_args =
        if add_var_too then (
          if Z3.Sort.equal sort z3env.expr && fix_exp then z3numer :: var_args
          else
            let z3var = Z3.Expr.mk_const_s z3env.z3ctx sym sort in
            Bag.add_unit var_bag z3var;
            z3var :: var_args)
        else var_args
      in
      (z3numer :: numeral_args, var_args)
  in
  let app_fact (fact_file, func, arg_sorts) =
    let fact_file_path = Filename.concat datalog_dir fact_file in
    let ic = In_channel.create fact_file_path in
    let rec loop () =
      let line = In_channel.input_line ic in
      if Option.is_some line then (
        let line = Option.value_exn line in
        let numeral_args, var_args =
          List.fold2_exn ~init:([], [])
            ~f:(z3_add_symbol ~fix_exp:(String.equal fact_file "LibCall.facts"))
            (String.split ~on:'\t' line)
            arg_sorts
        in
        let numeral_args = List.rev numeral_args in
        let var_args = List.rev var_args in
        Z3env.add_fact solver func numeral_args;
        if add_var_too then Z3env.add_fact z3env.pattern_solver func var_args;
        loop ())
    in
    loop ();
    In_channel.close ic
  in
  List.iter ~f:app_fact z3env.facts

let get_transitive_closure ?(add_var_too = false) z3env solver =
  Z3.Fixedpoint.add_rule solver z3env.dupath_r0 None;
  Z3.Fixedpoint.add_rule solver z3env.dupath_r1 None;
  Hashtbl.iter
    (fun s1 n1 ->
      Hashtbl.iter
        (fun s2 n2 ->
          let status =
            Z3.Fixedpoint.query solver
              (Z3.FuncDecl.apply z3env.dupath [ n1; n2 ])
          in
          match status with
          | Z3.Solver.UNSATISFIABLE -> ()
          | Z3.Solver.UNKNOWN ->
              Logger.log "Unknown: %s(%s),%s(%s)" s1 (Z3.Expr.to_string n1) s2
                (Z3.Expr.to_string n2)
          | Z3.Solver.SATISFIABLE ->
              (if add_var_too then
               let v1 = Z3.Expr.mk_const_s z3env.z3ctx s1 z3env.node in
               let v2 = Z3.Expr.mk_const_s z3env.z3ctx s2 z3env.node in
               Z3env.add_fact z3env.pattern_solver z3env.dupath [ v1; v2 ]);
              Z3env.add_fact solver z3env.dupath [ n1; n2 ])
        node_map)
    node_map

let match_rule z3env solver facts rule =
  List.iter ~f:(fun fact -> Z3.Fixedpoint.add_rule solver fact None) facts;
  Z3.Fixedpoint.add_rule solver rule None;
  let status = Z3.Fixedpoint.query solver (Z3.FuncDecl.apply z3env.bug []) in
  match status with
  | Z3.Solver.UNSATISFIABLE -> None
  | Z3.Solver.SATISFIABLE -> Z3.Fixedpoint.get_answer solver
  | Z3.Solver.UNKNOWN -> None

module RuleSet = Set.Make (struct
  type t = Z3.Expr.expr list

  let compare = compare_list Stdlib.compare
end)

let rec pick picked_facts fact_sign pat_cand =
  if List.length pat_cand = 0 then picked_facts
  else if fact_sign land 1 = 1 then
    let fact = List.hd_exn pat_cand in
    let pat_cand = List.tl_exn pat_cand in
    pick (fact :: picked_facts) (fact_sign asr 1) pat_cand
  else pick picked_facts (fact_sign asr 1) (List.tl_exn pat_cand)

let int_size = Sys.word_size_in_bits - 1

let int2bin =
  let buf = Bytes.create int_size in
  fun n ->
    for i = 0 to int_size - 1 do
      let pos = int_size - 1 - i in
      Bytes.set buf pos (if n land (1 lsl i) <> 0 then '1' else '0')
    done;
    (* skip leading zeros *)
    match Stdlib.Bytes.index_opt buf '1' with
    | None -> "0b0"
    | Some i -> "0b" ^ Stdlib.Bytes.sub_string buf i (int_size - i)

let is_what subs rule =
  if Z3.Expr.to_string rule |> String.is_substring ~substring:subs then true
  else false

let is_duedge = is_what "(DUEdge"
let is_var = is_what "(Var"
let is_skip = is_what "(Skip"
let is_ret = is_what "(Return"
let ( ||| ) f1 f2 x = f1 x || f2 x

let abstract_bug_pattern z3env =
  let donor_facts = Z3.Fixedpoint.get_rules z3env.donor_solver in
  let patch_facts = Z3.Fixedpoint.get_rules z3env.patch_solver in
  let donee_facts = Z3.Fixedpoint.get_rules z3env.donee_solver in
  let pat_cand =
    Z3.Fixedpoint.get_rules z3env.pattern_solver
    |> List.filter ~f:(fun r ->
           r |> (is_duedge ||| is_var ||| is_skip ||| is_ret) |> not)
  in
  Logger.log "Pattern Candidate:\n%s\n"
    (pat_cand |> List.map ~f:Z3.Expr.to_string |> String.concat ~sep:"\n");
  List.iter ~f:(fun r -> Z3.Expr.to_string r |> F.printf "%s\n") pat_cand;
  let vars_for_all = Bag.to_list var_bag in
  let rec try_matching fact_sign pat_cand =
    Logger.log "Try Matching... fact_sign: %s" (int2bin fact_sign);
    let picked_facts = pick [] fact_sign pat_cand in
    let implies =
      Z3.Boolean.mk_and z3env.z3ctx picked_facts
      |> Z3.Boolean.mk_implies z3env.z3ctx
    in
    let bug_pattern_rule =
      implies (Z3.FuncDecl.apply z3env.bug [])
      |> mk_rule z3env.z3ctx vars_for_all
    in
    let donor_solver = mk_fixedpoint z3env.z3ctx in
    reg_rel_to_solver z3env donor_solver;
    let donor_matched =
      match_rule z3env donor_solver donor_facts bug_pattern_rule
    in
    if Option.is_some donor_matched then (
      let patch_solver = mk_fixedpoint z3env.z3ctx in
      reg_rel_to_solver z3env patch_solver;
      let patch_matched =
        match_rule z3env patch_solver patch_facts bug_pattern_rule
      in
      if Option.is_none patch_matched then (
        let donee_solver = mk_fixedpoint z3env.z3ctx in
        reg_rel_to_solver z3env donee_solver;
        let donee_matched =
          match_rule z3env donee_solver donee_facts bug_pattern_rule
        in
        if Option.is_some donee_matched then bug_pattern_rule
        else try_matching (fact_sign - 1) pat_cand)
      else try_matching (fact_sign - 1) pat_cand)
    else try_matching (fact_sign - 1) pat_cand
  in
  let fact_sign = Int.( ** ) 2 (List.length pat_cand) - 1 in
  try_matching fact_sign pat_cand |> Z3.Expr.to_string |> print_endline

(* let rec try_matching filtered_rules pat_cand added_facts = *)
(*   match pat_cand with *)
(*   | [] -> *)
(*       let implies = *)
(*         Z3.Boolean.mk_and z3env.z3ctx added_facts *)
(*         |> Z3.Boolean.mk_implies z3env.z3ctx *)
(*       in *)
(*       let bug_pattern_rule = *)
(*         implies (Z3.FuncDecl.apply z3env.bug []) *)
(*         |> mk_rule z3env.z3ctx vars_for_all *)
(*       in *)
(*       let donor_solver = mk_fixedpoint z3env.z3ctx in *)
(*       reg_rel_to_solver z3env donor_solver; *)
(*       let donor_matched = *)
(*         match_rule z3env donor_solver donor_facts bug_pattern_rule *)
(*       in *)
(*       if Option.is_none donor_matched then filtered_rules *)
(*       else *)
(*         let patch_solver = mk_fixedpoint z3env.z3ctx in *)
(*         reg_rel_to_solver z3env patch_solver; *)
(*         let patch_matched = *)
(*           match_rule z3env patch_solver patch_facts bug_pattern_rule *)
(*         in *)
(*         if Option.is_some patch_matched then filtered_rules *)
(*         else *)
(*           let donee_solver = mk_fixedpoint z3env.z3ctx in *)
(*           reg_rel_to_solver z3env donee_solver; *)
(*           let donee_matched = *)
(*             match_rule z3env donee_solver donee_facts bug_pattern_rule *)
(*           in *)
(*           if Option.is_none donee_matched then filtered_rules *)
(*           else RuleSet.add added_facts filtered_rules *)
(*   | r :: rs -> *)
(*       RuleSet.union *)
(*         (try_matching filtered_rules rs added_facts) *)
(*         (try_matching filtered_rules rs (r :: added_facts)) *)
(* in *)
(* let matched_pattern = try_matching RuleSet.empty pat_cand [] in *)
(* RuleSet.cardinal matched_pattern |> string_of_int |> print_endline *)

let pattern_match donor_dir patch_dir donee_dir z3env =
  let out_dir = Filename.concat donee_dir !Cmdline.out_dir in
  Logger.log "Pattern matching...";
  Hashtbl.reset numeral_map;
  Hashtbl.reset const_map;
  Bag.clear var_bag;
  mk_facts ~add_var_too:true z3env z3env.donor_solver donor_dir;
  get_transitive_closure ~add_var_too:true z3env z3env.donor_solver;
  dump "donor" sym_map z3env.donor_solver out_dir;
  (* dump "pattern" sym_map z3env.pattern_solver out_dir; *)
  mk_facts z3env z3env.patch_solver patch_dir;
  get_transitive_closure z3env z3env.patch_solver;
  dump "patch" sym_map z3env.patch_solver out_dir;
  mk_facts z3env z3env.donee_solver donee_dir;
  get_transitive_closure z3env z3env.donee_solver;
  dump "donee" sym_map z3env.donee_solver out_dir;
  Logger.log "Make facts done";
  abstract_bug_pattern z3env;
  Logger.log "Make pattern done"
