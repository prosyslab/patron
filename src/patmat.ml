module F = Format
open Z3env

let cnt = ref 0
let sym_map = Hashtbl.create 1000
let node_map = Hashtbl.create 1000

let mk_facts z3env solver work_dir =
  Hashtbl.reset sym_map;
  Hashtbl.reset node_map;
  let datalog_dir = Filename.concat work_dir "sparrow-out/interval/datalog" in
  let z3_add_symbol args sym sort =
    if Hashtbl.mem sym_map sym then
      let z3sym = Hashtbl.find sym_map sym in
      z3sym :: args
    else
      let z3sym = Z3.Expr.mk_numeral_int z3env.z3ctx !cnt sort in
      Hashtbl.add sym_map sym z3sym;
      if Z3.Sort.equal sort z3env.node then Hashtbl.add node_map sym z3sym;
      incr cnt;
      z3sym :: args
  in
  let app_fact (fact_file, func, arg_sorts) =
    let fact_file_path = Filename.concat datalog_dir fact_file in
    let ic = open_in fact_file_path in
    let rec loop () =
      try
        let line = input_line ic in
        let args =
          List.fold_left2 z3_add_symbol []
            (String.split_on_char '\t' line)
            arg_sorts
          |> List.rev
        in
        Z3env.add_fact solver func args;
        loop ()
      with End_of_file -> ()
    in
    loop ();
    close_in ic
  in
  List.iter app_fact z3env.facts

let get_transitive_closure z3env solver =
  Z3.Fixedpoint.add_rule solver z3env.dupath_r0 None;
  Z3.Fixedpoint.add_rule solver z3env.dupath_r1 None;
  Hashtbl.iter
    (fun n1 s1 ->
      Hashtbl.iter
        (fun n2 s2 ->
          let status =
            Z3.Fixedpoint.query solver
              (Z3.FuncDecl.apply z3env.dupath [ s1; s2 ])
          in
          match status with
          | Z3.Solver.UNSATISFIABLE -> ()
          | Z3.Solver.UNKNOWN ->
              Logger.log "Unknown: %s(%s),%s(%s)" n1 (Z3.Expr.to_string s1) n2
                (Z3.Expr.to_string s2)
          | Z3.Solver.SATISFIABLE ->
              Z3env.add_fact solver z3env.dupath [ s1; s2 ])
        node_map)
    node_map

let abstract_bug_pattern z3env =
  (* TODO: find abstract strategy (e.g. how to order relations?) *)
  let donor_facts = Z3.Fixedpoint.get_rules z3env.donor_solver in
  let status =
    Z3.Fixedpoint.query z3env.donee_solver (Z3.FuncDecl.apply z3env.bug [])
  in
  match status with
  | Z3.Solver.UNSATISFIABLE -> print_endline "No bug found"
  | Z3.Solver.SATISFIABLE -> (
      print_endline "Bug found";
      match Z3.Fixedpoint.get_answer z3env.donee_solver with
      | None -> print_endline "No answer"
      | Some answer ->
          print_endline "Instances:";
          answer |> Z3.Expr.to_string |> print_endline)
  | Z3.Solver.UNKNOWN -> print_endline "Unknown"

let dump ver_name sym_map solver out_dir =
  let sym_map_file = ver_name ^ "_symbol.map" |> Filename.concat out_dir in
  let sym_map_oc = open_out sym_map_file in
  Hashtbl.iter
    (fun sym z3sym ->
      Printf.fprintf sym_map_oc "%s\t%s\n" (Z3.Expr.to_string z3sym) sym)
    sym_map;
  close_out sym_map_oc;
  let solver_file = ver_name ^ ".smt2" |> Filename.concat out_dir in
  let solver_oc = open_out solver_file in
  Z3.Fixedpoint.to_string solver |> output_string solver_oc;
  close_out solver_oc

let pattern_match donor_dir donee_dir z3env =
  let out_dir = Filename.concat donee_dir !Cmdline.out_dir in
  Logger.log "Pattern matching...";
  mk_facts z3env z3env.donor_solver donor_dir;
  get_transitive_closure z3env z3env.donor_solver;
  dump "donor" sym_map z3env.donor_solver out_dir;
  mk_facts z3env z3env.donee_solver donee_dir;
  get_transitive_closure z3env z3env.donee_solver;
  dump "donee" sym_map z3env.donor_solver out_dir;
  Logger.log "Make facts done";
  abstract_bug_pattern z3env;
  Logger.log "Make pattern done"
