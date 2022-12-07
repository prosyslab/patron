module F = Format
open Z3env

let sym_map = Hashtbl.create 1000
let cnt = ref 0
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
  List.iter app_fact z3env.facts;
  Logger.log "Symbol table:";
  Hashtbl.iter
    (fun sym z3sym -> Logger.log "%s -> %s" (Z3.Expr.to_string z3sym) sym)
    sym_map

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

let abstract_bug_pattern donor donee = ()

let pattern_match donor_dir donee_dir =
  Logger.log "Pattern matching...";
  let z3env = Z3env.mk_env () in
  mk_facts z3env z3env.donor_solver donor_dir;
  get_transitive_closure z3env z3env.donor_solver;
  mk_facts z3env z3env.donee_solver donee_dir;
  get_transitive_closure z3env z3env.donee_solver;
  Logger.log "Make facts done";
  let donor = () in
  let donee = () in
  abstract_bug_pattern donor donee;
  Logger.log "Make pattern done";
  Logger.log "SMT Encoding Result - Donor:\n%s"
    (Z3.Fixedpoint.to_string z3env.donor_solver);
  Logger.log "SMT Encoding Result - Donee:\n%s"
    (Z3.Fixedpoint.to_string z3env.donee_solver);
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
