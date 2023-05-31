open Core
open Z3env
module Hashtbl = Stdlib.Hashtbl

let cnt = ref 0

let new_numer () =
  cnt := !cnt + 1;
  !cnt

let new_ign () = "IGN-" ^ string_of_int (new_numer ())
let new_argid () = "ArgId-" ^ string_of_int (new_numer ())

let mk_numer fix_exp maps sym sort =
  if
    (Z3.Sort.equal sort z3env.expr && fix_exp)
    || List.mem ~equal:Z3.Sort.equal [ z3env.binop_sort; z3env.unop_sort ] sort
  then (
    let map =
      if Z3.Sort.equal sort z3env.expr then maps.Maps.exp_map
      else if Z3.Sort.equal sort z3env.binop_sort then maps.Maps.binop_map
      else maps.Maps.unop_map
    in
    let const = Hashtbl.find map sym in
    if Hashtbl.mem Maps.const_map const then (
      let z3numer = Hashtbl.find Maps.const_map const in
      let nn = z3numer |> Z3.Expr.to_string |> int_of_string in
      Hashtbl.add maps.Maps.numeral_map nn sym;
      z3numer)
    else
      let nn = new_numer () in
      let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx nn sort in
      Hashtbl.add Maps.const_map const z3numer;
      Hashtbl.add maps.Maps.sym_map sym z3numer;
      Hashtbl.add maps.Maps.numeral_map nn sym;
      Bag.add_unit Maps.fixed_exps sym;
      z3numer)
  else if Hashtbl.mem maps.Maps.sym_map sym then
    Hashtbl.find maps.Maps.sym_map sym
  else
    let nn = new_numer () in
    let z3numer = Z3.Expr.mk_numeral_int z3env.z3ctx nn sort in
    Hashtbl.add maps.Maps.sym_map sym z3numer;
    Hashtbl.add maps.Maps.numeral_map nn sym;
    if Z3.Sort.equal sort z3env.node then
      Hashtbl.add maps.Maps.node_map sym z3numer;
    z3numer

let mk_args add_var_too maps ~fix_exp (numeral_args, var_args) sym sort =
  if Z3.Sort.equal sort z3env.int_sort then (
    let z3int =
      Z3.Arithmetic.Integer.mk_numeral_i z3env.z3ctx (int_of_string sym)
    in
    let z3int_var = Z3.Expr.mk_const_s z3env.z3ctx (new_argid ()) sort in
    Bag.add_unit Maps.var_bag z3int_var;
    (z3int :: numeral_args, z3int_var :: var_args))
  else
    let z3numer = mk_numer fix_exp maps sym sort in
    let var_args =
      if add_var_too then (
        if Z3.Sort.equal sort z3env.expr && fix_exp then z3numer :: var_args
        else if Bag.mem Maps.fixed_exps ~equal:String.equal sym then
          Hashtbl.find maps.Maps.sym_map sym :: var_args
        else
          let z3var = Z3.Expr.mk_const_s z3env.z3ctx sym sort in
          Bag.add_unit Maps.var_bag z3var;
          z3var :: var_args)
      else var_args
    in
    (z3numer :: numeral_args, var_args)

let apply_fact add_var_too maps datalog_dir solver (fact_file, func, arg_sorts)
    =
  if String.is_empty fact_file then ()
  else
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

let make ?(add_var_too = false) ~maps solver work_dir =
  let datalog_dir = Filename.concat work_dir "sparrow-out/taint/datalog" in
  let open_in_datalog fn =
    fn |> Filename.concat datalog_dir |> In_channel.create
  in
  let exp_map_ic = open_in_datalog "Exp.map" in
  Maps.make_map exp_map_ic maps.Maps.exp_map;
  let binop_map_ic = open_in_datalog "Bop.map" in
  Maps.make_map binop_map_ic maps.Maps.binop_map;
  let unop_map_ic = open_in_datalog "Uop.map" in
  Maps.make_map unop_map_ic maps.Maps.unop_map;
  List.iter ~f:(apply_fact add_var_too maps datalog_dir solver) z3env.funs
