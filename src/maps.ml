open Core
module Hashtbl = Stdlib.Hashtbl
module F = Format

type t = {
  sym_map : (string, Z3.Expr.expr) Hashtbl.t;
  node_map : (string, Z3.Expr.expr) Hashtbl.t;
  numeral_map : (int, string) Hashtbl.t;
  exp_map : (string, string) Hashtbl.t;
  binop_map : (string, string) Hashtbl.t;
  unop_map : (string, string) Hashtbl.t;
}

let const_map : (string, Z3.Expr.expr) Hashtbl.t = Hashtbl.create 1000
let fixed_exps : string Bag.t = Bag.create ()
let var_bag : Z3.Expr.expr Bag.t = Bag.create ()

let create_maps () =
  {
    sym_map = Hashtbl.create 1000;
    node_map = Hashtbl.create 1000;
    numeral_map = Hashtbl.create 1000;
    exp_map = Hashtbl.create 1000;
    binop_map = Hashtbl.create 100;
    unop_map = Hashtbl.create 100;
  }

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

let reset_maps maps =
  Hashtbl.reset maps.sym_map;
  Hashtbl.reset maps.node_map;
  Hashtbl.reset maps.numeral_map;
  Hashtbl.reset maps.exp_map;
  Hashtbl.reset maps.binop_map;
  Hashtbl.reset maps.unop_map

let reset_globals () =
  Hashtbl.reset const_map;
  Bag.clear fixed_exps;
  Bag.clear var_bag

let dump_smt ver_name solver out_dir =
  let solver_file = ver_name ^ ".smt2" |> Filename.concat out_dir in
  let solver_oc = Out_channel.create solver_file in
  Z3.Fixedpoint.to_string solver |> Out_channel.output_string solver_oc;
  Out_channel.close solver_oc

let dump_map to_string map_name mode map out_dir =
  let sym_map_file =
    F.sprintf "%s_%s.map" mode map_name |> Filename.concat out_dir
  in
  let sym_map_oc = Out_channel.create sym_map_file in
  let sym_map_fmt = F.formatter_of_out_channel sym_map_oc in
  Hashtbl.iter
    (fun sym n -> F.fprintf sym_map_fmt "%s\t%s\n" sym (to_string n))
    map;
  F.pp_print_flush sym_map_fmt ();
  Out_channel.close sym_map_oc

let dump_z3_map = dump_map Z3.Expr.to_string
let dump_sym_map = dump_z3_map "sym"
let dump_node_map = dump_z3_map "node"
let dump_const_map = dump_z3_map "const"
let dump_str_map = dump_map Fun.id
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
  dump_const_map "" const_map out_dir
