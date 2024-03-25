open Core
module L = Logger
module F = Format
module Hashtbl = Stdlib.Hashtbl
module Set = Stdlib.Set

module PairSet = Set.Make (struct
  type t = int * int

  let compare (x1, y1) (x2, y2) =
    let c1 = Int.compare x1 x2 in
    if c1 = 0 then Int.compare y1 y2 else c1

  let equal a b = compare a b = 0
end)

let match_facts =
  List.fold2_exn
    ~f:(fun pairs f1 f2 ->
      match (f1, f2) with
      | (fn1, args1), (fn2, args2)
        when String.equal fn1 fn2 && List.length args1 = List.length args2 ->
          List.fold2_exn
            ~f:(fun ps a1 a2 -> PairSet.add (a1, a2) ps)
            ~init:pairs args1 args2
      | _ -> L.error "match_facts - invalid format")
    ~init:PairSet.empty

let dump_sol_map target_alarm buggy_maps target_maps out_dir pairs =
  let oc =
    Out_channel.create (Filename.concat out_dir (target_alarm ^ "_sol.map"))
  in
  let fmt = F.formatter_of_out_channel oc in
  PairSet.iter
    (fun (buggy_n, donee_n) ->
      if 0 <= buggy_n && buggy_n <= 21 then
        F.fprintf fmt "%s\t%s\n"
          (Z3utils.binop_of_int buggy_n)
          (Z3utils.binop_of_int donee_n)
      else if 22 <= buggy_n && buggy_n <= 24 then
        F.fprintf fmt "%s\t%s\n"
          (Z3utils.unop_of_int buggy_n)
          (Z3utils.unop_of_int donee_n)
      else
        F.fprintf fmt "%s\t%s\n"
          (Hashtbl.find buggy_maps.Maps.numeral_map buggy_n)
          (Hashtbl.find target_maps.Maps.numeral_map donee_n))
    pairs;
  F.pp_print_flush fmt ();
  Out_channel.close oc

let parse_dl_fact rel =
  match String.split ~on:'(' rel with
  | [ func_name; tl ] ->
      let args =
        String.chop_suffix_if_exists ~suffix:")." tl
        |> String.split ~on:','
        |> List.map ~f:(fun s -> int_of_string s)
      in
      (func_name, args)
  | _ -> L.error "parse_dl_fact - invalid format"

let is_dl_fact s =
  String.is_suffix s ~suffix:"." && not (String.is_substring ~substring:":-" s)

let parse_ans ans =
  String.split ~on:'|' ans
  |> List.fold_left
       ~f:(fun fs rel -> if is_dl_fact rel then parse_dl_fact rel :: fs else fs)
       ~init:[]

let match_ans buggy_maps target_maps target_alarm i_str out_dir =
  let buggy_ans =
    Filename.concat out_dir ("buggy_numer_" ^ i_str ^ "_ans.smt2")
    |> In_channel.read_all
  in
  let target_ans =
    Filename.concat out_dir (target_alarm ^ "_ans.smt2") |> In_channel.read_all
  in
  let buggy_facts = parse_ans buggy_ans in
  let target_facts = parse_ans target_ans in
  let pairs = match_facts buggy_facts target_facts in
  dump_sol_map target_alarm buggy_maps target_maps out_dir pairs
