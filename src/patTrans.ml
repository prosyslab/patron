open Core
open Z3utils
module L = Logger
module Hashtbl = Stdlib.Hashtbl
module TF = Transformer

module PairSet = Set.Make (struct
  type t = int * int

  let compare (x1, y1) (x2, y2) =
    let c1 = Int.compare x1 x2 in
    if c1 = 0 then Int.compare y1 y2 else c1

  let equal a b = compare a b = 0
end)

let fold_db f db_dir =
  Sys_unix.fold_dir ~init:(false, [])
    ~f:(fun (matched, donors) cand ->
      L.debug "Try matching with %s..." cand;
      let cand_path = Filename.concat db_dir cand in
      if f cand_path then (true, cand :: donors) else (matched, donors))
    db_dir

let match_bug out_dir donee donee_maps pattern =
  let status =
    Chc.pattern_match out_dir "donee" donee_maps donee pattern [ z3env.bug ]
  in
  if Option.is_some status then (
    Option.iter
      ~f:(fun ans ->
        L.info "Donee Matched";
        Z3utils.dump_expr_to_smt "donee_ans" ans out_dir)
      status;
    true)
  else (
    L.info "Donee Not Matched";
    false)

let try_until_matched out_dir donee donee_maps pattern =
  let errtrace_rule = Chc.find_rule "ErrTrace" pattern in
  let syntactic_pattern = Chc.Elt.get_body errtrace_rule |> Chc.of_list in
  let removable = Chc.collect_removable syntactic_pattern in
  if match_bug out_dir donee donee_maps pattern then true
  else
    let rec loop removable =
      if Chc.is_empty removable then false
      else
        let cand = Chc.min_elt removable in
        let syntactic_pattern' =
          Chc.remove cand syntactic_pattern |> Chc.to_list
        in
        let pattern' = Chc.update_rule "ErrTrace" syntactic_pattern' pattern in
        if match_bug out_dir donee donee_maps pattern' then true
        else
          let removable' = Chc.remove cand removable in
          loop removable'
    in
    loop removable

let match_bug_for_one_prj out_dir donee donee_maps donor_cand_path =
  let pattern =
    Parser.parse_chc (Filename.concat donor_cand_path "pattern_mach.chc")
    |> Chc.map Chc.Elt.numer2var
  in
  try_until_matched out_dir donee donee_maps pattern

let rec find_bug = function
  | Sexp.List
      (Sexp.List (Sexp.Atom "_" :: Sexp.Atom "hyper-res" :: _)
      :: Sexp.List (Sexp.Atom "asserted" :: _)
      :: tl) as s
    when List.last tl |> Option.exists ~f:(Sexp.equal (Sexp.Atom "Bug")) ->
      Some s
  | Sexp.List ss ->
      List.fold_left ~init:None
        ~f:(fun mp s -> if Option.is_some mp then mp else find_bug s)
        ss
  | _ -> None

let rec find_a a = function
  | Sexp.List [ Sexp.Atom x; r ] when String.equal a x -> Some r
  | Sexp.List ss ->
      List.fold_left ~init:None
        ~f:(fun mp s -> if Option.is_some mp then mp else find_a a s)
        ss
  | _ -> None

let rec find_errtrace_internal ans = function
  | Sexp.List
      (Sexp.List (Sexp.Atom "_" :: Sexp.Atom "hyper-res" :: _)
      :: Sexp.List (Sexp.Atom "asserted" :: _)
      :: tl) as s
    when List.last tl
         |> Option.exists ~f:(function
              | Sexp.List (Sexp.Atom "ErrTrace" :: _) -> true
              | _ -> false) ->
      Some s
  | Sexp.Atom a when String.is_prefix a ~prefix:"a!" ->
      let a_rule = find_a a ans |> Option.value_exn in
      find_errtrace_internal ans a_rule
  | _ -> None

let find_errtrace ans = function
  | Sexp.List
      (Sexp.List (Sexp.Atom "_" :: Sexp.Atom "hyper-res" :: _)
      :: Sexp.List (Sexp.Atom "asserted" :: _)
      :: tl)
    when List.last tl |> Option.exists ~f:(Sexp.equal (Sexp.Atom "Bug")) ->
      let a1 = List.hd_exn tl in
      let a2 = List.nth_exn tl 1 in
      Option.merge (find_errtrace_internal ans a1)
        (find_errtrace_internal ans a2) ~f:(fun a _ -> a)
  | _ -> L.error "find_errtrace: input's head must be bug"

let rec collect_facts_internal ans = function
  | Sexp.List
      [
        Sexp.List (Sexp.Atom "_" :: Sexp.Atom "hyper-res" :: _);
        Sexp.List (Sexp.Atom "asserted" :: _);
        fact;
      ] ->
      fact
  | Sexp.Atom a when String.is_prefix a ~prefix:"a!" ->
      let a_rule = find_a a ans |> Option.value_exn in
      collect_facts_internal ans a_rule
  | _ -> L.error "collect_facts_internal: wrong format"

let collect_facts ans = function
  | Sexp.List
      (Sexp.List (Sexp.Atom "_" :: Sexp.Atom "hyper-res" :: _)
      :: Sexp.List (Sexp.Atom "asserted" :: _)
      :: tl)
    when List.last tl
         |> Option.exists ~f:(function
              | Sexp.List (Sexp.Atom "ErrTrace" :: _) -> true
              | _ -> false) -> (
      match List.rev tl with
      | hd :: tl -> hd :: List.map ~f:(collect_facts_internal ans) tl
      | [] -> L.error "collect_facts: ???")
  | _ -> L.error "collect_facts: input's head must be ErrT"

let match_facts =
  List.fold2_exn ~init:PairSet.empty ~f:(fun pairs f1 f2 ->
      match (f1, f2) with
      | Sexp.List (Sexp.Atom hd1 :: args1), Sexp.List (Sexp.Atom hd2 :: args2)
        when String.equal hd1 hd2 ->
          List.fold2_exn args1 args2 ~init:pairs ~f:(fun pairs' a1 a2 ->
              match (a1, a2) with
              | Sexp.Atom s1, Sexp.Atom s2 ->
                  PairSet.add (int_of_string s1, int_of_string s2) pairs'
              | _ -> L.error "match_facts: wrong format")
      | _ -> L.error "match_facts: wrong format")

let dump_sol_map donor_name donor_maps donee_maps out_dir pairs =
  let oc =
    Out_channel.create (Filename.concat out_dir (donor_name ^ "_sol.map"))
  in
  let fmt = F.formatter_of_out_channel oc in
  PairSet.iter
    (fun (donor_n, donee_n) ->
      if 0 <= donor_n && donor_n <= 21 then
        F.fprintf fmt "%s\t%s\n"
          (Z3utils.binop_of_int donor_n)
          (Z3utils.binop_of_int donee_n)
      else if 22 <= donor_n && donor_n <= 24 then
        F.fprintf fmt "%s\t%s\n"
          (Z3utils.unop_of_int donor_n)
          (Z3utils.unop_of_int donee_n)
      else
        F.fprintf fmt "%s\t%s\n"
          (Hashtbl.find donor_maps.Maps.numeral_map donor_n)
          (Hashtbl.find donee_maps.Maps.numeral_map donee_n))
    pairs;
  F.pp_print_flush fmt ();
  Out_channel.close oc

let match_ans donee_maps out_dir db_dir donor_name =
  let donor_dir = Filename.concat db_dir donor_name in
  let donor_ans =
    Filename.concat donor_dir "donor_ans.smt2"
    |> In_channel.read_all |> Sexp.of_string
  in
  let donee_ans =
    Filename.concat out_dir "donee_ans.smt2"
    |> In_channel.read_all |> Sexp.of_string
  in
  let donor_facts =
    Option.(
      find_bug donor_ans >>= find_errtrace donor_ans >>| collect_facts donor_ans)
    |> Option.value_exn
  in
  let donee_facts =
    Option.(
      find_bug donee_ans >>= find_errtrace donee_ans >>| collect_facts donee_ans)
    |> Option.value_exn
  in
  let numeral_pairs = match_facts donor_facts donee_facts in
  let donor_maps = Maps.create_maps () in
  Maps.reset_maps donor_maps;
  let donor_numeral_map_ic =
    In_channel.create (Filename.concat donor_dir "donor_numeral.map")
  in
  Maps.load_numeral_map donor_numeral_map_ic donor_maps.Maps.numeral_map;
  dump_sol_map donor_name donor_maps donee_maps out_dir numeral_pairs

let run db_dir donee_dir out_dir =
  L.info "Finding bug pattern from DB...";
  let donee_maps = Maps.create_maps () in
  Maps.reset_maps donee_maps;
  let donee = Parser.make donee_dir in
  Chc.pretty_dump (Filename.concat out_dir "donee") donee;
  Chc.sexp_dump (Filename.concat out_dir "donee") donee;
  L.info "Make CHC done";
  let is_matched, matched_donors =
    fold_db (match_bug_for_one_prj out_dir donee donee_maps) db_dir
  in
  if not is_matched then (
    L.info ~to_console:true "There is no donor to donate patch TT";
    exit 1);
  List.iter
    ~f:(fun donor_name ->
      match_ans donee_maps out_dir db_dir donor_name;
      List.iter matched_donors ~f:(fun donor_cand ->
          let is_patched, patch = TF.transplant donor_cand donee_dir out_dir in
          if is_patched then (
            L.info ~to_console:true
              "Patch is successfully written at %s/applied.c\n" out_dir;
            TF.write_out out_dir patch;
            exit 0)))
    matched_donors
