open Core
open Z3utils
module L = Logger
module Hashtbl = Stdlib.Hashtbl

let fold_db f db_dir =
  Sys_unix.fold_dir ~init:(false, "")
    ~f:(fun (matched, donor) cand ->
      if matched then (matched, donor)
      else (
        L.debug "Try matching with %s..." cand;
        let cand_path = Filename.concat db_dir cand in
        if f cand_path then (true, cand) else (matched, donor)))
    db_dir

let match_bug out_dir donee donee_maps donor_cand_path =
  let pattern =
    Parser.parse_chc (Filename.concat donor_cand_path "pattern_mach.chc")
    |> Chc.map Chc.numer2var
  in
  let status = Chc.pattern_match donee_maps donee pattern [ z3env.bug ] in
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

let rec find_errnode_internal ans = function
  | Sexp.List
      (Sexp.List (Sexp.Atom "_" :: Sexp.Atom "hyper-res" :: _)
      :: Sexp.List (Sexp.Atom "asserted" :: _)
      :: tl) as s
    when List.last tl
         |> Option.exists ~f:(function
              | Sexp.List (Sexp.Atom "ErrNode" :: _) -> true
              | _ -> false) ->
      Some s
  | Sexp.Atom a when String.is_prefix a ~prefix:"a!" ->
      let a_rule = find_a a ans |> Option.value_exn in
      find_errnode_internal ans a_rule
  | _ -> None

let find_errnode ans = function
  | Sexp.List
      (Sexp.List (Sexp.Atom "_" :: Sexp.Atom "hyper-res" :: _)
      :: Sexp.List (Sexp.Atom "asserted" :: _)
      :: tl)
    when List.last tl |> Option.exists ~f:(Sexp.equal (Sexp.Atom "Bug")) ->
      let a1 = List.hd_exn tl in
      let a2 = List.nth_exn tl 1 in
      Option.merge (find_errnode_internal ans a1) (find_errnode_internal ans a2)
        ~f:(fun a _ -> a)
  | _ -> L.error "find_errnode: input's head must be bug"

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
              | Sexp.List (Sexp.Atom "ErrNode" :: _) -> true
              | _ -> false) -> (
      match List.rev tl with
      | hd :: tl -> hd :: List.map ~f:(collect_facts_internal ans) tl
      | [] -> L.error "collect_facts: ???")
  | _ -> L.error "collect_facts: input's head must be ErrNode"

let match_facts =
  List.fold2_exn ~init:[] ~f:(fun pairs f1 f2 ->
      match (f1, f2) with
      | Sexp.List (Sexp.Atom hd1 :: args1), Sexp.List (Sexp.Atom hd2 :: args2)
        when String.equal hd1 hd2 ->
          List.map2_exn args1 args2 ~f:(fun a1 a2 ->
              match (a1, a2) with
              | Sexp.Atom s1, Sexp.Atom s2 ->
                  (int_of_string s1, int_of_string s2)
              | _ -> L.error "match_facts: wrong format")
          |> List.rev_append pairs
      | _ -> L.error "match_facts: wrong format")

let dump_sol_map donor_maps donee_maps out_dir =
  let oc = Out_channel.create (Filename.concat out_dir "sol.map") in
  let fmt = F.formatter_of_out_channel oc in
  List.iter ~f:(fun (donor_n, donee_n) ->
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

let match_ans donee_maps out_dir donor_dir =
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
      find_bug donor_ans >>= find_errnode donor_ans >>| collect_facts donor_ans)
    |> Option.value_exn
  in
  let donee_facts =
    Option.(
      find_bug donee_ans >>= find_errnode donee_ans >>| collect_facts donee_ans)
    |> Option.value_exn
  in
  let numeral_pairs = match_facts donor_facts donee_facts in
  let donor_maps = Maps.create_maps () in
  Maps.reset_maps donor_maps;
  let donor_numeral_map_ic =
    In_channel.create (Filename.concat donor_dir "donor_numeral.map")
  in
  Maps.load_numeral_map donor_numeral_map_ic donor_maps.Maps.numeral_map;
  dump_sol_map donor_maps donee_maps out_dir numeral_pairs

let run db_dir donee_dir out_dir =
  L.info "Finding bug pattern from DB...";
  let donee_maps = Maps.create_maps () in
  Maps.reset_maps donee_maps;
  let donee = Parser.make donee_dir in
  Chc.pretty_dump (Filename.concat out_dir "donee") donee;
  Chc.sexp_dump (Filename.concat out_dir "donee") donee;
  L.info "Make CHC done";
  let _, donor_dir = fold_db (match_bug out_dir donee donee_maps) db_dir in
  let donor_dir = Filename.concat db_dir donor_dir in
  match_ans donee_maps out_dir donor_dir
