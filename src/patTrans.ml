open Core
open Z3utils
module L = Logger
module Sys = Stdlib.Sys

let iter_db f db_dir =
  let prjs = Sys.readdir db_dir in
  Array.iter
    ~f:(fun p ->
      let p_path = Filename.concat db_dir p in
      f p_path)
    prjs

(* let match_bug ver_name solver pattern out_dir =
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
   else L.info "%s not Matched" ver_name *)

let run db_dir donee_dir out_dir =
  L.info "Finding bug pattern from DB...";
  let donee_maps = Maps.create_maps () in
  Maps.reset_maps donee_maps;
  Maps.reset_globals ()
(* Facts.make ~maps:donee_maps z3env.donee_solver donee_dir *)
(* iter_db match_bug db_dir *)
