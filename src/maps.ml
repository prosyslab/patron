open Core
module Hashtbl = Stdlib.Hashtbl
module J = Yojson.Basic.Util
module F = Format

module CfgNode = struct
  type loc = { file : string; line : int }

  type t =
    | CNone
    | CSet of string * string * loc (* (lv, e, loc) *)
    | CExternal of string * loc (*(lv, loc)*)
    | CAlloc of string * string * loc (*(lv, Array e, _, loc) *)
    | CSalloc of string * string * loc (*(lv, s, loc) *)
    | CFalloc of string * string * loc (*(lv, f, loc) *)
    | CCall of string * t * loc (*(Some lv, CcallExp(fexp, params, loc))*)
    | CCallExp of string * string list * loc (*(None, fexp, params, loc)*)
    | CReturn1 of string * loc (*(Some e, loc) *)
    | CReturn2 of loc (*(None, loc) *)
    | CIf of loc (*(_, _, _, loc) *)
    | CAssume of string * loc (*(e, _, loc) *)
    | CLoop of loc (*loc *)
    | CAsm of loc (*(_, _, _, _, _, loc) *)
    | CSkip of loc (*(_, loc)*)

  let parse_loc loc =
    let parsed = Str.split (Str.regexp ":") loc in
    if List.length parsed <> 2 then { file = ""; line = -1 }
    else
      {
        file = List.nth_exn parsed 0;
        line = int_of_string (List.nth_exn parsed 1);
      }

  let parse_sparrow nodes map fact_maps =
    (* let set_facts = parse_facts (Filename.concat path "Set.facts") in
       let call_facts = parse_call_facts (Filename.concat path "Set.facts") in *)
    (* let exp_map = parse_map (Filename.concat path "Exp.map") in *)
    let _, args_facts =
      List.find_exn ~f:(fun (k, _) -> String.equal k "Arg") fact_maps
    in
    let _, alloc_exp_facts =
      List.find_exn ~f:(fun (k, _) -> String.equal k "Alloc") fact_maps
    in
    let _, set_facts =
      List.find_exn ~f:(fun (k, _) -> String.equal k "Set") fact_maps
    in
    (* TODO: call_facts not proper *)
    let _, call_facts =
      List.find_exn ~f:(fun (k, _) -> String.equal k "Call") fact_maps
    in
    let _, return_facts =
      List.find_exn ~f:(fun (k, _) -> String.equal k "Return") fact_maps
    in
    let _, assume_facts =
      List.find_exn ~f:(fun (k, _) -> String.equal k "Assume") fact_maps
    in
    List.iter
      ~f:(fun (key, cmd, loc) ->
        let cmd =
          match List.hd_exn cmd with
          | "skip" -> CSkip (parse_loc loc)
          | "return" ->
              let arg_opt = Utils.StrMap.find_opt key return_facts in
              if Option.is_none arg_opt then CNone
              else
                let arg = Option.value ~default:[] arg_opt in
                if List.length arg <> 0 then
                  CReturn1 (List.hd_exn arg, parse_loc loc)
                else CReturn2 (parse_loc loc)
          | "call" ->
              let arg_opt = Utils.StrMap.find_opt key call_facts in
              if Option.is_none arg_opt then CNone
              else
                let arg = Option.value ~default:[] arg_opt in
                let call_exp = List.nth_exn arg 1 in
                let lval = List.nth_exn arg 0 in
                let arg_lst = Utils.StrMap.find_opt call_exp args_facts in
                let arg_lst =
                  if Option.is_none arg_lst then []
                  else Option.value ~default:[] arg_lst
                in
                CCall
                  ( List.hd_exn arg,
                    CCallExp (lval, arg_lst, parse_loc loc),
                    parse_loc loc )
          | "assume" ->
              let arg_opt = Utils.StrMap.find_opt key assume_facts in
              if Option.is_none arg_opt then CNone
              else
                let arg = Option.value ~default:[] arg_opt in
                CAssume (List.hd_exn arg, parse_loc loc)
          | "set" ->
              let arg = Utils.StrMap.find_opt key set_facts in
              if Option.is_none arg then CNone
              else
                let arg = Option.value ~default:[] arg in
                CSet (List.hd_exn arg, List.nth_exn arg 1, parse_loc loc)
          | "alloc" -> (
              let arg = Utils.StrMap.find_opt key alloc_exp_facts in
              match arg with
              | None -> CNone
              | Some arg ->
                  CAlloc (List.hd_exn arg, List.nth_exn arg 1, parse_loc loc))
          | "falloc" -> CNone
          | "salloc" -> CNone
          | _ ->
              print_endline "----------";
              print_endline (List.hd_exn cmd);
              print_endline "----------";
              failwith "Unknown Command"
        in
        match cmd with CNone | CSkip _ -> () | _ -> Hashtbl.add map cmd key)
      nodes
end

type t = {
  sym_map : (string, Z3.Expr.expr) Hashtbl.t;
  numeral_map : (int, string) Hashtbl.t;
  ast_map : (Cil.stmt, int) Hashtbl.t;
  cfg_map : (CfgNode.t, string) Hashtbl.t;
  exp_map : (string, string) Hashtbl.t;
}

let create_maps () =
  {
    sym_map = Hashtbl.create 1000;
    numeral_map = Hashtbl.create 1000;
    ast_map = Hashtbl.create 1000;
    cfg_map = Hashtbl.create 1000;
    exp_map = Hashtbl.create 1000;
  }

let load_map cast1 cast2 ic map =
  let rec loop () =
    let line = In_channel.input_line ic in
    if Option.is_some line then (
      let pair = Option.value_exn line |> String.split ~on:'\t' in
      Hashtbl.add map
        (List.nth_exn pair 0 |> cast1)
        (List.nth_exn pair 1 |> cast2);
      loop ())
  in
  loop ();
  In_channel.close ic

let load_numeral_map = load_map int_of_string Fun.id

let reset_maps maps =
  Hashtbl.reset maps.sym_map;
  Hashtbl.reset maps.numeral_map;
  Hashtbl.reset maps.ast_map;
  Hashtbl.reset maps.cfg_map

let make_ast_map stmts ast_map =
  List.fold_left ~init:1
    ~f:(fun id stmt ->
      let next_id = id + 1 in
      Hashtbl.add ast_map stmt id;
      next_id)
    stmts
  |> ignore

let dump_map a_to_string b_to_string map_name mode map out_dir =
  let sym_map_file =
    F.sprintf "%s_%s.map" mode map_name |> Filename.concat out_dir
  in
  let sym_map_oc = Out_channel.create sym_map_file in
  let sym_map_fmt = F.formatter_of_out_channel sym_map_oc in
  Hashtbl.iter
    (fun a b ->
      F.fprintf sym_map_fmt "%s\t%s\n" (a_to_string a) (b_to_string b))
    map;
  F.pp_print_flush sym_map_fmt ();
  Out_channel.close sym_map_oc

let dump_sym_map = dump_map Fun.id Z3.Expr.to_string "sym"
let dump_numeral_map = dump_map string_of_int Fun.id "numeral"

let dump_ast_map =
  dump_map
    (fun x -> Utils.string_of_stmt x |> Utils.summarize_pp)
    string_of_int "ast"

let dump mode maps out_dir =
  dump_sym_map mode maps.sym_map out_dir;
  dump_numeral_map mode maps.numeral_map out_dir
(* dump_ast_map mode maps.ast_map out_dir *)
