open Yojson
open TransformerHelper
module F = Format
module L = Logger
module C = Cmdline
module J = Yojson.Basic
open J.Util
module StrMap = Map.Make (String)

class expUpdateVisitor (from_exp : Cil.exp) (to_exp : Cil.exp) =
  object
    inherit Cil.nopCilVisitor

    method! vexpr (e : Cil.exp) =
      if e = from_exp then ChangeTo to_exp else DoChildren
  end

class expInsertVisitor (context : syntatic_context) (from_exp : Cil.exp)
  (to_exp : Cil.exp) =
  object
    inherit Cil.nopCilVisitor

    method! vinst (i : Cil.instr) =
      if eq_call context i then
        match i with
        | Cil.Call (lval, exp, exp_list, loc) ->
            if List.exists (fun x -> x = from_exp) exp_list then
              let insert_loc = List.find (fun x -> x = from_exp) exp_list in
              ChangeTo
                [
                  Cil.Call
                    ( lval,
                      exp,
                      append_before_elt to_exp insert_loc exp_list,
                      loc );
                ]
            else DoChildren
        | _ -> DoChildren
      else DoChildren
  end

let map_sub_priority_2 exp_map exp =
  StrMap.fold
    (fun key value acc ->
      let trimed_exp =
        Str.global_replace (Str.regexp " ") "" (string_of_exp exp)
      in
      if
        subset (Str.global_replace (Str.regexp "@") "" value) trimed_exp
        && String.length trimed_exp > String.length value / 2
      then StrMap.add key exp acc
      else acc)
    exp_map StrMap.empty

let map_sub_priority_1 exp_map exp =
  StrMap.fold
    (fun key value acc ->
      let trimed_exp =
        Str.global_replace (Str.regexp " ") "" (string_of_exp exp)
      in
      if trimed_exp = Str.global_replace (Str.regexp "@") "" value then
        StrMap.add key exp acc
      else acc)
    exp_map StrMap.empty

let map_sub exp_map exp =
  let first = map_sub_priority_1 exp_map exp in
  if StrMap.cardinal first = 0 then map_sub_priority_2 exp_map exp else first

let map_set_instr exp_map set lval exp loc node =
  match node with
  | Node (n_id, cmd, nloc) ->
      if loc = nloc then
        match cmd with
        | Salloc (to_, from_)
        | Set (to_, from_)
        | Alloc (to_, from_)
        | Falloc (to_, from_) ->
            if
              subset (string_of_lval lval) to_
              || subset (string_of_exp exp) from_
            then
              [
                { id = n_id; elem = EInstr set; subelem = map_sub exp_map exp };
              ]
            else []
        | _ -> []
      else []
  | _ -> []

let replace_tmp str lookup_table =
  if subset str "__cil_tmp" then
    try StrMap.find str lookup_table with Not_found -> str
  else str

let rec check_args lookup_table args exp_list =
  match (args, exp_list) with
  | [], [] -> true
  | hd1 :: tl1, hd2 :: tl2 ->
      if
        subset (string_of_exp hd2) (replace_tmp hd1 lookup_table)
        || subset (replace_tmp hd1 lookup_table) (string_of_exp hd2)
      then check_args lookup_table tl1 tl2
      else false
  | _ -> false

let map_call_instr lookup_table exp_map call lval exp exp_list loc node =
  match node with
  | Node (n_id, cmd, nloc) ->
      if loc = nloc then
        match cmd with
        | Call (lv, funName, args) ->
            if String.length lv <> 0 || Option.is_some lval then
              if subset (string_of_lval (Option.get lval)) lv then
                if
                  subset
                    (Str.global_replace (Str.regexp "@") "" funName)
                    (string_of_exp exp)
                then
                  if check_args lookup_table args exp_list then
                    [
                      {
                        id = n_id;
                        elem = EInstr call;
                        subelem =
                          StrMap.union
                            (fun _ v1 _ -> Some v1)
                            (map_sub exp_map exp)
                            (List.fold_left
                               (fun acc x ->
                                 StrMap.union
                                   (fun _ v1 _ -> Some v1)
                                   (map_sub exp_map x) acc)
                               StrMap.empty exp_list);
                      };
                    ]
                  else []
                else []
              else []
            else if
              subset
                (Str.global_replace (Str.regexp "@") "" funName)
                (string_of_exp exp)
            then
              if check_args lookup_table args exp_list then
                [
                  {
                    id = n_id;
                    elem = EInstr call;
                    subelem =
                      StrMap.union
                        (fun _ v1 _ -> Some v1)
                        (map_sub exp_map exp)
                        (List.fold_left
                           (fun acc x ->
                             StrMap.union
                               (fun _ v1 _ -> Some v1)
                               (map_sub exp_map x) acc)
                           StrMap.empty exp_list);
                  };
                ]
              else []
            else []
        | _ -> []
      else []
  | _ -> []

let map_instr lookup_table exp_map node instr =
  match instr with
  | Cil.Set (lval, exp, loc) ->
      map_set_instr exp_map instr lval exp loc.line node
  | Cil.Call (lval, exp, exp_list, loc) ->
      map_call_instr lookup_table exp_map instr lval exp exp_list loc.line node
  | _ -> []

let fold_instrs lookup_table exp_map node instrs =
  List.fold_left
    (fun acc x -> acc @ map_instr lookup_table exp_map node x)
    [] instrs

let map_cond exp_map node stmt loc cond =
  match node with
  | Node (n_id, cmd, nloc) ->
      if loc = nloc then
        match cmd with
        | Assume (_, exp) ->
            if
              subset (string_of_exp cond)
                (Str.global_replace (Str.regexp ")") ""
                   (Str.global_replace (Str.regexp "(") "" exp))
            then
              [
                { id = n_id; elem = EStmt stmt; subelem = map_sub exp_map cond };
              ]
            else []
        | _ -> []
      else []
  | _ -> []

let rec fold_stmts lookup_table exp_map node stmts =
  List.fold_left
    (fun acc x -> acc @ map_skind lookup_table exp_map node x)
    [] stmts

and map_skind lookup_table exp_map node stmt =
  match stmt.Cil.skind with
  | Cil.Instr instrs -> fold_instrs lookup_table exp_map node instrs
  | Cil.If (cond, then_block, else_block, loc) ->
      map_cond exp_map node stmt loc.line cond
      @ fold_stmts lookup_table exp_map node then_block.bstmts
      @ fold_stmts lookup_table exp_map node else_block.bstmts
  | _ -> []

let map_global lookup_table exp_map node global =
  match global with
  | Cil.GFun (func_info, _) ->
      fold_stmts lookup_table exp_map node func_info.sbody.bstmts
  | _ -> []

let fold_globals lookup_table (exp_map : string StrMap.t) (node : sparrow_node)
    (globals : Cil.global list) =
  List.fold_left
    (fun acc glob -> acc @ map_global lookup_table exp_map node glob)
    [] globals

let map_cil_node exp_map node_list file =
  let lookup_table = create_temp_map node_list StrMap.empty in
  let new_exp_map =
    StrMap.map
      (fun x -> try StrMap.find x lookup_table with Not_found -> x)
      exp_map
  in
  let map_result =
    List.fold_left
      (fun acc x ->
        acc @ fold_globals lookup_table new_exp_map x file.Cil.globals)
      [] node_list
  in
  let unmapped =
    List.filter
      (fun x ->
        match x with
        | Node (id, _, _) ->
            if List.exists (fun y -> y.id = id) map_result then false else true
        | _ -> false)
      node_list
  in
  map_result
  @ List.fold_left
      (fun acc x ->
        match x with
        | Node (id, _, _) ->
            acc @ [ { id; elem = Empty; subelem = StrMap.empty } ]
        | _ -> acc)
      [] unmapped

let parse_cfg_edge json_path =
  let json = Yojson.Basic.from_file json_path in
  let open Yojson.Basic.Util in
  let cfg = json |> member "cfgs" in
  let main = cfg |> member "main" in
  let edges = main |> member "edges" |> to_list in
  List.fold_left
    (fun acc x ->
      let src = "main-" ^ (List.nth (to_list x) 0 |> to_string) in
      let dst = "main-" ^ (List.nth (to_list x) 1 |> to_string) in
      let edge = (src, dst) in
      acc @ [ edge ])
    [] edges

let parse_dug_edge json_path =
  let json = Yojson.Basic.from_file json_path in
  let open Yojson.Basic.Util in
  let dugraph = json |> member "dugraph" in
  let edges = dugraph |> member "edges" |> to_list in
  List.fold_left
    (fun acc x ->
      let src = List.nth (to_list x) 0 |> to_string in
      let dst = List.nth (to_list x) 1 |> to_string in
      let edge = (src, dst) in
      acc @ [ edge ])
    [] edges

let make_graph file sparrow_path exp_path =
  let exp_map = parse_strmap (read_lines exp_path) StrMap.empty in
  let sparrow_node_lst = parse_node (sparrow_path ^ "/node.json") in
  let nodes = map_cil_node exp_map sparrow_node_lst file in
  let cfg_edges = parse_cfg_edge (sparrow_path ^ "/dug.json") in
  let dug_edges = parse_dug_edge (sparrow_path ^ "/dug.json") in
  { nodes; cfg_edges; dug_edges }

let find_match_node_by_id id graph = List.find (fun x -> x.id = id) graph.nodes

let find_match_node_by_instr instr graph =
  List.find
    (fun x -> match x.elem with EInstr i -> i = instr | _ -> false)
    graph.nodes

let rec find_cfg_node context donor_graph sol =
  match context with
  | ExpContext (_, ctxt) -> (
      match ctxt with
      | InstrContext (i, _) -> find_match_node_by_instr i donor_graph
      | _ -> find_cfg_node ctxt donor_graph sol)
  | _ -> failwith "translation failed"

let match_exception exp donor_node =
  match exp with
  | Cil.SizeOfE e -> (
      let scnd_try =
        try
          List.find
            (fun x -> match x with _, v -> string_of_exp v = string_of_exp e)
            (StrMap.bindings donor_node.subelem)
        with Not_found -> ("None", exp)
      in
      match scnd_try with "None", v -> ("None", v) | k, _ -> (k, Cil.SizeOfE e))
  | Cil.CastE (typ, e) -> (
      let scnd_try =
        try
          List.find
            (fun x -> match x with _, v -> string_of_exp v = string_of_exp e)
            (StrMap.bindings donor_node.subelem)
        with Not_found -> ("None", exp)
      in
      match scnd_try with
      | "None", v -> ("None", v)
      | k, _ -> (k, Cil.CastE (typ, e)))
  | _ -> ("None", exp)

let match_exp exp donor_node donee_node sol =
  let match_tup =
    try
      List.find
        (fun x -> match x with _, v -> string_of_exp v = string_of_exp exp)
        (StrMap.bindings donor_node.subelem)
    with Not_found -> match_exception exp donor_node
  in
  match match_tup with
  | k, v -> (
      let matched_id = try StrMap.find k sol with Not_found -> "None" in
      match matched_id with
      | "None" -> []
      | _ -> (
          let matched_value =
            try StrMap.find matched_id donee_node.subelem
            with Not_found -> failwith "translation failed"
          in
          match v with
          | Cil.SizeOfE _ -> [ Cil.SizeOfE matched_value ]
          | Cil.CastE (typ, _) -> [ Cil.CastE (typ, matched_value) ]
          | _ -> [ matched_value ]))

let extract_action action donor_graph donee_graph sol =
  match action with
  | UpdateExp (context, from_, to_) ->
      let donor_node = find_cfg_node context donor_graph sol in
      let donee_node =
        find_match_node_by_id (StrMap.find donor_node.id sol) donee_graph
      in
      let matched_exp_from = match_exp from_ donor_node donee_node sol in
      let matched_exp_to = match_exp to_ donor_node donee_node sol in
      let matched_exp_from = List.hd matched_exp_from in
      let matched_exp_to =
        if List.length matched_exp_to = 0 then to_ else List.hd matched_exp_to
      in
      [
        UpdateExp (NodeLevelContext donee_node, matched_exp_from, matched_exp_to);
      ]
  | InsertExp (context, from_, to_) ->
      let donor_node = find_cfg_node context donor_graph sol in
      let donee_node =
        find_match_node_by_id (StrMap.find donor_node.id sol) donee_graph
      in
      let matched_exp_from = match_exp from_ donor_node donee_node sol in
      let matched_exp_to = match_exp to_ donor_node donee_node sol in
      let matched_exp_from = List.hd matched_exp_from in
      let matched_exp_to =
        if List.length matched_exp_to = 0 then to_ else List.hd matched_exp_to
      in
      [
        InsertExp (NodeLevelContext donee_node, matched_exp_from, matched_exp_to);
      ]
  | _ -> []

let translate edit_script donor_graph donee_graph sol =
  List.fold_left
    (fun acc x -> acc @ extract_action x donor_graph donee_graph sol)
    [] edit_script

let apply_action file action =
  match action with
  | UpdateExp (_, from_, to_) ->
      let vis = new expUpdateVisitor from_ to_ in
      ignore (Cil.visitCilFile vis file)
  | InsertExp (context, from_, to_) ->
      let vis = new expInsertVisitor context from_ to_ in
      ignore (Cil.visitCilFile vis file)
  | _ -> ()

let apply_es edit_script file =
  List.iter (fun x -> apply_action file x) edit_script

let apply edit_script file =
  apply_es edit_script file;
  let out_file = !Cmdline.out_dir ^ "/applied.c" in
  let out_chan = open_out out_file in
  Cil.dumpFile Cil.defaultCilPrinter out_chan "" file;
  close_out out_chan

let init () =
  Cil.initCIL ();
  Cil.insertImplicitCasts := false;
  (try Unix.mkdir !Cmdline.out_dir 0o775
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());
  print_endline ("Logging to " ^ !Cmdline.out_dir);
  Filename.concat !Cmdline.out_dir "transformer.log.txt" |> Logger.from_file;
  Logger.set_level !Cmdline.log_level

let main () =
  init ();
  let donor, patch, donee =
    match Array.to_list Sys.argv |> List.tl with
    | [ a; b; c; _; _; _ ] ->
        (Frontc.parse a (), Frontc.parse b (), Frontc.parse c ())
    | _ ->
        failwith
          "Argument mismatch: must be <Donor> <Patch> <Donee> <Donor Sparrow \
           Dir> <Patch Sparrow Dir> <test_input dir>"
  in
  let donor_graph =
    make_graph donor Sys.argv.(4) (Sys.argv.(6) ^ "/sparrow_exp_donor.txt")
  in
  let donee_graph =
    make_graph donee Sys.argv.(5) (Sys.argv.(6) ^ "/sparrow_exp_donee.txt")
  in
  let edit_script = extract donor patch in
  Logger.info "#edit script: %d\n%a\n" (List.length edit_script) pp_edit_script
    edit_script;
  let sol = make_str_map (Sys.argv.(6) ^ "/sol.map") in
  let translated_es = translate edit_script donor_graph donee_graph sol in
  Logger.info "#translated edit script: %d\n%a\n" (List.length edit_script)
    pp_edit_script translated_es;
  apply translated_es donee

let _ =
  Printexc.record_backtrace true;
  main ()
