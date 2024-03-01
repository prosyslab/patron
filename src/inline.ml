open Cil
module E = Errormsg
module H = Hashtbl
module IH = Inthash
module A = Alpha
module L = Logger

let ( >>> ) f g x = g (f x)
let flip f y x = f x y
let list_fold f list init = List.fold_left (flip f) init list
let id x = x

let get_loc_filename loc =
  try
    let idx = String.rindex loc.file '/' in
    let len = String.length loc.file in
    String.sub loc.file (idx + 1) (len - idx - 1)
  with _ -> loc.file

let s_location loc = get_loc_filename loc ^ ":" ^ string_of_int loc.line

module AbsDom = struct
  module type SET = sig
    type t

    val to_string : t -> string
    val compare : t -> t -> int
    val pp : Format.formatter -> t -> unit
  end

  module type HASHABLE_SET = sig
    include SET

    val equal : t -> t -> bool
    val hash : t -> int
  end

  (** Signature of CPO *)
  module type CPO = sig
    include SET

    val le : t -> t -> bool
    val eq : t -> t -> bool
    val bot : t
    val join : t -> t -> t
    val meet : t -> t -> t
    val widen : t -> t -> t
    val narrow : t -> t -> t
  end

  (** Signature of lattice *)
  module type LAT = sig
    include CPO

    val top : t
  end
end

open AbsDom

module IntraCfg = struct
  module Node = struct
    type t = ENTRY | EXIT | Node of int

    let compare = compare

    let equal n1 n2 =
      match (n1, n2) with
      | ENTRY, ENTRY -> true
      | EXIT, EXIT -> true
      | Node i1, Node i2 -> i1 = i2
      | _, _ -> false

    let hash = Hashtbl.hash
    let entry = ENTRY
    let exit = EXIT
    let nid = ref 0

    let fromCilStmt s =
      if !nid < s.sid then nid := s.sid;
      Node s.sid

    let make () =
      nid := !nid + 1;
      Node !nid

    let id = function ENTRY | EXIT -> -1 | Node id -> id
  end

  module NodeSet = BatSet.Make (Node)

  module Cmd = struct
    type t =
      | Cinstr of instr list * location
      | Cif of exp * block * block * location
      | CLoop of location
      | Cset of lval * exp * location
      | Cexternal of lval * location
      | Calloc of lval * alloc * local * static * location
      | Csalloc of lval * string * location
      | Cfalloc of lval * fundec * location
      | Cassume of exp * branch * location
      | Ccall of lval option * exp * exp list * location
      | Creturn of exp option * location
      | Casm of
          attributes
          * string list
          * (string option * string * lval) list
          * (string option * string * exp) list
          * string list
          * location
      | Cskip of tag * location

    and alloc = Array of exp | Struct of compinfo
    and local = bool
    and static = bool
    and branch = bool
    and tag = Unknown | ReturnNode | Branch | LoopHead

    let fromCilStmt = function
      | Instr instrs as s -> Cinstr (instrs, Cil.get_stmtLoc s)
      | If (exp, b1, b2, loc) -> Cif (exp, b1, b2, loc)
      | Loop (_, loc, _, _) -> CLoop loc
      | Return (expo, loc) -> Creturn (expo, loc)
      | s -> Cskip (Unknown, Cil.get_stmtLoc s)

    let location_of = function
      | Cinstr (_, l)
      | Cif (_, _, _, l)
      | CLoop l
      | Cset (_, _, l)
      | Cexternal (_, l)
      | Calloc (_, _, _, _, l)
      | Csalloc (_, _, l)
      | Cfalloc (_, _, l)
      | Ccall (_, _, _, l)
      | Creturn (_, l) ->
          l
      | Cassume (_, _, l) -> l
      | Cskip (_, l) -> l
      | _ -> Cil.locUnknown
  end

  type node = Node.t
  type cmd = Cmd.t

  module G = Graph.Persistent.Digraph.ConcreteBidirectional (Node)
  module Oper = Graph.Oper.P (G)
  module Merge = Graph.Merge.P (G)
  module Scc = Graph.Components.Make (G)

  module GDom = struct
    module V = Node

    type t = G.t

    let empty () = G.empty
    let fromG g = g
    let pred = G.pred
    let succ = G.succ
    let fold_vertex = G.fold_vertex
    let iter_vertex = G.iter_vertex
    let iter_succ = G.iter_succ
    let nb_vertex = G.nb_vertex
    let add_edge g _ _ = g
  end

  module Dom = Graph.Dominator.Make_graph (GDom)

  type t = {
    fd : Cil.fundec;
    graph : G.t;
    cmd_map : (node, cmd) BatMap.t;
    dom_fronts : dom_fronts;
    dom_tree : dom_tree;
    post_dom_fronts : dom_fronts;
    scc_list : node list list;
  }

  and dom_fronts = (Node.t, NodeSet.t) BatMap.t
  and dom_tree = G.t

  let empty fd =
    {
      fd;
      graph = G.empty;
      cmd_map = BatMap.empty;
      dom_fronts = BatMap.empty;
      post_dom_fronts = BatMap.empty;
      dom_tree = G.empty;
      scc_list = [];
    }

  let nodesof g = G.fold_vertex (fun x l -> x :: l) g.graph []
  let add_edge n1 n2 g = { g with graph = G.add_edge g.graph n1 n2 }
  let add_node n g = { g with graph = G.add_vertex g.graph n }

  let find_cmd n g =
    try BatMap.find n g.cmd_map
    with _ ->
      if n = Node.ENTRY || n = Node.EXIT then
        Cmd.Cskip (Cmd.Unknown, Cil.locUnknown)
      else Cmd.Cskip (Cmd.Unknown, Cil.locUnknown)

  let add_cmd n c g = { g with cmd_map = BatMap.add n c g.cmd_map }
  let add_node_with_cmd n c g = g |> add_node n |> add_cmd n c
  let remove_edge n1 n2 g = { g with graph = G.remove_edge g.graph n1 n2 }

  let remove_node n g =
    {
      g with
      graph = G.remove_vertex g.graph n;
      cmd_map = BatMap.remove n g.cmd_map;
      dom_fronts = BatMap.remove n g.dom_fronts;
      dom_tree = G.remove_vertex g.dom_tree n;
    }

  let add_new_node n cmd s g =
    let new_node = Node.make () in
    (add_cmd new_node cmd >>> remove_edge n s >>> add_edge n new_node
   >>> add_edge new_node s)
      g

  let pred n g = G.pred g.graph n
  let succ n g = G.succ g.graph n
  let fold_node f g a = G.fold_vertex f g.graph a

  let is_callnode n g =
    match find_cmd n g with Cmd.Ccall _ -> true | _ -> false

  let returnof n g =
    if is_callnode n g then (
      assert (List.length (succ n g) = 1);
      List.hd (succ n g))
    else L.error "IntraCfg.returnof - given node is not a call-node"

  let generate_assumes g =
    try
      fold_node
        (fun n g ->
          match find_cmd n g with
          | Cmd.Cif (e, tb, fb, loc) ->
              let succs = succ n g in
              let _ = assert (List.length succs = 1 || List.length succs = 2) in
              if List.length succs = 2 then
                let s1, s2 = (List.nth succs 0, List.nth succs 1) in
                let tbn, fbn =
                  match (tb.bstmts, fb.bstmts) with
                  | [], [] -> (s1, s2)
                  | t :: _, _ ->
                      if t.sid = Node.id s1 then (s1, s2) else (s2, s1)
                  | _, t :: _ ->
                      if t.sid = Node.id s2 then (s1, s2) else (s2, s1)
                in
                let tassert = Cmd.Cassume (e, true, loc) in
                let not_e = UnOp (LNot, e, Cil.typeOf e) in
                let fassert = Cmd.Cassume (not_e, false, loc) in
                (add_new_node n fassert fbn >>> add_new_node n tassert tbn) g
              else
                let tbn = List.nth succs 0 in
                let tassert = Cmd.Cassume (e, true, loc) in
                add_new_node n tassert tbn g
          | _ -> g)
        g g
    with _ -> assert false

  let remove_if_loop g =
    fold_node
      (fun n g ->
        match find_cmd n g with
        | Cmd.Cif (_, _, _, l) -> add_cmd n (Cmd.Cskip (Cmd.Branch, l)) g
        | Cmd.CLoop l -> add_cmd n (Cmd.Cskip (Cmd.LoopHead, l)) g
        | _ -> g)
      g g

  let remove_empty_nodes g =
    fold_node
      (fun n g ->
        match find_cmd n g with
        | Cmd.Cskip _
          when List.length (succ n g) = 1 && List.length (pred n g) = 1 ->
            let p = List.nth (pred n g) 0 in
            let s = List.nth (succ n g) 0 in
            g |> remove_node n |> add_edge p s
        | _ -> g)
      g g

  let flatten_instructions g =
    fold_node
      (fun n g ->
        match find_cmd n g with
        | Cmd.Cinstr (instrs, _) when instrs <> [] ->
            let cmds =
              List.map
                (fun i ->
                  match i with
                  | Set (lv, e, loc) -> Cmd.Cset (lv, e, loc)
                  | Call (lvo, f, args, loc) -> Cmd.Ccall (lvo, f, args, loc)
                  | Asm (a, b, c, d, e, f) -> Cmd.Casm (a, b, c, d, e, f))
                instrs
            in
            let pairs = List.map (fun c -> (Node.make (), c)) cmds in
            let first, _ = List.nth pairs 0 in
            let last, _ = List.nth pairs (List.length pairs - 1) in
            let preds, succs = (pred n g, succ n g) in
            g
            |> (fun g ->
                 List.fold_left
                   (fun g (n, c) -> add_node_with_cmd n c g)
                   g pairs)
            |> (fun g ->
                 fst
                   (List.fold_left
                      (fun (g, p) (n, _) -> (add_edge p n g, n))
                      (g, n) pairs))
            |> list_fold (fun p -> add_edge p first) preds
            |> list_fold (fun s -> add_edge last s) succs
            |> remove_node n
        | Cmd.Cinstr ([], loc) ->
            if Cil.compareLoc loc Cil.locUnknown = 0 then
              let pred_locs =
                pred n g
                |> List.map (fun n -> find_cmd n g |> Cmd.location_of)
                |> List.filter (fun loc ->
                       Cil.compareLoc loc Cil.locUnknown <> 0)
              in
              if pred_locs = [] then
                add_cmd n (Cmd.Cskip (Cmd.Unknown, Cil.locUnknown)) g
              else add_cmd n (Cmd.Cskip (Cmd.Unknown, List.nth pred_locs 0)) g
            else add_cmd n (Cmd.Cskip (Cmd.Unknown, loc)) g
        | _ -> g)
      g g

  let make_array lv typ exp local loc entry g =
    let alloc_node = Node.make () in
    let size = Cil.BinOp (Cil.Mult, Cil.SizeOf typ, exp, Cil.intType) in
    let alloc_cmd = Cmd.Calloc (lv, Cmd.Array size, local, true, loc) in
    (alloc_node, g |> add_cmd alloc_node alloc_cmd |> add_edge entry alloc_node)

  let make_struct lv comp local loc entry g =
    let alloc_node = Node.make () in
    let alloc_cmd = Cmd.Calloc (lv, Cmd.Struct comp, local, true, loc) in
    (alloc_node, g |> add_cmd alloc_node alloc_cmd |> add_edge entry alloc_node)

  let make_init_loop fd lv exp loc entry f g =
    let init_node = Node.make () in
    let idxinfo = Cil.makeTempVar fd (Cil.TInt (IInt, [])) in
    let idx = (Cil.Var idxinfo, Cil.NoOffset) in
    let init_value = Cil.Const (Cil.CInt64 (Int64.zero, IInt, None)) in
    let init_cmd = Cmd.Cset (idx, init_value, loc) in
    let g = add_cmd init_node init_cmd g in
    let skip_node = Node.make () in
    let g = add_cmd skip_node (Cmd.Cskip (Cmd.LoopHead, loc)) g in
    let g = add_edge init_node skip_node g in
    let g = add_edge entry init_node g in
    let assume_node = Node.make () in
    let cond = Cil.BinOp (Cil.Lt, Cil.Lval idx, exp, Cil.intType) in
    let assume_cmd = Cmd.Cassume (cond, true, loc) in
    let g = add_cmd assume_node assume_cmd g in
    let g = add_edge skip_node assume_node g in
    let nassume_node = Node.make () in
    let nassume_cmd =
      Cmd.Cassume (Cil.UnOp (Cil.LNot, cond, Cil.intType), false, loc)
    in
    let g = add_cmd nassume_node nassume_cmd g in
    let g = add_edge skip_node nassume_node g in
    let element =
      Cil.addOffsetLval (Index (Lval (Var idxinfo, NoOffset), NoOffset)) lv
    in
    let term, g = f assume_node element g in
    let incr_node = Node.make () in
    let incr_cmd =
      Cmd.Cset
        ( idx,
          Cil.BinOp
            ( Cil.PlusA,
              Cil.Lval idx,
              Cil.Const (Cil.CInt64 (Int64.one, IInt, None)),
              Cil.intType ),
          loc )
    in
    let g = add_cmd incr_node incr_cmd g in
    let g = add_edge term incr_node g in
    let g = add_edge incr_node skip_node g in
    (nassume_node, g)

  let rec make_nested_array fd lv typ exp local loc entry initialize g =
    let typ = unrollTypeDeep typ in
    match typ with
    | TArray (t, Some size, _) ->
        let f assume_node element g =
          let tmp =
            ( Cil.Var (Cil.makeTempVar fd (Cil.TPtr (Cil.TVoid [], []))),
              Cil.NoOffset )
          in
          let term, g = make_array tmp t size local loc assume_node g in
          let cast_node = Node.make () in
          let cast_cmd =
            Cmd.Cset (element, Cil.CastE (TPtr (t, []), Cil.Lval tmp), loc)
          in
          let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
          make_nested_array fd element t size local loc cast_node initialize g
        in
        make_init_loop fd lv exp loc entry f g
    | TComp (comp, _) ->
        let f assume_node element g =
          let term, g = make_struct element comp local loc assume_node g in
          generate_allocs_field comp.cfields element local fd term g
        in
        make_init_loop fd lv exp loc entry f g
    | _ when initialize ->
        let f assume_node element g =
          let init_node = Node.make () in
          let init_cmd = Cmd.Cset (element, Cil.zero, loc) in
          ( init_node,
            g |> add_cmd init_node init_cmd |> add_edge assume_node init_node )
        in
        make_init_loop fd lv exp loc entry f g
    | _ -> (entry, g)

  and generate_allocs_field fl lv local fd entry g =
    match fl with
    | [] -> (entry, g)
    | fieldinfo :: t -> (
        match Cil.unrollTypeDeep fieldinfo.ftype with
        | TArray (typ, Some exp, _) ->
            let field =
              addOffsetLval (Cil.Field (fieldinfo, Cil.NoOffset)) lv
            in
            let tmp =
              (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset)
            in
            let term, g = make_array tmp typ exp local fieldinfo.floc entry g in
            let cast_node = Node.make () in
            let cast_cmd =
              Cmd.Cset
                ( field,
                  Cil.CastE (Cil.TPtr (typ, []), Cil.Lval tmp),
                  fieldinfo.floc )
            in
            let g =
              g |> add_cmd cast_node cast_cmd |> add_edge term cast_node
            in
            let term, g =
              make_nested_array fd field typ exp local fieldinfo.floc cast_node
                false g
            in
            generate_allocs_field t lv local fd term g
        | TComp (comp, _) ->
            let field =
              addOffsetLval (Cil.Field (fieldinfo, Cil.NoOffset)) lv
            in
            let term, g = make_struct field comp local fieldinfo.floc entry g in
            let term, g =
              generate_allocs_field comp.cfields field local fd term g
            in
            generate_allocs_field t lv local fd term g
        | _ -> generate_allocs_field t lv local fd entry g)

  and get_base_type = function
    | TArray (t, _, _) | TPtr (t, _) -> get_base_type t
    | typ -> typ

  let rec generate_local_allocs fd vl entry g =
    match vl with
    | [] -> (entry, g)
    | varinfo :: t -> (
        match Cil.unrollTypeDeep varinfo.vtype with
        | TArray (typ, Some exp, _) ->
            let lv = (Cil.Var varinfo, Cil.NoOffset) in
            let tmp =
              (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset)
            in
            let term, g = make_array tmp typ exp true varinfo.vdecl entry g in
            let cast_node = Node.make () in
            let cast_cmd =
              Cmd.Cset
                ( lv,
                  Cil.CastE (Cil.TPtr (unrollTypeDeep typ, []), Cil.Lval tmp),
                  varinfo.vdecl )
            in
            let g =
              g |> add_cmd cast_node cast_cmd |> add_edge term cast_node
            in
            let term, g =
              make_nested_array fd lv typ exp true varinfo.vdecl cast_node false
                g
            in
            generate_local_allocs fd t term g
        | TComp (comp, _) ->
            let lv = (Cil.Var varinfo, Cil.NoOffset) in
            let term, g = make_struct lv comp true varinfo.vdecl entry g in
            let term, g =
              generate_allocs_field comp.cfields lv true fd term g
            in
            generate_local_allocs fd t term g
        | _ -> generate_local_allocs fd t entry g)

  let replace_node_graph old entry exit g =
    let preds = pred old g in
    let succs = succ old g in
    let g = remove_node old g in
    let g = List.fold_left (fun g p -> add_edge p entry g) g preds in
    let g = List.fold_left (fun g s -> add_edge exit s g) g succs in
    g

  let transform_string_allocs fd g =
    let rec replace_str e =
      match e with
      | Const (CStr s) ->
          let tempinfo =
            Cil.makeTempVar fd (Cil.TPtr (Cil.TInt (IChar, []), []))
          in
          let temp = (Cil.Var tempinfo, Cil.NoOffset) in
          (Lval temp, [ (temp, s) ])
      | Lval (Mem exp, off) -> (
          let exp', l = replace_str exp in
          match l with [] -> (e, l) | _ -> (Lval (Mem exp', off), l))
      | SizeOfStr s ->
          let tempinfo =
            Cil.makeTempVar fd (Cil.TPtr (Cil.TInt (IChar, []), []))
          in
          let temp = (Cil.Var tempinfo, Cil.NoOffset) in
          (Lval temp, [ (temp, s) ])
      | SizeOfE exp -> (
          let exp', l = replace_str exp in
          match l with [] -> (e, l) | _ -> (SizeOfE exp', l))
      | AlignOfE exp -> (
          let exp', l = replace_str exp in
          match l with [] -> (e, l) | _ -> (AlignOfE exp', l))
      | UnOp (u, exp, t) -> (
          let exp', l = replace_str exp in
          match l with [] -> (e, l) | _ -> (UnOp (u, exp', t), l))
      | BinOp (b, e1, e2, t) -> (
          let e1', l1 = replace_str e1 in
          let e2', l2 = replace_str e2 in
          match l1 @ l2 with
          | [] -> (e, [])
          | _ -> (BinOp (b, e1', e2', t), l1 @ l2))
      | CastE (t, exp) -> (
          let exp', l = replace_str exp in
          match l with [] -> (e, l) | _ -> (CastE (t, exp'), l))
      | _ -> (e, [])
    in
    let generate_sallocs l loc node g =
      List.fold_left
        (fun (node, g) (lv, s) ->
          let new_node = Node.make () in
          let g = add_edge node new_node g in
          let cmd = Cmd.Csalloc (lv, s, loc) in
          let g = add_cmd new_node cmd g in
          (new_node, g))
        (node, g) l
    in
    let targets =
      [
        "strcpy";
        "strcat";
        "strncpy";
        "memcpy";
        "memmove";
        "strlen";
        "fgets";
        "sprintf";
        "scanf";
        "getenv";
        "strdup";
        "gettext";
        "getpwent";
        "strchr";
        "strrchr";
      ]
    in
    fold_node
      (fun n g ->
        match find_cmd n g with
        | Cmd.Cset (lv, e, loc) -> (
            match replace_str e with
            | _, [] -> g
            | e, l ->
                let empty_node, last_node = (Node.make (), Node.make ()) in
                let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
                let node, g = generate_sallocs l loc empty_node g in
                let cmd = Cmd.Cset (lv, e, loc) in
                let g = add_cmd last_node cmd g in
                let g = add_edge node last_node g in
                replace_node_graph n empty_node last_node g)
        | Cmd.Cassume (e, b, loc) -> (
            match replace_str e with
            | _, [] -> g
            | e, l ->
                let empty_node, last_node = (Node.make (), Node.make ()) in
                let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
                let node, g = generate_sallocs l loc empty_node g in
                let cmd = Cmd.Cassume (e, b, loc) in
                let g = add_cmd last_node cmd g in
                let g = add_edge node last_node g in
                replace_node_graph n empty_node last_node g)
        | Cmd.Ccall (_, Cil.Lval (Cil.Var f, Cil.NoOffset), _, _)
          when f.vstorage = Cil.Extern && not (List.mem f.vname targets) ->
            g
        | Cmd.Ccall (lv, f, el, loc) -> (
            let el, l =
              List.fold_left
                (fun (el, l) param ->
                  let e', l' = replace_str param in
                  (el @ [ e' ], l @ l'))
                ([], []) el
            in
            match (el, l) with
            | _, [] -> g
            | el, l ->
                let empty_node, last_node = (Node.make (), Node.make ()) in
                let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
                let node, g = generate_sallocs l loc empty_node g in
                let cmd = Cmd.Ccall (lv, f, el, loc) in
                let g = add_cmd last_node cmd g in
                let g = add_edge node last_node g in
                replace_node_graph n empty_node last_node g)
        | Cmd.Creturn (Some e, loc) -> (
            match replace_str e with
            | _, [] -> g
            | e, l ->
                let empty_node, last_node = (Node.make (), Node.make ()) in
                let g = add_cmd empty_node (Cmd.Cskip (Cmd.Unknown, loc)) g in
                let node, g = generate_sallocs l loc empty_node g in
                let cmd = Cmd.Creturn (Some e, loc) in
                let g = add_cmd last_node cmd g in
                let g = add_edge node last_node g in
                replace_node_graph n empty_node last_node g)
        | _ -> g)
      g g

  let transform_malloc fd g =
    let rec transform lv exp loc node g =
      match exp with
      | BinOp (Mult, SizeOf typ, e, _)
      | BinOp (Mult, e, SizeOf typ, _)
      | BinOp (Mult, CastE (_, SizeOf typ), e, _)
      | BinOp (Mult, e, CastE (_, SizeOf typ), _) -> (
          let typ = Cil.unrollTypeDeep typ in
          match (lv, typ) with
          | (Var _, NoOffset), TComp (_, _) ->
              let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
              let g = add_cmd node cmd g in
              make_nested_array fd lv typ e false loc node false g
          | _ ->
              let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
              let g = add_cmd node cmd g in
              (node, g))
      | BinOp (Mult, SizeOfE ex1, ex2, t)
      | BinOp (Mult, ex2, SizeOfE ex1, t)
      | BinOp (Mult, CastE (_, SizeOfE ex1), ex2, t)
      | BinOp (Mult, ex2, CastE (_, SizeOfE ex1), t) ->
          transform lv
            (BinOp (Mult, SizeOf (Cil.typeOf ex1), ex2, t))
            loc node g
      | BinOp (PlusA, SizeOf typ, _, _)
      | BinOp (PlusA, CastE (_, SizeOf typ), _, _) ->
          transform lv (SizeOf typ) loc node g
      | BinOp (PlusA, SizeOfE ex1, _, _)
      | BinOp (PlusA, CastE (_, SizeOfE ex1), _, _) ->
          transform lv (SizeOf (Cil.typeOf ex1)) loc node g
      | SizeOf typ | CastE (_, SizeOf typ) -> (
          let typ = Cil.unrollTypeDeep typ in
          match (lv, typ) with
          | (Var _, NoOffset), TComp (comp, _) ->
              let cast_node = Node.make () in
              let cast_cmd =
                Cmd.Cset (lv, Cil.CastE (Cil.TPtr (typ, []), Cil.Lval lv), loc)
              in
              let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
              g |> add_cmd node cmd |> add_cmd cast_node cast_cmd
              |> add_edge node cast_node
              |> generate_allocs_field comp.cfields (Mem (Lval lv), NoOffset)
                   false fd cast_node
          | _, _ ->
              let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
              let g = add_cmd node cmd g in
              (node, g))
      | SizeOfE e | CastE (_, SizeOfE e) ->
          transform lv (SizeOf (Cil.typeOf e)) loc node g
      | CastE (_, e) -> transform lv e loc node g
      | _ ->
          let cmd = Cmd.Calloc (lv, Cmd.Array exp, false, false, loc) in
          let g = add_cmd node cmd g in
          (node, g)
    in
    let try_resolve_alloc_size fname args =
      match (fname, args) with
      | "malloc", size :: _ | "__builtin_alloca", size :: _ -> Some size
      | "realloc", _ :: size :: _ -> Some size
      | "calloc", n :: size :: _ -> Some (BinOp (Mult, n, size, Cil.uintType))
      | _, _ -> None
    in
    fold_node
      (fun n g ->
        match find_cmd n g with
        | Cmd.Ccall (Some lv, Lval (Var varinfo, NoOffset), args, loc) -> (
            match try_resolve_alloc_size varinfo.vname args with
            | Some arg ->
                let new_node = Node.make () in
                let preds = pred n g in
                let succs = succ n g in
                let g = List.fold_left (fun g s -> remove_edge n s g) g succs in
                let g = List.fold_left (fun g p -> remove_edge p n g) g preds in
                let g = remove_node n g in
                let g =
                  List.fold_left (fun g p -> add_edge p new_node g) g preds
                in
                let lv =
                  match lv with
                  | Var v, NoOffset ->
                      (Var { v with vtype = voidPtrType }, NoOffset)
                  | _ -> lv
                in
                let term, g = transform lv arg loc new_node g in
                List.fold_left (fun g s -> add_edge term s g) g succs
            | None -> g)
        | _ -> g)
      g g

  let insert_return_nodes g =
    List.fold_left
      (fun g c ->
        match find_cmd c g with
        | Cmd.Ccall (_, Lval (Var varinfo, _), _, loc)
          when varinfo.vname = "exit" || varinfo.vname = "abort"
               || Cil.hasAttribute "noreturn" varinfo.vattr ->
            let r = returnof c g in
            let n = Node.make () in
            remove_edge c r g
            |> add_cmd n (Cmd.Cskip (Cmd.ReturnNode, loc))
            |> add_edge c n
        | Cmd.Ccall (_, _, _, loc) ->
            let r = returnof c g in
            add_new_node c (Cmd.Cskip (Cmd.ReturnNode, loc)) r g
        | _ -> g)
      g (nodesof g)

  let insert_return_before_exit g =
    let add_return node acc =
      match find_cmd node g with
      | Cmd.Creturn _ -> acc
      | _ -> add_new_node node (Cmd.Creturn (None, locUnknown)) Node.EXIT acc
    in
    list_fold add_return (pred Node.EXIT g) g

  let compute_dom g =
    let dom_functions = Dom.compute_all (GDom.fromG g.graph) Node.ENTRY in
    let dom_tree =
      List.fold_left
        (fun dom_tree node ->
          List.fold_left
            (fun dom_tree child -> G.add_edge dom_tree node child)
            dom_tree
            (dom_functions.Dom.dom_tree node))
        G.empty (nodesof g)
    in
    let dom_fronts =
      List.fold_left
        (fun dom_fronts node ->
          BatMap.add node
            (NodeSet.of_list (dom_functions.Dom.dom_frontier node))
            dom_fronts)
        BatMap.empty (nodesof g)
    in
    let post_dom_functions = Dom.compute_all (Oper.mirror g.graph) Node.EXIT in
    let post_dom_fronts =
      List.fold_left
        (fun post_dom_fronts node ->
          BatMap.add node
            (NodeSet.of_list (post_dom_functions.Dom.dom_frontier node))
            post_dom_fronts)
        BatMap.empty (nodesof g)
    in
    { g with dom_tree; dom_fronts; post_dom_fronts }

  let compute_scc g = { g with scc_list = Scc.scc_list g.graph }

  let process_gvardecl fd lv init_opt loc entry g =
    match (Cil.unrollTypeDeep (Cil.typeOfLval lv), init_opt) with
    | TArray (typ, Some exp, _), _ ->
        let tmp =
          (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset)
        in
        let term, g = make_array tmp typ exp false loc entry g in
        let cast_node = Node.make () in
        let cast_cmd =
          Cmd.Cset (lv, Cil.CastE (Cil.TPtr (typ, []), Cil.Lval tmp), loc)
        in
        let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
        let term, g =
          make_nested_array fd lv typ exp false loc cast_node true g
        in
        (term, g)
    | TArray (typ, None, _), Some ilist ->
        let tmp =
          (Cil.Var (Cil.makeTempVar fd Cil.voidPtrType), Cil.NoOffset)
        in
        let exp = List.length ilist |> Cil.integer in
        let term, g = make_array tmp typ exp false loc entry g in
        let cast_node = Node.make () in
        let cast_cmd =
          Cmd.Cset (lv, Cil.CastE (Cil.TPtr (typ, []), Cil.Lval tmp), loc)
        in
        let g = g |> add_cmd cast_node cast_cmd |> add_edge term cast_node in
        let term, g =
          make_nested_array fd lv typ exp false loc cast_node true g
        in
        (term, g)
    | TInt (_, _), _ | TFloat (_, _), _ ->
        let node = Node.make () in
        let cmd = Cmd.Cset (lv, Cil.zero, loc) in
        (node, g |> add_cmd node cmd |> add_edge entry node)
    | TComp (comp, _), _ ->
        let term, g = make_struct lv comp false loc entry g in
        let term, g = generate_allocs_field comp.cfields lv false fd term g in
        (term, g)
    | _ -> (entry, g)

  let rec process_init fd lv i loc entry g =
    match i with
    | SingleInit exp ->
        let new_node = Node.make () in
        let cmd = Cmd.Cset (lv, exp, loc) in
        let g = add_edge entry new_node (add_cmd new_node cmd g) in
        (new_node, g)
    | CompoundInit (_, ilist) ->
        List.fold_left
          (fun (node, g) (offset, init) ->
            let lv = Cil.addOffsetLval offset lv in
            process_init fd lv init loc node g)
          (entry, g) ilist

  let process_gvar fd lv i loc entry g =
    match (Cil.typeOfLval lv, i.init) with
    | _, None -> process_gvardecl fd lv None loc entry g
    | _, Some (SingleInit _ as init) -> process_init fd lv init loc entry g
    | _, Some (CompoundInit (_, ilist) as init) ->
        let length = List.length ilist in
        if length > 1000 then
          Logger.warn "WARN: too large global array initialization (%d) %@ %s\n"
            (List.length ilist) (s_location loc);
        let node, g = process_gvardecl fd lv (Some ilist) loc entry g in
        if length < max_int then process_init fd lv init loc node g
        else (node, g)

  let get_main_dec globals =
    List.fold_left
      (fun s g ->
        match g with
        | Cil.GFun (fundec, loc) when fundec.svar.vname = "main" ->
            Some (fundec, loc)
        | _ -> s)
      None globals

  let process_fundecl fundecl loc node g =
    let new_node = Node.make () in
    let cmd = Cmd.Cfalloc ((Var fundecl.svar, NoOffset), fundecl, loc) in
    let g = add_edge node new_node (add_cmd new_node cmd g) in
    (new_node, g)

  let generate_cmd_args fd loc g =
    let argc, argv =
      ( (Cil.Var (List.nth fd.sformals 0), Cil.NoOffset),
        (Cil.Var (List.nth fd.sformals 1), Cil.NoOffset) )
    in
    let arg_node = Node.make () in
    let arg_cmd =
      Cmd.Ccall
        ( None,
          Cil.Lval
            ( Cil.Var (Cil.makeGlobalVar "sparrow_arg" Cil.voidType),
              Cil.NoOffset ),
          [ Cil.Lval argc; Cil.Lval argv ],
          loc )
    in
    let optind, optarg =
      ( (Cil.Var (Cil.makeGlobalVar "optind" Cil.intType), Cil.NoOffset),
        (Cil.Var (Cil.makeGlobalVar "optarg" Cil.charPtrType), Cil.NoOffset) )
    in
    let opt_node = Node.make () in
    let opt_cmd =
      Cmd.Ccall
        ( None,
          Cil.Lval
            ( Cil.Var (Cil.makeGlobalVar "sparrow_opt" Cil.voidType),
              Cil.NoOffset ),
          [ Cil.Lval optind; Cil.Lval optarg ],
          loc )
    in
    let g =
      g |> add_cmd arg_node arg_cmd |> add_cmd opt_node opt_cmd
      |> add_edge Node.ENTRY arg_node
      |> add_edge arg_node opt_node
    in
    (opt_node, g)

  let ignore_function fd =
    List.map (fun str -> Str.regexp (".*" ^ str ^ ".*")) []
    |> List.exists (fun re -> Str.string_match re fd.svar.vname 0)

  let init fd loc =
    let g =
      empty fd
      |> add_node_with_cmd Node.ENTRY (Cmd.Cskip (Cmd.Unknown, loc))
      |> add_node_with_cmd Node.EXIT (Cmd.Cskip (Cmd.Unknown, loc))
    in
    if Cil.hasAttribute "noreturn" fd.svar.vattr || ignore_function fd then
      add_edge Node.ENTRY Node.EXIT g
    else
      let entry = Node.fromCilStmt (List.nth fd.sallstmts 0) in
      let g =
        (list_fold
           (fun s ->
             add_node_with_cmd (Node.fromCilStmt s) (Cmd.fromCilStmt s.skind))
           fd.sallstmts
        >>> list_fold
              (fun stmt ->
                list_fold
                  (fun succ ->
                    add_edge (Node.fromCilStmt stmt) (Node.fromCilStmt succ))
                  stmt.succs)
              fd.sallstmts)
          g
      in
      let term, g =
        if fd.svar.vname = "main" && List.length fd.sformals >= 2 then
          generate_cmd_args fd loc g
        else (Node.ENTRY, g)
      in
      let term, g = generate_local_allocs fd fd.slocals term g in
      let g = add_edge term entry g in
      let nodes = nodesof g in
      let lasts = List.filter (fun n -> succ n g = []) nodes in
      g
      |> list_fold
           (function Node.EXIT -> id | last -> add_edge last Node.EXIT)
           lasts
      |> generate_assumes |> flatten_instructions |> remove_if_loop
      |> transform_malloc fd |> transform_string_allocs fd |> remove_empty_nodes
      |> insert_return_nodes |> insert_return_before_exit

  let ignore_file regexps loc =
    List.exists (fun re -> Str.string_match re loc.file 0) regexps

  let generate_global_proc globals fd =
    let entry = Node.ENTRY in
    let regexps = List.map (fun str -> Str.regexp (".*" ^ str ^ ".*")) [] in
    let term, g =
      List.fold_left
        (fun (node, g) x ->
          match x with
          | Cil.GVar (var, init, loc) when not (ignore_file regexps loc) ->
              process_gvar fd (Cil.var var) init loc node g
          | Cil.GVarDecl (var, loc) when not (ignore_file regexps loc) ->
              process_gvardecl fd (Cil.var var) None loc node g
          | Cil.GFun (fundec, loc) when not (ignore_file regexps loc) ->
              process_fundecl fundec loc node g
          | _ -> (node, g))
        (entry, empty fd)
        globals
    in
    let add_call_main g =
      match get_main_dec globals with
      | Some (main_dec, main_loc) ->
          let call_node = Node.make () in
          let call_cmd =
            Cmd.Ccall (None, Lval (Var main_dec.svar, NoOffset), [], main_loc)
          in
          g |> add_cmd call_node call_cmd |> add_edge term call_node
          |> add_edge call_node Node.EXIT
      | None ->
          prerr_endline "Warning: main not Found";
          g |> add_edge term Node.EXIT
    in
    g |> add_call_main |> generate_assumes |> flatten_instructions
    |> remove_if_loop |> transform_string_allocs fd |> remove_empty_nodes
    |> insert_return_nodes

  let unreachable_node g =
    let all_nodes = NodeSet.of_list (nodesof g) in
    let rec remove_reachable_node' work acc =
      if NodeSet.is_empty work then acc
      else
        let node, work = NodeSet.pop work in
        if NodeSet.mem node acc then
          let acc = NodeSet.remove node acc in
          let succs = NodeSet.remove node (NodeSet.of_list (succ node g)) in
          let work = NodeSet.union work succs in
          remove_reachable_node' work acc
        else remove_reachable_node' work acc
    in
    remove_reachable_node' (NodeSet.singleton Node.ENTRY) all_nodes

  let merge_vertex g vl =
    { g with graph = Merge.merge_vertex g.graph vl }
    |> remove_edge (List.hd vl) (List.hd vl)

  let rec collect g n lval node_list exp_list =
    let s = succ n g |> List.hd in
    match (find_cmd n g, find_cmd s g) with
    | Cmd.Csalloc (_, str, _), Cmd.Cset (l, _, _) -> (
        match Cil.removeOffsetLval l with
        | l, Cil.Index (i, Cil.NoOffset)
          when Ast.eq_lval lval l && Cil.isConstant i ->
            let node_list, exp_list =
              (n :: s :: node_list, Cil.mkString str :: exp_list)
            in
            let ss = succ s g in
            if List.length ss = 1 then
              collect g (List.hd ss) lval node_list exp_list
            else (node_list, exp_list)
        | _ -> (node_list, exp_list))
    | Cmd.Cset (l, e, _), _ when Cil.isConstant e -> (
        match Cil.removeOffsetLval l with
        | l, Cil.Index (i, Cil.NoOffset)
          when Ast.eq_lval lval l && Cil.isConstant i ->
            let node_list, exp_list = (n :: node_list, e :: exp_list) in
            let ss = succ n g in
            if List.length ss = 1 then
              collect g (List.hd ss) lval node_list exp_list
            else (node_list, exp_list)
        | _ -> (node_list, exp_list))
    | _ -> (node_list, exp_list)

  let is_candidate n g =
    let is_starting_point lval =
      match Cil.removeOffsetLval lval with
      | l, Cil.Index (i, Cil.NoOffset) when Cil.isZero i -> Some l
      | _ -> None
    in
    let ss = try succ n g with _ -> [] in
    if List.length ss = 1 then
      let s = List.hd ss in
      match (find_cmd n g, find_cmd s g) with
      | Cmd.Csalloc (_, _, _), Cmd.Cset (lval, e, _)
        when Cil.isPointerType (Cil.typeOf e) ->
          is_starting_point lval
      | Cmd.Cset (lval, e, _), _ when Cil.isIntegralType (Cil.typeOf e) ->
          is_starting_point lval
      | _ -> None
    else None

  let optimize_array_init g =
    fold_node
      (fun n g ->
        match is_candidate n g with
        | Some lval ->
            let nodes, exps = collect g n lval [] [] in
            if List.length nodes > 1 then
              let new_node = Node.make () in
              let g = merge_vertex g (new_node :: nodes) in
              let args = Cil.Lval lval :: List.rev exps in
              let loc = find_cmd n g |> Cmd.location_of in
              let cmd =
                Cmd.Ccall
                  ( None,
                    Cil.Lval
                      ( Cil.Var
                          (Cil.makeGlobalVar "sparrow_array_init" Cil.voidType),
                        Cil.NoOffset ),
                    args,
                    loc )
              in
              add_cmd new_node cmd g
            else g
        | _ -> g)
      g g

  let optimize = optimize_array_init
end

module InterCfg = struct
  module Proc = struct
    include String

    let equal = ( = )
    let hash = Hashtbl.hash
    let to_string x = x
    let pp fmt x = Format.fprintf fmt "%s" x
  end

  module ProcSet = BatSet.Make (Proc)

  type pid = Proc.t

  module Node = struct
    type t = Proc.t * IntraCfg.Node.t [@@deriving compare, equal]

    let make pid node = (pid, node)
    let get_pid = fst
  end

  module IntraNodeSet = IntraCfg.NodeSet
  module NodeSet = BatSet.Make (Node)

  type node = Node.t

  type t = {
    cfgs : (pid, IntraCfg.t) BatMap.t;
    globals : Cil.global list;
    call_edges : (Node.t, ProcSet.t) BatMap.t;
  }

  let add_call_edge call_node pid g =
    let callees =
      (try BatMap.find call_node g.call_edges with _ -> ProcSet.empty)
      |> ProcSet.add pid
    in
    { g with call_edges = BatMap.add call_node callees g.call_edges }

  let global_proc = "_G_"

  let ignore_file regexps loc =
    List.exists (fun re -> Str.string_match re loc.file 0) regexps

  let gen_cfgs file =
    let regexps = List.map (fun str -> Str.regexp (".*" ^ str ^ ".*")) [] in
    BatMap.add global_proc
      (IntraCfg.generate_global_proc file.Cil.globals
         (Cil.emptyFunction global_proc))
      (list_fold
         (fun g m ->
           match g with
           | Cil.GFun (f, loc) when not (ignore_file regexps loc) ->
               BatMap.add f.svar.vname (IntraCfg.init f loc) m
           | _ -> m)
         file.Cil.globals BatMap.empty)

  let compute_dom_and_scc icfg =
    {
      icfg with
      cfgs =
        BatMap.map
          (fun cfg -> IntraCfg.compute_scc (IntraCfg.compute_dom cfg))
          icfg.cfgs;
    }

  let remove_function pid icfg =
    let is_not_pid_node node _ = Node.get_pid node <> pid in
    {
      icfg with
      cfgs = BatMap.remove pid icfg.cfgs;
      call_edges = BatMap.filter is_not_pid_node icfg.call_edges;
    }

  let cfgof g pid =
    try BatMap.find pid g.cfgs
    with Not_found ->
      prerr_endline ("InterCfg.cfgof " ^ pid);
      raise Not_found

  let cmdof g (pid, node) = IntraCfg.find_cmd node (cfgof g pid)

  let nodes_of_pid g pid =
    List.map (Node.make pid) (IntraCfg.nodesof (cfgof g pid))

  let fold_cfgs f g a = BatMap.foldi f g.cfgs a
  let map_cfgs f g = { g with cfgs = BatMap.map f g.cfgs }

  let nodesof g =
    BatMap.foldi
      (fun pid cfg ->
        List.append (List.map (fun n -> Node.make pid n) (IntraCfg.nodesof cfg)))
      g.cfgs []

  let pidsof g = BatMap.foldi (fun pid _ acc -> pid :: acc) g.cfgs []
  let is_def pid g = BatMap.mem pid g.cfgs
  let is_undef pid g = not (BatMap.mem pid g.cfgs)

  let unreachable_node_pid pid icfg =
    IntraNodeSet.fold
      (fun node -> NodeSet.add (pid, node))
      (IntraCfg.unreachable_node icfg)
      NodeSet.empty

  let unreachable_node g =
    let add_unreachable_node pid icfg =
      NodeSet.union (unreachable_node_pid pid icfg)
    in
    fold_cfgs add_unreachable_node g NodeSet.empty

  let remove_node (pid, intra_node) g =
    let intra_cfg = cfgof g pid in
    let intra_cfg = IntraCfg.remove_node intra_node intra_cfg in
    { g with cfgs = BatMap.add pid intra_cfg g.cfgs }

  let node_to_lstr icfg node =
    cmdof icfg node |> IntraCfg.Cmd.location_of |> s_location

  let optimize_il icfg = icfg |> map_cfgs IntraCfg.optimize

  let init file =
    {
      cfgs = gen_cfgs file;
      globals = file.Cil.globals;
      call_edges = BatMap.empty;
    }
    |> optimize_il |> compute_dom_and_scc
end

module PowDom = struct
  module type CPO = sig
    include CPO

    type elt

    module A : AbsDom.SET with type t = elt

    val empty : t
    val filter : (elt -> bool) -> t -> t
    val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
    val fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
    val map : (elt -> elt) -> t -> t
    val iter : (elt -> unit) -> t -> unit
    val singleton : elt -> t
    val subset : t -> t -> bool
    val cardinal : t -> int
    val mem : elt -> t -> bool
    val add : elt -> t -> t
    val diff : t -> t -> t
    val choose : t -> elt
    val pop : t -> elt * t
    val remove : elt -> t -> t
    val is_empty : t -> bool
    val union : t -> t -> t
    val union_small_big : t -> t -> t
    val inter : t -> t -> t
    val for_all : (elt -> bool) -> t -> bool
    val exists : (elt -> bool) -> t -> bool
    val of_list : elt list -> t
    val elements : t -> elt list
  end

  module type LAT = sig
    include AbsDom.LAT
    include CPO with type t := t
  end

  module MakeCPO (A : SET) = struct
    module BatSet = BatSet.Make (A)
    module A = A

    type elt = A.t
    type t = BatSet.t

    let compare = BatSet.compare

    let le : t -> t -> bool =
     fun x y -> if x == y then true else BatSet.subset x y

    let eq : t -> t -> bool =
     fun x y -> if x == y then true else BatSet.equal x y

    let bot = BatSet.empty
    let empty = bot

    let join : t -> t -> t =
     fun x y -> if le x y then y else if le y x then x else BatSet.union x y

    let union = join
    let filter : (elt -> bool) -> t -> t = fun f s -> BatSet.filter f s
    let fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a = BatSet.fold
    let singleton : elt -> t = fun e -> BatSet.singleton e
    let subset : t -> t -> bool = BatSet.subset
    let cardinal : t -> int = BatSet.cardinal
    let mem : elt -> t -> bool = BatSet.mem
    let add e s = BatSet.add e s
    let diff = BatSet.diff
    let elements = BatSet.elements
    let is_empty = BatSet.is_empty
    let for_all = BatSet.for_all
    let of_list = BatSet.of_list

    let pp fmt x =
      let pp_sep fmt () = Format.fprintf fmt "," in
      let pp_list fmt l = Format.pp_print_list ~pp_sep A.pp fmt l in
      if is_empty x then Format.fprintf fmt "bot"
      else Format.fprintf fmt "{%a}" pp_list (elements x)
  end
end

module BasicDom = struct
  module Proc = InterCfg.Proc
  module PowProc = PowDom.MakeCPO (Proc)
end

module Callgraph = struct
  module G = struct
    include Graph.Imperative.Digraph.Concrete (BasicDom.Proc)
    module PredHash = Hashtbl.Make (BasicDom.Proc)

    let pred_hash = PredHash.create 10000

    let bootstrap g =
      PredHash.clear pred_hash;
      iter_edges
        (fun s d ->
          let old_pred =
            try PredHash.find pred_hash d with _ -> BasicDom.PowProc.empty
          in
          let new_pred = BasicDom.PowProc.add s old_pred in
          PredHash.replace pred_hash d new_pred)
        g

    let add_edge_htbl g s d =
      let old_pred =
        try PredHash.find pred_hash d with _ -> BasicDom.PowProc.empty
      in
      let new_pred = BasicDom.PowProc.add s old_pred in
      PredHash.replace pred_hash d new_pred;
      add_edge g s d

    let fold_pred_htbl f _ v a =
      let preds =
        try PredHash.find pred_hash v with _ -> BasicDom.PowProc.empty
      in
      BasicDom.PowProc.fold f preds a

    let add_transitive_closure_htbl g0 =
      let phi v g =
        fold_succ
          (fun sv g ->
            fold_pred_htbl
              (fun pv g ->
                add_edge_htbl g pv sv;
                g)
              g v g)
          g v g
      in
      fold_vertex phi g0 g0

    let transitive_closure g0 =
      bootstrap g0;
      add_transitive_closure_htbl (copy g0)
  end

  module Oper = Graph.Oper.I (G)

  type t = { graph : G.t; trans_callees : G.t; trans_callers : G.t }

  let empty () =
    {
      graph = G.create ();
      trans_callees = G.create ();
      trans_callers = G.create ();
    }

  let add_edge src dst g =
    G.add_edge g.graph src dst;
    g

  let callees pid g = G.succ g.graph pid |> BasicDom.PowProc.of_list

  let trans_callees pid g =
    G.succ g.trans_callees pid |> BasicDom.PowProc.of_list

  let trans_callers pid g =
    G.succ g.trans_callers pid |> BasicDom.PowProc.of_list

  let compute_transitive callgraph =
    let trans_callees = G.transitive_closure callgraph.graph in
    let trans_callers =
      G.copy callgraph.graph |> Oper.mirror |> G.transitive_closure
    in
    { callgraph with trans_callees; trans_callers }

  let is_rec callgraph pid =
    if G.mem_vertex callgraph.trans_callees pid then
      let trans = G.succ callgraph.trans_callees pid in
      List.mem pid trans
    else true

  let remove_function pid callgraph =
    G.remove_vertex callgraph.graph pid;
    callgraph
end

module CallGraph = struct
  open BasicDom

  module G = struct
    include Graph.Imperative.Digraph.Concrete (BasicDom.Proc)
    module PredHash = Hashtbl.Make (BasicDom.Proc)

    let pred_hash = PredHash.create 10000

    let bootstrap g =
      PredHash.clear pred_hash;
      iter_edges
        (fun s d ->
          let old_pred =
            try PredHash.find pred_hash d with _ -> PowProc.empty
          in
          let new_pred = PowProc.add s old_pred in
          PredHash.replace pred_hash d new_pred)
        g

    let add_edge_htbl g s d =
      let old_pred = try PredHash.find pred_hash d with _ -> PowProc.empty in
      let new_pred = PowProc.add s old_pred in
      PredHash.replace pred_hash d new_pred;
      add_edge g s d

    let fold_pred_htbl f _ v a =
      let preds = try PredHash.find pred_hash v with _ -> PowProc.empty in
      PowProc.fold f preds a

    let add_transitive_closure_htbl g0 =
      let phi v g =
        fold_succ
          (fun sv g ->
            fold_pred_htbl
              (fun pv g ->
                add_edge_htbl g pv sv;
                g)
              g v g)
          g v g
      in
      fold_vertex phi g0 g0

    let transitive_closure g0 =
      bootstrap g0;
      add_transitive_closure_htbl (copy g0)
  end

  module Oper = Graph.Oper.I (G)

  type t = { graph : G.t; trans_callees : G.t; trans_callers : G.t }

  let empty () =
    {
      graph = G.create ();
      trans_callees = G.create ();
      trans_callers = G.create ();
    }

  let add_edge src dst g =
    G.add_edge g.graph src dst;
    g

  let callees pid g = G.succ g.graph pid |> PowProc.of_list
  let trans_callees pid g = G.succ g.trans_callees pid |> PowProc.of_list
  let trans_callers pid g = G.succ g.trans_callers pid |> PowProc.of_list

  let compute_transitive callgraph =
    let trans_callees = G.transitive_closure callgraph.graph in
    let trans_callers =
      G.copy callgraph.graph |> Oper.mirror |> G.transitive_closure
    in
    { callgraph with trans_callees; trans_callers }

  let is_rec callgraph pid =
    if G.mem_vertex callgraph.trans_callees pid then
      let trans = G.succ callgraph.trans_callees pid in
      List.mem pid trans
    else true

  let remove_function pid callgraph =
    G.remove_vertex callgraph.graph pid;
    callgraph
end

module Global = struct
  open BasicDom
  open InterCfg

  type t = {
    file : Cil.file;
    icfg : InterCfg.t;
    callgraph : CallGraph.t;
    line_to_func : (string, string) BatMap.t;
  }

  let remove_nodes nodes global =
    { global with icfg = NodeSet.fold InterCfg.remove_node nodes global.icfg }

  let remove_functions pids global =
    let folder pid glob =
      {
        glob with
        icfg = InterCfg.remove_function pid glob.icfg;
        callgraph = CallGraph.remove_function pid glob.callgraph;
      }
    in
    let global = PowProc.fold folder pids global in
    { global with callgraph = CallGraph.compute_transitive global.callgraph }

  let is_rec pid global = CallGraph.is_rec global.callgraph pid

  let remove_unreachable_nodes global =
    let _ = InterCfg.nodesof global.icfg in
    let unreachable = InterCfg.unreachable_node global.icfg in
    let global = remove_nodes unreachable global in
    global

  let build_line_to_func_map global =
    let nodes = InterCfg.nodesof global.icfg in
    let folder acc n =
      BatMap.add (InterCfg.node_to_lstr global.icfg n) (Node.get_pid n) acc
    in
    let line_to_func = List.fold_left folder BatMap.empty nodes in
    { global with line_to_func }

  let init file =
    {
      file;
      icfg = InterCfg.init file;
      callgraph = CallGraph.empty ();
      line_to_func = BatMap.empty;
    }
    |> remove_unreachable_nodes
end

module PreProcess = struct
  open Global
  open BasicDom

  let collect_call_from_cmd icfg node acc_calls =
    match InterCfg.cmdof icfg node with
    | IntraCfg.Cmd.Ccall (_, Cil.Lval (Cil.Var f, Cil.NoOffset), _, _) ->
        if InterCfg.is_undef f.vname icfg then acc_calls
        else BatSet.add (node, f.vname) acc_calls
    | _ -> acc_calls

  let find_direct_calls icfg =
    let folder = collect_call_from_cmd icfg in
    let all_nodes = InterCfg.nodesof icfg in
    list_fold folder all_nodes BatSet.empty

  let approximate_call_graph global =
    let call_edges = find_direct_calls global.icfg in
    let folder (caller_node, callee_func) (icfg, callgraph) =
      let caller_func = InterCfg.Node.get_pid caller_node in
      ( InterCfg.add_call_edge caller_node callee_func icfg,
        CallGraph.add_edge caller_func callee_func callgraph )
    in
    let init = (global.icfg, global.callgraph) in
    let icfg, callgraph = BatSet.fold folder call_edges init in
    let callgraph = CallGraph.compute_transitive callgraph in
    { global with icfg; callgraph }

  let rec collect_fref_from_exp icfg gvar_map exp =
    match exp with
    | Cil.Const _ -> PowProc.empty
    | Cil.Lval l | Cil.StartOf l | Cil.AddrOf l ->
        collect_fref_from_lv icfg gvar_map l
    | Cil.SizeOf _ | Cil.SizeOfE _ | Cil.SizeOfStr _ -> PowProc.empty
    | Cil.AlignOf _ | Cil.AlignOfE _ -> PowProc.empty
    | Cil.UnOp (_, e, _) | Cil.CastE (_, e) ->
        collect_fref_from_exp icfg gvar_map e
    | Cil.BinOp (_, e1, e2, _) | Cil.Question (_, e1, e2, _) ->
        PowProc.union
          (collect_fref_from_exp icfg gvar_map e1)
          (collect_fref_from_exp icfg gvar_map e2)
    | Cil.AddrOfLabel _ -> PowProc.empty

  and collect_fref_from_lv icfg gvar_map lv =
    match fst lv with
    | Cil.Var v ->
        if InterCfg.is_def v.vname icfg then PowProc.singleton v.vname
        else if BatMap.mem v.vname gvar_map then BatMap.find v.vname gvar_map
        else PowProc.empty
    | Cil.Mem e -> collect_fref_from_exp icfg gvar_map e

  let weak_add k v m is_fixed =
    let prev_v = if BatMap.mem k m then BatMap.find k m else PowProc.empty in
    let new_v = PowProc.union v prev_v in
    (BatMap.add k new_v m, is_fixed && PowProc.subset v prev_v)

  let update_gvar_fref_map icfg node (acc_map, acc_flag) =
    match InterCfg.cmdof icfg node with
    | IntraCfg.Cmd.Cset ((Cil.Var v, _), e, _) ->
        let frefs = collect_fref_from_exp icfg acc_map e in
        if PowProc.is_empty frefs then (acc_map, acc_flag)
        else weak_add v.vname frefs acc_map acc_flag
    | IntraCfg.Cmd.Ccall
        ( _,
          Cil.Lval (Cil.Var f, Cil.NoOffset),
          Cil.Lval (Cil.Var v, _) :: real_arg_exps,
          _ )
      when f.vname = "sparrow_array_init" ->
        let frefs =
          List.map (collect_fref_from_exp icfg acc_map) real_arg_exps
          |> List.fold_left PowProc.union PowProc.empty
        in
        if PowProc.is_empty frefs then (acc_map, acc_flag)
        else weak_add v.vname frefs acc_map acc_flag
    | _ -> (acc_map, acc_flag)

  let build_gvar_fref_map icfg =
    let folder = update_gvar_fref_map icfg in
    let g_nodes = InterCfg.nodes_of_pid icfg InterCfg.global_proc in
    let rec fixpt gvar_map =
      let gvar_map, is_fixed = list_fold folder g_nodes (gvar_map, true) in
      if is_fixed then gvar_map else fixpt gvar_map
    in
    fixpt BatMap.empty

  let collect_fref_from_cmd icfg gvar_map node acc_frefs =
    match InterCfg.cmdof icfg node with
    | IntraCfg.Cmd.Cset (_, e, _) ->
        PowProc.union (collect_fref_from_exp icfg gvar_map e) acc_frefs
    | IntraCfg.Cmd.Ccall (_, f_exp, arg_exps, _) ->
        List.map (collect_fref_from_exp icfg gvar_map) arg_exps
        |> List.fold_left PowProc.union PowProc.empty
        |> PowProc.union (collect_fref_from_exp icfg gvar_map f_exp)
        |> PowProc.union acc_frefs
    | IntraCfg.Cmd.Creturn (Some e, _) ->
        PowProc.union (collect_fref_from_exp icfg gvar_map e) acc_frefs
    | _ -> acc_frefs

  let collect_fref_from_func icfg gvar_map f =
    let folder = collect_fref_from_cmd icfg gvar_map in
    let f_nodes = InterCfg.nodes_of_pid icfg f in
    list_fold folder f_nodes PowProc.empty

  let rec find_func_refs_loop icfg gvar_map acc_frefs visited = function
    | [] -> acc_frefs
    | head_func :: tail_funcs ->
        let frefs = collect_fref_from_func icfg gvar_map head_func in
        let acc_frefs = PowProc.union frefs acc_frefs in
        let to_add = PowProc.diff frefs visited in
        let visited = PowProc.union frefs visited in
        let worklist = PowProc.elements to_add @ tail_funcs in
        find_func_refs_loop icfg gvar_map acc_frefs visited worklist

  let find_func_refs icfg =
    let gvar_map = build_gvar_fref_map icfg in
    let worklist = [ "main" ] in
    find_func_refs_loop icfg gvar_map PowProc.empty PowProc.empty worklist
    |> PowProc.add InterCfg.global_proc
    |> PowProc.add "main"

  let remove_unreferred_funcs global =
    let frefs = find_func_refs global.icfg in
    let pids_all = PowProc.of_list (InterCfg.pidsof global.icfg) in
    let unrefs = PowProc.diff pids_all frefs in
    let _ = PowProc.filter (fun pid -> is_rec pid global) frefs in
    (* L.info "%-16s: %d\n" "#functions all" (PowProc.cardinal pids_all);
       L.info "%-16s: %d\n" "#referred" (PowProc.cardinal frefs);
       if PowProc.cardinal frefs > 0 then L.info "%a\n" PowProc.pp frefs;
       L.info "%-16s: %d\n" "#unreferred" (PowProc.cardinal unrefs);
       if PowProc.cardinal unrefs > 0 then L.info "%a\n" PowProc.pp unrefs;
       L.info "%-16s: %d\n" "#recursive" (PowProc.cardinal recursive);
       if PowProc.cardinal recursive > 0 then L.info "%a\n" PowProc.pp recursive; *)
    Global.remove_functions unrefs global

  let perform global = approximate_call_graph global |> remove_unreferred_funcs
end

let debug = false

exception Recursion (* Used to signal recursion *)

(* A visitor that makes a deep copy of a function body for use inside a host 
 * function, replacing duplicate labels, returns, etc. *)
class copyBodyVisitor (host : fundec)
  (* The host of the 
   * inlining *) (inlining : varinfo)
  (* Function being 
   * inlined *) (replVar : varinfo -> varinfo)
  (* Maps locals of the 
   * inlined function 
   * to locals of the 
   * host *)
    (retlval : varinfo option) (* The destination 
                                * for the "return" *)
  (replLabel : string -> string)
  (* A renamer for 
   * labels *)
    (retlab : stmt) (* The label for the 
                     * return *) =
  object
    inherit nopCilVisitor

    (* Keep here a maping from statements to their copies, indexed by their 
     * original ID *)
    val stmtmap : stmt IH.t = IH.create 113

    (* Keep here a list of statements to be patched *)
    val patches : stmt list ref = ref []
    val argid = ref 0

    (* This is the entry point *)
    method! vfunc (f : fundec) : fundec visitAction =
      let patchfunction (f' : fundec) =
        let findStmt (i : int) =
          try IH.find stmtmap i
          with Not_found -> E.s (bug "Cannot find the copy of stmt#%d" i)
        in
        let patchstmt (s : stmt) =
          match s.skind with
          | Goto (sr, l) ->
              if debug then E.log "patching goto\n";
              (* Make a copy of the reference *)
              let sr' = ref (findStmt !sr.sid) in
              s.skind <- Goto (sr', l)
          | Switch (e, body, cases, l) ->
              s.skind <-
                Switch
                  (e, body, Util.list_map (fun cs -> findStmt cs.sid) cases, l)
          | _ -> ()
        in
        List.iter patchstmt !patches;
        f'
      in
      patches := [];
      IH.clear stmtmap;
      ChangeDoChildrenPost (f, patchfunction)

    (* We must replace references to local variables *)
    method! vvrbl (v : varinfo) =
      if v.vglob then SkipChildren
      else
        let v' = replVar v in
        if v == v' then SkipChildren else ChangeTo v'

    method! vinst (i : instr) =
      match i with
      | Call (_, Lval (Var vi, _), _, _) when vi.vid == inlining.vid ->
          raise Recursion
      | _ -> DoChildren

    (* Replace statements. *)
    method! vstmt (s : stmt) : stmt visitAction =
      (* There is a possibility that we did not have the statements IDed 
       * propertly. So, we change the ID even on the replaced copy so that we 
       * can index on them ! *)
      (match host.smaxstmtid with
      | Some id -> s.sid <- 1 + id
      | None -> s.sid <- 1);
      (* Copy and change ID *)
      let s' = { s with sid = s.sid } in
      host.smaxstmtid <- Some s'.sid;

      IH.add stmtmap s.sid s';
      (* Remember where we copied this statement *)
      (* if we have a Goto or a Switch remember them to fixup at end *)
      (match s'.skind with
      | Goto _ | Switch _ -> patches := s' :: !patches
      | _ -> ());

      (* Change the returns *)
      let postProc (s' : stmt) : stmt =
        (* Rename the labels if necessary *)
        s'.labels <-
          Util.list_map
            (fun lb ->
              match lb with
              | Label (n, l, fromsrc) -> Label (replLabel n, l, fromsrc)
              | _ -> lb)
            s'.labels;

        (* Now deal with the returns *)
        (match s'.skind with
        | Return (ro, l) -> (
            (* Change this into an assignment followed by a Goto *)
            match (ro, retlval) with
            | _, None ->
                (* Function called with no return lval *)
                s'.skind <- Goto (ref retlab, l)
            | None, _ ->
                ignore (warn "Found return without value in inlined function");
                s'.skind <- Goto (ref retlab, l)
            | Some rv, Some retvar ->
                s'.skind <-
                  Block
                    (mkBlock
                       [
                         mkStmt (Instr [ Set (var retvar, rv, l) ]);
                         mkStmt (Goto (ref retlab, l));
                       ]))
        | _ -> ());
        s'
      in
      (* Do the children then postprocess *)
      ChangeDoChildrenPost (s', postProc)

    (* Copy blocks since they are mutable *)
    method! vblock (b : block) =
      ChangeDoChildrenPost ({ b with bstmts = b.bstmts }, fun x -> x)

    method! vglob _ = E.s (bug "copyFunction should not be used on globals")
  end

(** Replace a statement with the result of inlining *)
let replaceStatement (host : fundec) (* The host *)
    (inlineWhat : varinfo -> fundec option) (* What to inline *)
    (replLabel : string -> string)
    (* label 
     * replacement *) (anyInlining : bool ref)
    (* will set this 
     * to true if we 
     * did any 
     * inlining *) (s : stmt) : stmt =
  match s.skind with
  | Instr il when il <> [] ->
      let prevrstmts : stmt list ref = ref [] in
      (* Reversed list of previous 
       * statements *)
      let prevrinstr : instr list ref = ref [] in
      (* Reverse list of previous 
       * instructions, in this 
       * statement *)
      let emptyPrevrinstr () =
        if !prevrinstr <> [] then (
          prevrstmts := mkStmt (Instr (List.rev !prevrinstr)) :: !prevrstmts;
          prevrinstr := [])
      in

      let rec loop (rest : instr list) : unit =
        (* Remaining instructions *)
        match rest with
        | [] -> (* Done *) ()
        | (Call (lvo, Lval (Var fvi, NoOffset), args, l) as i) :: resti -> (
            if debug then E.log "Checking whether to inline %s\n" fvi.vname;
            let replo : fundec option =
              match inlineWhat fvi with
              | Some repl ->
                  if repl.svar.vid = host.svar.vid then (
                    ignore
                      (warn
                         "Inliner encountered recursion in inlined function %s"
                         host.svar.vname);
                    None)
                  else Some repl
              | None -> None
            in
            match replo with
            | None ->
                prevrinstr := i :: !prevrinstr;
                loop resti
            | Some repl ->
                anyInlining := true;
                prerr_endline
                  ("-inline " ^ repl.svar.vname ^ " @" ^ s_location l);

                (* We must inline *)
                (* Prepare the mapping of local variables *)
                let vmap : varinfo IH.t = IH.create 13 in
                let replVar (vi : varinfo) =
                  if vi.vglob then vi
                  else
                    try IH.find vmap vi.vid
                    with Not_found ->
                      E.s
                        (bug "Cannot find the new copy of local variable %s"
                           vi.vname)
                in
                (* Do the actual arguments, and keep extending prevrinstr *)
                let rec loopArgs (args : exp list) (formals : varinfo list) =
                  match (args, formals) with
                  | [], [] -> ()
                  | a :: args', f :: formals' ->
                      (* We must copy the argument even if it is already a 
                       * variable, to obey call by value *)
                      (* Make a local and a copy *)
                      let f' = makeTempVar host ~name:f.vname f.vtype in
                      prevrinstr := Set (var f', a, l) :: !prevrinstr;
                      IH.add vmap f.vid f';

                      loopArgs args' formals'
                  | _, _ -> E.bug "Invalid number of arguments"
                in
                loopArgs args repl.sformals;

                (* Copy the locals *)
                List.iter
                  (fun loc ->
                    let loc' = makeTempVar host ~name:loc.vname loc.vtype in
                    IH.add vmap loc.vid loc')
                  repl.slocals;

                (* Make the return statement *)
                let (ret : stmt), (retvar : varinfo option) =
                  let rt, _, _, _ = splitFunctionType repl.svar.vtype in
                  match rt with
                  | TVoid _ -> (mkStmt (Instr []), None)
                  | _ -> (
                      match lvo with
                      | None -> (mkStmt (Instr []), None)
                      | Some lv ->
                          (* Make a return variable *)
                          let rv =
                            makeTempVar host ~name:("ret_" ^ repl.svar.vname) rt
                          in
                          (mkStmtOneInstr (Set (lv, Lval (var rv), l)), Some rv)
                      )
                in
                ret.labels <-
                  [ Label (replLabel ("Lret_" ^ repl.svar.vname), l, false) ];
                let oldBody = repl.sbody in
                (* Now replace the body *)
                (try
                   ignore
                     (visitCilFunction
                        (new copyBodyVisitor
                           host repl.svar replVar retvar replLabel ret)
                        repl);
                   currentLoc := l;
                   let body' = repl.sbody in
                   (* Replace the old body in the function to inline *)
                   repl.sbody <- oldBody;

                   emptyPrevrinstr ();
                   prevrstmts := ret :: mkStmt (Block body') :: !prevrstmts
                 with Recursion ->
                   ignore
                     (warn "Encountered recursion in function %s"
                        repl.svar.vname);
                   prevrinstr := i :: !prevrinstr);

                loop resti)
        | i :: resti ->
            prevrinstr := i :: !prevrinstr;
            loop resti
      in
      loop il;

      emptyPrevrinstr ();
      if List.length !prevrstmts > 1 then
        s.skind <- Block (mkBlock (List.rev !prevrstmts));

      s
  | _ -> s

(** Apply inlining to a function, modify in place *)
let doFunction (host : fundec) (* The function into which to inline *)
    (inlineWhat : varinfo -> fundec option)
    (* The functions to 
     * inline, as a 
     * partial map 
     * from varinfo to 
     * body *)
      (anyInlining : bool ref) : unit =
  (* Will be set to true 
   * if any inlining 
   * took place *)
  (* Scan the host function and build the alpha-conversion table for labels *)
  let labTable : (string, unit A.alphaTableData ref) H.t = H.create 5 in
  ignore
    (visitCilBlock
       (object
          inherit nopCilVisitor

          method! vstmt (s : stmt) =
            List.iter
              (fun l ->
                match l with
                | Label (ln, _, _) ->
                    ignore
                      (A.registerAlphaName ~alphaTable:labTable ~undolist:None
                         ~data:() ~lookupname:ln)
                | _ -> ())
              s.labels;
            DoChildren
       end)
       host.sbody);
  (* Now the label replacement function *)
  let replLabel (ln : string) : string =
    let ln', _ =
      A.newAlphaName ~alphaTable:labTable ~undolist:None ~lookupname:ln ~data:()
    in
    ln'
  in
  (* Now scan the function to do the inlining *)
  let body' : block =
    visitCilBlock
      (object
         inherit nopCilVisitor

         method! vstmt (s : stmt) =
           ChangeDoChildrenPost
             (s, replaceStatement host inlineWhat replLabel anyInlining)
      end)
      host.sbody
  in
  host.sbody <- body';
  ()

(** Apply inlining to a whole file *)
let doFile (inlineWhat : varinfo -> fundec option)
    (* What to inline. See 
     * comments for [doFunction] *) (fl : file) =
  iterGlobals fl (fun g ->
      match g with
      | GFun (fd, _) ->
          (* Keep doing inlining until there is no more. We will catch 
           * recursion eventually when we want to inline a function into itself*)
          let anyInlining = ref true in
          while !anyInlining do
            anyInlining := false;
            doFunction fd inlineWhat anyInlining
          done
      | _ -> ())

(* Function names to inline *)
let toinline : string list ref = ref []

let doit (fl : file) =
  (* Scan the file and build the hashtable of functions to inline *)
  let inlineTable : (string, fundec) H.t = H.create 5 in
  visitCilFile
    (object
       inherit nopCilVisitor

       method! vfunc (fd : fundec) =
         if List.mem fd.svar.vname !toinline then
           H.add inlineTable fd.svar.vname fd;
         SkipChildren
    end)
    fl;
  let inlineWhat (vi : varinfo) : fundec option =
    try Some (H.find inlineTable vi.vname) with Not_found -> None
  in
  (* Give warnings if we cannot find some fundecs *)
  List.iter
    (fun fn ->
      if not (H.mem inlineTable fn) then
        ignore
          (warn
             "Cannot inline function %s because we cannot find its definition"
             fn))
    !toinline;

  doFile inlineWhat fl

(* let rec feature =
   {
     fd_name = "inliner";
     fd_enabled = false;
     fd_description = "inline function calls";
     fd_extraopt =
       [
         ( "--inline",
           Arg.String
             (fun s ->
               feature.fd_enabled <- true;
               toinline := s :: !toinline),
           "<func> inline this function" );
       ];
     fd_doit = doit;
     fd_post_check = true;
   } *)

let rec unnecessary_blk_remover stmts acc =
  match stmts with
  | [] -> acc
  | hd :: tl -> (
      match hd.skind with
      | Block b -> unnecessary_blk_remover tl acc @ b.bstmts
      | _ -> unnecessary_blk_remover tl (acc @ [ hd ]))

class blockRemoveVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vstmt (s : Cil.stmt) =
      match s.skind with
      | Block b when b.bstmts = [] -> ChangeTo (mkEmptyStmt ())
      | If (a, tb, fb, l) ->
          ChangeTo
            (Cil.mkStmt
               (If
                  ( a,
                    Cil.mkBlock (unnecessary_blk_remover tb.bstmts []),
                    Cil.mkBlock (unnecessary_blk_remover fb.bstmts []),
                    l )))
      | Loop (b, l, s1, s2) ->
          ChangeTo
            (Cil.mkStmt
               (Loop
                  (Cil.mkBlock (unnecessary_blk_remover b.bstmts []), l, s1, s2)))
      | _ -> DoChildren
  end

let is_varargs fid file =
  Cil.foldGlobals file
    (fun b global ->
      match global with
      | GFun (fd, _) when fd.svar.vname = fid -> (
          match fd.svar.vtype with TFun (_, _, b_va, _) -> b_va | _ -> b)
      | _ -> b)
    false

let inline opt (global : Global.t) =
  let f = global.file in
  let regexps = List.map (fun str -> Str.regexp (".*" ^ str ^ ".*")) opt in
  let to_inline =
    Ast.list_fold
      (fun global to_inline ->
        match global with
        | GFun (fd, _)
          when List.exists
                 (fun regexp -> Str.string_match regexp fd.svar.vname 0)
                 regexps ->
            fd.svar.vname :: to_inline
        | _ -> to_inline)
      f.globals []
  in
  let varargs_procs = List.filter (fun fid -> is_varargs fid f) to_inline in
  let recursive_procs =
    List.filter (fun fid -> Global.is_rec fid global) to_inline
  in
  let to_exclude = varargs_procs @ recursive_procs in
  toinline := List.filter (fun fid -> not (List.mem fid to_exclude)) to_inline;
  doit f;
  global

let do_inline (opt : string list) (file : Cil.file) =
  let global =
    file |> Global.init |> Global.build_line_to_func_map |> PreProcess.perform
    |> inline opt
  in
  let vis = new blockRemoveVisitor in
  ignore (Cil.visitCilFile vis file);
  global.file

let makeCFGinfo (f : Cil.file) =
  ignore (Partial.calls_end_basic_blocks f);
  ignore (Partial.globally_unique_vids f);
  Cil.iterGlobals f (fun glob ->
      match glob with
      | Cil.GFun (fd, _) ->
          Cil.prepareCFG fd;
          ignore (Cil.computeCFGInfo fd true)
      | _ -> ());
  f

class blockVisitor =
  object
    inherit Cil.nopCilVisitor

    method! vblock b =
      let stmts =
        List.fold_left
          (fun l stmt ->
            match stmt.Cil.skind with
            | Cil.Instr il when List.length il > 1 ->
                let new_il = List.map Cil.mkStmtOneInstr (List.tl il) in
                stmt.skind <- Instr [ List.hd il ];
                l @ (stmt :: new_il)
            | Cil.Instr il when List.length il = 0 -> l
            | _ -> l @ [ stmt ])
          [] b.bstmts
      in
      b.bstmts <- stmts;
      ChangeDoChildrenPost (b, fun x -> x)
  end

let perform inline_opt file =
  let cil = makeCFGinfo file |> do_inline (List.rev inline_opt) in
  Cil.visitCilFile (new blockVisitor) cil;
  cil
