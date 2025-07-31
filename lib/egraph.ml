open Sexplib.Std

module L = struct
  type 'a shape =
    | Match of 'a list * Ir.case list
    | FullMatch of int * int * 'a list * ('a list * 'a) list
    | LetIn of Ir.name list * 'a list * Ir.expr
    | Call of Ir.name * 'a list
    | Var of Ir.name
  [@@deriving ord, sexp]

  type t = Mk of t shape [@@unboxed] [@@deriving sexp]

  type op =
    | MatchOp of Ir.case list
    | FullMatchOp of int * int
    | LetInOp of Ir.name list * Ir.expr
    | CallOp of Ir.name
    | VarOp of Ir.name
  [@@deriving eq, sexp]

  let pp_op : Format.formatter -> op -> unit =
    fun fmt op ->
    match op with
    | MatchOp case_list ->
      Format.fprintf
        fmt
        "MatchOp %s"
        (String.concat "|\n" (List.map Ir.pp_case case_list))
    | FullMatchOp (i, j) -> Format.fprintf fmt "FullMatchOp %d %d" i j
    | LetInOp (names, body) ->
      Format.fprintf fmt "LetInOp %s %s" (String.concat ", " names) (Ir.pp_expr body)
    | CallOp name -> Format.fprintf fmt "CallOp %s" name
    | VarOp name -> Format.fprintf fmt "VarOp %s" name
  ;;

  let equal_op : op -> op -> bool = fun op1 op2 -> op1 = op2

  let pp_shape : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a shape -> unit =
    fun pp fmt shape ->
    match shape with
    | Match (match_list, case_list) ->
      Format.fprintf
        fmt
        "match %a with %s"
        (Format.pp_print_list pp)
        match_list
        (String.concat "\n" (List.map (fun case -> Ir.pp_case case) case_list))
    | FullMatch (_, _, match_list, case_list) ->
      let pp_case fmt (a, b) =
        Format.fprintf fmt "| %a -> %a" (Format.pp_print_list pp) a pp b
      in
      Format.fprintf
        fmt
        "match %a with %a"
        (Format.pp_print_list pp)
        match_list
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt "\n") pp_case)
        case_list
    | LetIn (names, args, body) ->
      Format.fprintf
        fmt
        "let %a = %a in %s"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
           Format.pp_print_string)
        names
        (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ") pp)
        args
        (Ir.pp_expr body)
    | Call (name, args) -> Format.fprintf fmt "%s %a" name (Format.pp_print_list pp) args
    | Var name -> Format.fprintf fmt "%s" name
  ;;

  let compare_shape : ('a -> 'a -> int) -> 'a shape -> 'a shape -> int =
    fun cmp shape1 shape2 ->
    ignore cmp;
    if shape1 = shape2 then 0 else 1
  ;;

  let op : 'a shape -> op =
    fun shape ->
    match shape with
    | Match (_, case_list) -> MatchOp case_list
    | FullMatch (i, j, _, _) -> FullMatchOp (i, j)
    | LetIn (names, _, body) -> LetInOp (names, body)
    | Call (name, _) -> CallOp name
    | Var name -> VarOp name
  ;;

  let children : 'a shape -> 'a list =
    fun shape ->
    match shape with
    | Match (match_list, _) -> match_list
    | FullMatch (_, _, match_list, case_list) ->
      match_list @ (List.map (fun (a, b) -> a @ [ b ]) case_list |> List.flatten)
    | LetIn (_, args, _) -> args
    | Call (_, args) -> args
    | Var _ -> []
  ;;

  let map_children : 'a shape -> ('a -> 'b) -> 'b shape =
    fun shape f ->
    match shape with
    | Match (match_list, case_list) ->
      let new_match_list = List.map f match_list in
      Match (new_match_list, case_list)
    | FullMatch (i, j, match_list, case_list) ->
      let new_match_list = List.map f match_list in
      let new_case_list = List.map (fun (a, b) -> List.map f a, f b) case_list in
      FullMatch (i, j, new_match_list, new_case_list)
    | LetIn (names, args, body) ->
      let new_args = List.map f args in
      LetIn (names, new_args, body)
    | Call (name, args) ->
      let new_args = List.map f args in
      Call (name, new_args)
    | Var name -> Var name
  ;;

  let make : op -> 'a list -> 'a shape =
    fun op args ->
    match op with
    | MatchOp case_list -> Match (args, case_list)
    | FullMatchOp (i, j) ->
      let range start stop =
        let rec range' i acc = if i >= stop then acc else range' (i + 1) (acc @ [ i ]) in
        range' start []
      in
      let slice i j lst =
        let rec aux i j lst acc =
          match lst with
          | [] -> List.rev acc
          | x :: xs ->
            if i = 0
            then if j = 0 then List.rev acc else aux i (j - 1) xs (x :: acc)
            else aux (i - 1) j xs acc
        in
        aux i j lst []
      in
      let match_list = slice 0 (i - 1) args in
      let rest = slice i (List.length args - 1) args in
      let range = range 0 j in
      let case_list =
        List.map
          (fun index ->
             let slicing = slice ((i + 1) * index) (((i + 1) * (index + 1)) - 1) rest in
             List.rev slicing |> List.tl |> List.rev, List.rev slicing |> List.hd)
          range
      in
      FullMatch (i, j, match_list, case_list)
    | LetInOp (names, body) -> LetIn (names, args, body)
    | CallOp name -> Call (name, args)
    | VarOp name -> Var name
  ;;
end

module A = struct
  type t = unit
  type data = int option [@@deriving eq, show]

  let pp_data : Format.formatter -> data -> unit =
    fun fmt data ->
    match data with
    | None -> Format.fprintf fmt "None"
    | Some n -> Format.fprintf fmt "%d" n
  ;;

  let show_data : data -> string =
    fun data ->
    match data with
    | None -> "None"
    | Some n -> string_of_int n
  ;;

  let equal_data : data -> data -> bool =
    fun data1 data2 ->
    match data1, data2 with
    | None, None -> true
    | Some n1, Some n2 -> n1 = n2
    | _ -> false
  ;;

  let default : data = None
end

module MA
    (S :
       Ego.Generic.GRAPH_API
       with type 'p t = (Ego.Id.t L.shape, A.t, A.data, 'p) Ego.Generic.egraph
        and type analysis := A.t
        and type data := A.data
        and type 'a shape := 'a L.shape
        and type node := L.t) =
struct
  type 'p t = 'p S.t

  let eval : A.data L.shape -> A.data =
    fun shape ->
    ignore shape;
    None
  ;;

  let make : Ego.Generic.ro t -> Ego.Id.t L.shape -> A.data =
    fun graph term -> eval (L.map_children term (S.get_data graph))
  ;;

  let merge : A.t -> A.data -> A.data -> A.data * (bool * bool) =
    fun () data1 data2 ->
    match data1, data2 with
    | Some l, _ -> Some l, (false, true)
    | _, Some l -> Some l, (true, false)
    | None, None -> None, (false, false)
  ;;

  let modify : Ego.Generic.rw t -> Ego.Id.t -> unit =
    fun graph cls ->
    match S.get_data (S.freeze graph) cls with
    | None -> ()
    | Some n ->
      let nw_cls = S.add_node graph (L.Mk (L.Var (string_of_int n))) in
      S.merge graph nw_cls cls
  ;;
end

module Egraph = Ego.Generic.Make (L) (A) (MA)

let rec l_of_expr : Ir.expr -> L.t =
  fun expr ->
  match expr.desc with
  | Ir.Call (name, args) ->
    let args = List.map l_of_expr args in
    L.Mk (L.Call (name, args))
  | Ir.Var name -> L.Mk (L.Var name)
  | Ir.Match (match_list, case_list) ->
    if
      List.for_all
        (fun case ->
           let (Ir.Case (pat, _)) = case in
           let pat_vars = Ir.collect_var_in_pat pat in
           List.is_empty pat_vars && not (pat = Ir.Pat_any))
        case_list
    then (
      let match_list = List.map l_of_expr match_list in
      let i = List.length match_list in
      let j = List.length case_list in
      let case_list =
        List.map
          (fun case ->
             let (Ir.Case (pat, body)) = case in
             let pat = Ir.{ desc = expr_of_pattern pat; typ = Tany } |> l_of_expr in
             let body = l_of_expr body in
             [ pat ], body)
          case_list
      in
      L.Mk (L.FullMatch (i, j, match_list, case_list)))
    else (
      let match_list = List.map l_of_expr match_list in
      L.Mk (L.Match (match_list, case_list)))
  | _ -> failwith "not implemented yet"
;;

let op_of_string str =
  match str with
  | str when String.starts_with ~prefix:"Call" str ->
    let name = String.sub str 5 (String.length str - 5) in
    L.CallOp name
  | str when String.starts_with ~prefix:"Var" str ->
    let name = String.sub str 4 (String.length str - 4) in
    L.VarOp name
  | str when String.starts_with ~prefix:"Match" str ->
    let str = String.sub str 6 (String.length str - 6) in
    let case_list = String.split_on_char '|' str in
    let case_list =
      List.map (fun case -> Ir.case_of_sexp (Sexplib.Sexp.of_string case)) case_list
    in
    L.MatchOp case_list
  | str when String.starts_with ~prefix:"LetIn" str ->
    let str = String.sub str 6 (String.length str - 6) in
    let str = String.split_on_char '_' str in
    let names = List.tl str in
    let body = List.hd str in
    L.LetInOp (names, Ir.expr_of_sexp (Sexplib.Sexp.of_string body))
  | _ -> failwith ("don't know: " ^ str)
;;

let copy graph =
  let version = graph.Ego.Generic.version in
  let analysis = graph.Ego.Generic.analysis in
  let uf = graph.Ego.Generic.uf in
  let limit = uf.limit in
  let content : Ego.Id.elem Ego.Id.Map.t = uf.content in
  let new_content = Ego.Id.Map.copy content in
  let uf = Ego.Id.{ limit; content = new_content } in
  let class_data = graph.Ego.Generic.class_data in
  let class_data = Ego.Id.Map.copy class_data in
  let hash_cons = graph.Ego.Generic.hash_cons in
  let hash_cons = Hashtbl.copy hash_cons in
  let pending = graph.Ego.Generic.pending in
  let pending = CCVector.copy pending in
  let pending_analysis = graph.Ego.Generic.pending_analysis in
  let pending_analysis = CCVector.copy pending_analysis in
  let new_graph =
    Ego.Generic.
      { version; analysis; uf; class_data; hash_cons; pending; pending_analysis }
  in
  new_graph
;;
