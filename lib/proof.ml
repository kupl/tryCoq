open Sexplib.Std

type t = (fact list * goal) list [@@deriving sexp]
and fact = prop [@@deriving sexp]
and goal = prop [@@deriving sexp]

and prop =
  | Eq of expr * expr
  | Le of expr * expr
  | Lt of expr * expr
  | And of prop * prop
  | Or of prop * prop
  | Not of prop
  | Forall of string * prop
  | Imply of prop * prop
  | Type of string * string
[@@deriving sexp]

and expr = Ir.expr [@@deriving sexp]

type theorem = tactic list * goal [@@deriving sexp]

and tactic =
  | ApplyInAt of string * string * int
  | Intro of string
  | RewriteInAt of string * string * int
  | Induction of string
  | Case of string
  | SimplInAt of string * string * int
  | Reflexivity
[@@deriving sexp]

let get_type env name =
  ignore (env, name);
  "int"
;;

let rec search_qvar name goal : goal =
  match goal with
  | Forall (var, goal') ->
    if var = name then goal' else Forall (var, search_qvar name goal')
  | _ -> failwith "There is no such universal variable in goal"
;;

let apply_tactic t env tactic : t =
  let facts, goal = List.hd t in
  match tactic with
  | ApplyInAt (fact, target, i) ->
    ignore (fact, target, i);
    t
  | Intro name ->
    let new_state =
      match goal with
      | Forall (var, goal) ->
        if var = name
        then facts @ [ Type (name, get_type env name) ], goal
        else
          facts @ [ Type (name, get_type env name) ], Forall (var, search_qvar name goal)
      | Imply (p1, p2) -> facts @ [ p1 ], p2
      | _ -> failwith "There is no term that can be introduced"
    in
    new_state :: List.tl t
  | RewriteInAt (fact, target, i) ->
    ignore (fact, target, i);
    t
  | Induction name ->
    ignore name;
    t
  | Case name ->
    ignore name;
    t
  | SimplInAt (fact, target, i) ->
    ignore (fact, target, i);
    t
  | Reflexivity ->
    (match goal with
     | Eq (e1, e2) when e1 = e2 -> List.tl t
     | _ -> failwith "The goal is not an equality")
;;

let string_of_t t = t |> sexp_of_t |> Sexplib.Sexp.to_string
let string_of_theorem t = t |> sexp_of_theorem |> Sexplib.Sexp.to_string
let string_of_tactic t = t |> sexp_of_tactic |> Sexplib.Sexp.to_string
let string_of_prop p = p |> sexp_of_prop |> Sexplib.Sexp.to_string
let string_of_expr e = e |> sexp_of_expr |> Sexplib.Sexp.to_string
let pp_expr = Ir.pp_expr

let rec pp_prop prop =
  match prop with
  | Eq (e1, e2) -> pp_expr e1 ^ " = " ^ pp_expr e2
  | Le (e1, e2) -> pp_expr e1 ^ " <= " ^ pp_expr e2
  | Lt (e1, e2) -> pp_expr e1 ^ " < " ^ pp_expr e2
  | And (p1, p2) -> pp_prop p1 ^ " /\\ " ^ pp_prop p2
  | Or (p1, p2) -> pp_prop p1 ^ " \\/ " ^ pp_prop p2
  | Not p -> "not " ^ pp_prop p
  | Forall (name, p) -> "forall " ^ name ^ ". " ^ pp_prop p
  | Imply (p1, p2) -> pp_prop p1 ^ " -> " ^ pp_prop p2
  | Type (name, typ) -> name ^ " : " ^ typ
;;

let pp_tactic tactic =
  match tactic with
  | ApplyInAt (fact, goal, i) ->
    "apply " ^ fact ^ " in " ^ goal ^ " at " ^ string_of_int i
  | Intro name -> "intro " ^ name
  | RewriteInAt (fact, goal, i) ->
    "rewrite " ^ fact ^ " in " ^ goal ^ " at " ^ string_of_int i
  | Induction name -> "induction " ^ name
  | Case name -> "case " ^ name
  | SimplInAt (fact, goal, i) ->
    "simpl " ^ fact ^ " in " ^ goal ^ " at " ^ string_of_int i
  | Reflexivity -> "reflexivity"
;;

let pp_theorem (tactics, goal) =
  (List.map pp_tactic tactics |> String.concat "\n") ^ "\n" ^ pp_prop goal
;;

let pp_t (t : t) =
  List.map
    (fun (facts, goal) ->
       (List.map pp_prop facts |> String.concat "\n")
       ^ "\n---------------------------------------\n"
       ^ pp_prop goal)
    t
  |> String.concat "\n\n"
;;

let mk_proof program_a program_b func_name =
  (* dummy *)
  ignore program_a;
  ignore program_b;
  let goal =
    Forall
      ( "n1"
      , Forall
          ( "n2"
          , Eq
              ( Ir.Call (func_name ^ "_ta1", [ Ir.Var "n1"; Ir.Var "n2" ])
              , Ir.Call (func_name ^ "_ta2", [ Ir.Var "n1"; Ir.Var "n2" ]) ) ) )
  in
  List.fold_left
    (fun t tactic -> apply_tactic t [] tactic)
    [ [], goal ]
    [ Intro "n1"; Intro "n2" ]
  |> pp_t
  |> print_endline
;;
