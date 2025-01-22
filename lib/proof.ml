open Sexplib.Std

type t = (fact list * goal) list [@@deriving sexp]
and fact = string * prop [@@deriving sexp]
and goal = prop [@@deriving sexp]

and prop =
  | Eq of expr * expr
  | Le of expr * expr
  | Lt of expr * expr
  | And of prop * prop
  | Or of prop * prop
  | Not of prop
  | Forall of string * prop * prop
  | Imply of prop * prop
  | Type of string
[@@deriving sexp]

and expr = Ir.expr [@@deriving sexp]

type theorem = tactic list * goal [@@deriving sexp]

and tactic =
  | Intro of string
  | RewriteInAt of string * string * int
  | Induction of string
  | Case of string
  | SimplInAt of string * string * int
  | Reflexivity
[@@deriving sexp]

type env = Ir.t [@@deriving sexp]

let apply_intro name facts goal =
  let rec search_qvar name goal : goal =
    match goal with
    | Forall (var, typ, goal') ->
      if var = name then goal' else Forall (var, typ, search_qvar name goal')
    | _ -> failwith "There is no such universal variable in goal"
  in
  match goal with
  | Forall (var, typ, goal) ->
    if var = name
    then facts @ [ name, typ ], goal
    else facts @ [ name, typ ], Forall (var, typ, search_qvar name goal)
  | Imply (p1, p2) -> facts @ [ name, p1 ], p2
  | _ -> failwith "There is no term that can be introduced"
;;

let apply_eq goal =
  let rec peel_forall goal =
    match goal with
    | Forall (_, _, goal') -> peel_forall goal'
    | Eq (e1, e2) -> if e1 = e2 then [] else failwith "LHS and RHS are not equal"
    | _ -> failwith "The goal is not an equality"
  in
  match goal with
  | Eq (e1, e2) -> if e1 = e2 then [] else failwith "LHS and RHS are not equal"
  | Forall (_, _, goal) -> peel_forall goal
  | _ -> failwith "The goal is not an equality"
;;

let apply_induction name facts goal =
  ignore name;
  ignore facts;
  ignore goal;
  failwith "Not implemented"
;;

let apply_rewrite facts goal fact target i =
  ignore facts;
  ignore goal;
  ignore fact;
  ignore target;
  ignore i;
  failwith "Not implemented"
;;

let apply_case name facts goal =
  ignore name;
  ignore facts;
  ignore goal;
  failwith "Not implemented"
;;

let apply_simpl facts goal fact target i =
  ignore facts;
  ignore goal;
  ignore fact;
  ignore target;
  ignore i;
  failwith "Not implemented"
;;

let apply_tactic t env tactic : t =
  ignore env;
  let facts, goal = List.hd t in
  match tactic with
  | Intro name -> apply_intro name facts goal :: List.tl t
  | RewriteInAt (fact, target, i) -> apply_rewrite facts goal fact target i @ List.tl t
  | Induction name -> apply_induction name facts goal @ List.tl t
  | Case name -> apply_case name facts goal @ List.tl t
  | SimplInAt (fact, target, i) -> apply_simpl facts goal fact target i :: List.tl t
  | Reflexivity -> apply_eq goal @ List.tl t
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
  | Forall (name, typ, p) -> "forall " ^ name ^ ":" ^ pp_prop typ ^ ". " ^ pp_prop p
  | Imply (p1, p2) -> pp_prop p1 ^ " -> " ^ pp_prop p2
  | Type typ -> typ
;;

let pp_fact (name, prop) = name ^ " : " ^ pp_prop prop

let pp_tactic tactic =
  match tactic with
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
       (List.map pp_fact facts |> String.concat "\n")
       ^ "\n---------------------------------------\n"
       ^ pp_prop goal)
    t
  |> String.concat "\n\n"
;;

let mk_proof program_a program_b func_name =
  (* dummy *)
  let env = program_a @ program_b in
  ignore func_name;
  ignore program_a;
  ignore program_b;
  let goal = Forall ("x", Type "nat", Forall ("y", Type "nat", Eq (Var "x", Var "x"))) in
  List.fold_left (fun t tactic -> apply_tactic t env tactic) [ [], goal ] [ Reflexivity ]
  |> pp_t
  |> print_endline
;;
