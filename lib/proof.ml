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
  | Forall of (string * prop) list * prop
  | Imply of prop * prop
  | Type of string
[@@deriving sexp]

and expr = Ir.expr [@@deriving sexp]

type theorem = tactic list * goal [@@deriving sexp]

and tactic =
  | Intro of string
  | RewriteInAt of string * string * int
  | RewriteReverse of string * string * int
  | Induction of string
  | StrongInduction of string
  | Case of string
  | SimplInAt of string * string * int
  | Reflexivity
[@@deriving sexp]

type env = Ir.t [@@deriving sexp]

let range start stop =
  let rec range' i acc = if i = stop then acc else range' (i + 1) (i :: acc) in
  range' start []
;;

let substitute_expr_in_expr target var_from var_to i =
  Ir.substitute_expr Ir.is_equal_expr target var_from var_to i
;;

let substitute_expr_in_prop target var_from var_to i =
  let rec substitute_expr_in_prop' target var_from var_to i =
    match target with
    | Eq (e1, e2) ->
      let lhs, cnt = substitute_expr_in_expr e1 var_from var_to i in
      let rhs, cnt =
        substitute_expr_in_expr e2 var_from var_to (if i = 0 then 0 else cnt)
      in
      Eq (lhs, rhs), cnt
    | Le (e1, e2) ->
      let lhs, cnt = substitute_expr_in_expr e1 var_from var_to i in
      let rhs, cnt =
        substitute_expr_in_expr e2 var_from var_to (if i = 0 then 0 else cnt)
      in
      Le (lhs, rhs), cnt
    | Lt (e1, e2) ->
      let lhs, cnt = substitute_expr_in_expr e1 var_from var_to i in
      let rhs, cnt =
        substitute_expr_in_expr e2 var_from var_to (if i = 0 then 0 else cnt)
      in
      Lt (lhs, rhs), cnt
    | And (p1, p2) ->
      let p1, cnt = substitute_expr_in_prop' p1 var_from var_to i in
      let p2, cnt =
        substitute_expr_in_prop' p2 var_from var_to (if i = 0 then 0 else cnt)
      in
      And (p1, p2), cnt
    | Or (p1, p2) ->
      let p1, cnt = substitute_expr_in_prop' p1 var_from var_to i in
      let p2, cnt =
        substitute_expr_in_prop' p2 var_from var_to (if i = 0 then 0 else cnt)
      in
      Or (p1, p2), cnt
    | Not p ->
      let p, cnt = substitute_expr_in_prop' p var_from var_to i in
      Not p, cnt
    | Forall (var_list, p) ->
      let p, cnt = substitute_expr_in_prop' p var_from var_to i in
      Forall (var_list, p), cnt
    | Imply (p1, p2) ->
      let p1, cnt = substitute_expr_in_prop' p1 var_from var_to i in
      let p2, cnt =
        substitute_expr_in_prop' p2 var_from var_to (if i = 0 then 0 else cnt)
      in
      Imply (p1, p2), cnt
    | Type typ -> Type typ, i
  in
  substitute_expr_in_prop' target var_from var_to i |> fst
;;

let apply_intro name facts goal =
  match goal with
  | Forall (var_list, goal) ->
    let typ =
      try List.assoc name var_list with
      | _ -> failwith "there is no such variable"
    in
    let var_list = List.filter (fun (name', _) -> name' <> name) var_list in
    facts @ [ name, typ ], Forall (var_list, goal)
  | Imply (p1, p2) -> facts @ [ name, p1 ], p2
  | _ -> failwith "There is no term that can be introduced"
;;

let rec apply_eq goal =
  match goal with
  | Eq (e1, e2) -> if e1 = e2 then [] else failwith "LHS and RHS are not equal"
  | Forall (_, goal) -> apply_eq goal
  | _ -> failwith "The goal is not an equality"
;;

let apply_induction env name facts goal : t =
  match goal with
  | Forall (var_list, goal) ->
    let typ =
      try List.assoc name var_list with
      | _ -> failwith "there is no such variable"
    in
    let typ_name =
      match typ with
      | Type typ -> typ
      | _ -> failwith "not implemented"
    in
    let decl =
      try Ir.find_decl typ_name env |> Ir.get_typ_decl with
      | _ -> failwith "There is no such type"
    in
    List.map
      (fun (constr, arg_types) ->
         let rec_args = List.filter (fun arg -> arg = typ_name) arg_types in
         match rec_args with
         | [] ->
           let base_case =
             match constr with
             | Ir.Constructor constr ->
               Ir.Call (constr, List.map (fun arg -> Ir.Var (arg ^ "_")) arg_types)
           in
           let new_facts = [ "asdf", Eq (Var name, base_case) ] in
           let new_goal = substitute_expr_in_prop goal (Var name) base_case 0 in
           let facts =
             List.map
               (fun (name, prop) ->
                  name, substitute_expr_in_prop prop (Var name) base_case 0)
               facts
           in
           facts @ new_facts, new_goal
         | _ ->
           let inductive_case =
             match constr with
             | Ir.Constructor constr ->
               Ir.Call (constr, List.map (fun arg -> Ir.Var (arg ^ "_")) arg_types)
             (* need to be generate free variable *)
           in
           let ihs =
             List.map
               (fun arg ->
                  "IH", substitute_expr_in_prop goal (Var name) (Var (arg ^ "_")) 0)
               (* need to be substitue to above variable *)
               rec_args
           in
           let new_facts = ihs @ [ "asdf", Eq (Var name, inductive_case) ] in
           let new_goal = substitute_expr_in_prop goal (Var name) inductive_case 0 in
           let facts =
             List.map
               (fun (name, prop) ->
                  name, substitute_expr_in_prop prop (Var name) inductive_case 0)
               facts
           in
           facts @ new_facts, new_goal)
      decl
  | _ -> failwith "not implemented"
;;

let apply_rewrite facts goal fact target i =
  ignore facts;
  ignore goal;
  ignore fact;
  ignore target;
  ignore i;
  failwith "Not implemented"
;;

let apply_rewrite_reverse facts goal fact target i =
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

let apply_simpl env facts goal fact target i =
  ignore env;
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
  | RewriteReverse (fact, target, i) ->
    apply_rewrite_reverse facts goal fact target i @ List.tl t
  | Induction name -> apply_induction env name facts goal @ List.tl t
  | StrongInduction _ -> failwith "Not implemented"
  | Case name -> apply_case name facts goal @ List.tl t
  | SimplInAt (fact, target, i) -> apply_simpl env facts goal fact target i :: List.tl t
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
  | Forall (var_list, p) ->
    "forall "
    ^ (List.map (fun (name, typ) -> name ^ ":" ^ pp_prop typ) var_list
       |> String.concat ". ")
    ^ pp_prop p
  | Imply (p1, p2) -> pp_prop p1 ^ " -> " ^ pp_prop p2
  | Type typ -> typ
;;

let pp_fact (name, prop) = name ^ " : " ^ pp_prop prop

let pp_tactic tactic =
  match tactic with
  | Intro name -> "intro " ^ name
  | RewriteInAt (fact, goal, i) ->
    "rewrite " ^ fact ^ " in " ^ goal ^ " at " ^ string_of_int i
  | RewriteReverse (fact, goal, i) ->
    "rewrite <-" ^ fact ^ " in " ^ goal ^ " at " ^ string_of_int i
  | Induction name -> "induction " ^ name
  | StrongInduction name -> "strong induction " ^ name
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
  let goal =
    Forall
      ( [ "x", Type "nat" ]
      , Forall ([ "y", Type "nat" ], Eq (Call ("natadd", [ Var "x"; Var "x" ]), Var "x"))
      )
  in
  List.fold_left
    (fun t tactic -> apply_tactic t env tactic)
    [ [], goal ]
    [ Induction "x" ]
  |> pp_t
  |> print_endline
;;
