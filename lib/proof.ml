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

let substitute_expr_in_expr pred convert target expr_from expr_to i =
  Ir.substitute_expr pred convert target expr_from expr_to i
;;

let substitute_expr_in_prop pred convert target expr_from expr_to i =
  let rec substitute_expr_in_prop' pred convert target expr_from expr_to i =
    match target with
    | Eq (e1, e2) ->
      let lhs, cnt = substitute_expr_in_expr pred convert e1 expr_from expr_to i in
      let rhs, cnt =
        substitute_expr_in_expr
          pred
          convert
          e2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
      in
      Eq (lhs, rhs), cnt
    | Le (e1, e2) ->
      let lhs, cnt = substitute_expr_in_expr pred convert e1 expr_from expr_to i in
      let rhs, cnt =
        substitute_expr_in_expr
          pred
          convert
          e2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
      in
      Le (lhs, rhs), cnt
    | Lt (e1, e2) ->
      let lhs, cnt = substitute_expr_in_expr pred convert e1 expr_from expr_to i in
      let rhs, cnt =
        substitute_expr_in_expr
          pred
          convert
          e2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
      in
      Lt (lhs, rhs), cnt
    | And (p1, p2) ->
      let p1, cnt = substitute_expr_in_prop' pred convert p1 expr_from expr_to i in
      let p2, cnt =
        substitute_expr_in_prop'
          pred
          convert
          p2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
      in
      And (p1, p2), cnt
    | Or (p1, p2) ->
      let p1, cnt = substitute_expr_in_prop' pred convert p1 expr_from expr_to i in
      let p2, cnt =
        substitute_expr_in_prop'
          pred
          convert
          p2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
      in
      Or (p1, p2), cnt
    | Not p ->
      let p, cnt = substitute_expr_in_prop' pred convert p expr_from expr_to i in
      Not p, cnt
    | Forall (var_list, p) ->
      let p, cnt = substitute_expr_in_prop' pred convert p expr_from expr_to i in
      Forall (var_list, p), cnt
    | Imply (p1, p2) ->
      let p1, cnt = substitute_expr_in_prop' pred convert p1 expr_from expr_to i in
      let p2, cnt =
        substitute_expr_in_prop'
          pred
          convert
          p2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
      in
      Imply (p1, p2), cnt
    | Type typ -> Type typ, i
  in
  substitute_expr_in_prop' pred convert target expr_from expr_to i |> fst
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
               Ir.Call
                 ( constr
                 , List.map
                     (fun arg ->
                        { Ir.desc = Ir.Var (arg ^ "_"); Ir.typ = Ir.typ_of_string arg })
                     arg_types )
           in
           let new_facts =
             [ ( "asdf"
               , Eq
                   ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                   , Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name } ) )
             ]
           in
           let new_goal =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to)
               goal
               Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
               Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
               0
           in
           let facts =
             List.map
               (fun (name, prop) ->
                  ( name
                  , substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to)
                      prop
                      Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                      Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
                      0 ))
               facts
           in
           facts @ new_facts, new_goal
         | _ ->
           let inductive_case =
             match constr with
             | Ir.Constructor constr ->
               Ir.Call
                 ( constr
                 , List.map
                     (fun arg ->
                        Ir.{ desc = Var (arg ^ "_"); typ = Ir.typ_of_string arg })
                     arg_types )
             (* need to be generate free variable *)
           in
           let ihs =
             List.map
               (fun arg ->
                  ( "IH"
                  , substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to)
                      goal
                      Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                      Ir.{ desc = Var (arg ^ "_"); typ = Ir.typ_of_string typ_name }
                      0 ))
               (* need to be substitue to above variable *)
               rec_args
           in
           let new_facts =
             ihs
             @ [ ( "asdf"
                 , Eq
                     ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                     , Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name } ) )
               ]
           in
           let new_goal =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to)
               goal
               Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
               Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
               0
           in
           let facts =
             List.map
               (fun (name, prop) ->
                  ( name
                  , substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to)
                      prop
                      Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                      Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
                      0 ))
               facts
           in
           facts @ new_facts, new_goal)
      decl
  | _ -> failwith "not implemented"
;;

let apply_strong_induction env name facts goal =
  ignore env;
  ignore name;
  ignore facts;
  ignore goal;
  failwith "Not implemented"
;;

let rec forall_target var_list target source =
  match source.Ir.desc with
  | Ir.Var var ->
    let lhs_typ = source.Ir.typ in
    if List.mem_assoc var var_list
    then (
      let target_typ = target.Ir.typ in
      lhs_typ = target_typ)
    else Ir.is_equal_expr source target
  | Ir.Call (name, args) ->
    (match target.Ir.desc with
     | Ir.Call (name', args') ->
       name = name' && List.for_all2 (fun a b -> forall_target var_list a b) args args'
     | _ -> false)
  | Ir.Match (e, cases) ->
    (match target.Ir.desc with
     | Ir.Match (e', cases') ->
       forall_target var_list e e'
       && List.for_all2
            (fun a b ->
               match a, b with
               | Ir.Case (_, e1), Ir.Case (_, e2) -> forall_target var_list e1 e2)
               (* have to think pattern order.... or compatiblity *)
            cases
            cases'
     | _ -> false)
  | Ir.LetIn (let_list, e) ->
    let new_expr =
      List.fold_left
        (fun e (name, e') ->
           substitute_expr_in_expr
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to)
             e
             Ir.{ desc = Var name; typ = e'.typ }
             e'
             0
           |> fst)
        e
        let_list
    in
    forall_target var_list new_expr target
  | Ir.IfthenElse (e1, e2, e3) ->
    (match target.Ir.desc with
     | Ir.IfthenElse (e1', e2', e3') ->
       forall_target var_list e1 e1'
       && forall_target var_list e2 e2'
       && forall_target var_list e3 e3'
     | _ -> false)
  | _ -> false
;;

let convert_in_rewrite target expr_from expr_to =
  match expr_from.Ir.desc with
  | Ir.Var _ -> expr_to
  (* we have to check variable in expr_to exsists in target *)
  | Ir.Call (name, args) ->
    (match target.Ir.desc with
     | Ir.Call (name', args') ->
       if name = name'
       then (
         let args = List.map2 (fun a b -> a, b) args args' in
         List.fold_left
           (fun expr_to (arg, arg') ->
              substitute_expr_in_expr
                Ir.is_equal_expr
                (fun _ _ expr_to -> expr_to)
                expr_to
                arg
                arg'
                0
              |> fst)
           expr_to
           args)
       else failwith "The function name is not equal"
     | _ -> failwith "Not rewritable")
  | _ -> failwith "The source is not a variable"
;;

let apply_rewrite (facts : fact list) (goal : goal) fact_label target_label i =
  let source = List.assoc fact_label facts in
  let var_list, expr_from, expr_to =
    match source with
    | Eq (lhs, rhs) -> [], lhs, rhs
    | Forall (var_list, Eq (lhs, rhs)) -> var_list, lhs, rhs
    | _ -> failwith "Not rewritable"
  in
  match target_label with
  | "goal" ->
    let new_goal =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        goal
        expr_from
        expr_to
        i
    in
    [ facts, new_goal ]
  | _ ->
    let target_fact = List.assoc target_label facts in
    let new_fact =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        target_fact
        expr_from
        expr_to
        i
    in
    let new_facts =
      List.map
        (fun (name, prop) -> if name = target_label then name, new_fact else name, prop)
        facts
    in
    [ new_facts, goal ]
;;

let apply_rewrite_reverse facts goal fact_label target_label i =
  let source = List.assoc fact_label facts in
  let var_list, expr_from, expr_to =
    match source with
    | Eq (lhs, rhs) -> [], rhs, lhs
    | Forall (var_list, Eq (lhs, rhs)) -> var_list, rhs, lhs
    | _ -> failwith "Not rewritable"
  in
  match target_label with
  | "goal" ->
    let new_goal =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        goal
        expr_from
        expr_to
        i
    in
    [ facts, new_goal ]
  | _ ->
    let target_fact = List.assoc target_label facts in
    let new_fact =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        target_fact
        expr_from
        expr_to
        i
    in
    let new_facts =
      List.map
        (fun (name, prop) -> if name = target_label then name, new_fact else name, prop)
        facts
    in
    [ new_facts, goal ]
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
  | RewriteInAt (fact, target_label, i) ->
    apply_rewrite facts goal fact target_label i @ List.tl t
  | RewriteReverse (fact, target_label, i) ->
    apply_rewrite_reverse facts goal fact target_label i @ List.tl t
  | Induction name -> apply_induction env name facts goal @ List.tl t
  | StrongInduction name -> apply_strong_induction env name facts goal @ List.tl t
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
    ^ "."
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
  let facts =
    [ ( "H1"
      , Forall
          ( [ "n1", Type "nat" ]
          , Eq
              ( Ir.
                  { desc =
                      Call
                        ( "natadd"
                        , [ { desc = Var "n1"; typ = Ir.typ_of_string "nat" }
                          ; { desc = Var "n"; typ = Ir.typ_of_string "nat" }
                          ] )
                  ; typ = Ir.typ_of_string "nat"
                  }
              , Ir.
                  { desc =
                      Call
                        ( "natadd"
                        , [ { desc = Var "n"; typ = Ir.typ_of_string "nat" }
                          ; { desc = Var "n1"; typ = Ir.typ_of_string "nat" }
                          ] )
                  ; typ = Ir.typ_of_string "nat"
                  } ) ) )
    ]
  in
  let goal =
    Eq
      ( Ir.
          { desc =
              Call
                ( "natadd"
                , [ { desc =
                        Call ("SUCC", [ { desc = Var "n"; typ = Ir.typ_of_string "nat" } ])
                    ; typ = Ir.typ_of_string "nat"
                    }
                  ; { desc = Var "n"; typ = Ir.typ_of_string "nat" }
                  ] )
          ; typ = Ir.typ_of_string "nat"
          }
      , Ir.
          { desc =
              Call
                ( "natadd"
                , [ { desc = Var "n"; typ = Ir.typ_of_string "nat" }
                  ; { desc =
                        Call ("SUCC", [ { desc = Var "n"; typ = Ir.typ_of_string "nat" } ])
                    ; typ = Ir.typ_of_string "nat"
                    }
                  ] )
          ; typ = Ir.typ_of_string "nat"
          } )
  in
  List.fold_left
    (fun t tactic -> apply_tactic t env tactic)
    [ facts, goal ]
    [ RewriteInAt ("H1", "goal", 0) ]
  |> pp_t
  |> print_endline
;;
