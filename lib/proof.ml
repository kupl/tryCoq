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
  | Imply of prop list * prop
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
  | Destruct of string
  | Case of expr
  | SimplIn of string
  | Reflexivity
  | Assert of prop
[@@deriving sexp]

type env = Ir.t [@@deriving sexp]

let range start stop =
  let rec range' i acc = if i = stop then acc else range' (i + 1) (acc @ [ i ]) in
  range' start []
;;

let make_counter () =
  let count = ref 0 in
  fun () ->
    incr count;
    !count
;;

let counter = make_counter ()
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
    ^ ". "
    ^ pp_prop p
  | Imply (cond_list, p2) ->
    (List.map (fun cond -> pp_prop cond) cond_list |> String.concat "->")
    ^ " -> "
    ^ pp_prop p2
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
  | Destruct name -> "destruct " ^ name
  | Case expr -> "case " ^ Ir.pp_expr expr
  | SimplIn target -> "simpl in " ^ target
  | Reflexivity -> "reflexivity"
  | Assert prop -> "assert " ^ pp_prop prop
;;

let pp_theorem (tactics, goal) =
  (List.map pp_tactic tactics |> String.concat "\n") ^ "\n" ^ pp_prop goal
;;

let pp_t (t : t) =
  List.map
    (fun ((facts, goal), i) ->
       "goal"
       ^ string_of_int (i + 1)
       ^ "\n"
       ^ (List.map pp_fact facts |> String.concat "\n")
       ^ "\n---------------------------------------\n"
       ^ pp_prop goal)
    (List.combine t (range 0 (List.length t)))
  |> String.concat "\n\n"
;;

let partition_and_transform (pred : 'a -> bool) (transform : 'a -> 'b) (lst : 'a list)
  : 'b list * 'b list
  =
  let rec aux acc1 acc2 = function
    | [] -> List.rev acc1, List.rev acc2
    | x :: xs ->
      let transformed = transform x in
      if pred x
      then aux (transformed :: acc1) (transformed :: acc2) xs
      else aux (transformed :: acc1) acc2 xs
  in
  aux [] [] lst
;;

let substitute_expr_in_expr pred convert target expr_from expr_to i result =
  Ir.substitute_expr pred convert target expr_from expr_to i result
;;

let substitute_expr_in_prop pred convert target expr_from expr_to i =
  let rec substitute_expr_in_prop' pred convert target expr_from expr_to i result =
    match target with
    | Eq (e1, e2) ->
      let lhs, result, cnt =
        substitute_expr_in_expr pred convert e1 expr_from expr_to i result
      in
      let rhs, result, cnt =
        substitute_expr_in_expr
          pred
          convert
          e2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
          result
      in
      Eq (lhs, rhs), result, cnt
    | Le (e1, e2) ->
      let lhs, result, cnt =
        substitute_expr_in_expr pred convert e1 expr_from expr_to i result
      in
      let rhs, result, cnt =
        substitute_expr_in_expr
          pred
          convert
          e2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
          result
      in
      Le (lhs, rhs), result, cnt
    | Lt (e1, e2) ->
      let lhs, result, cnt =
        substitute_expr_in_expr pred convert e1 expr_from expr_to i result
      in
      let rhs, result, cnt =
        substitute_expr_in_expr
          pred
          convert
          e2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
          result
      in
      Lt (lhs, rhs), result, cnt
    | And (p1, p2) ->
      let p1, result, cnt =
        substitute_expr_in_prop' pred convert p1 expr_from expr_to i result
      in
      let p2, result, cnt =
        substitute_expr_in_prop'
          pred
          convert
          p2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
          result
      in
      And (p1, p2), result, cnt
    | Or (p1, p2) ->
      let p1, result, cnt =
        substitute_expr_in_prop' pred convert p1 expr_from expr_to i result
      in
      let p2, result, cnt =
        substitute_expr_in_prop'
          pred
          convert
          p2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
          result
      in
      Or (p1, p2), result, cnt
    | Not p ->
      let p, result, cnt =
        substitute_expr_in_prop' pred convert p expr_from expr_to i result
      in
      Not p, result, cnt
    | Forall (var_list, p) ->
      let p, result, cnt =
        substitute_expr_in_prop' pred convert p expr_from expr_to i result
      in
      Forall (var_list, p), result, cnt
    | Imply (cond_list, p2) ->
      let cond_list, result, cnt =
        List.fold_left
          (fun (cond_list, result, cnt) cond ->
             let cond, result, cnt =
               substitute_expr_in_prop' pred convert cond expr_from expr_to cnt result
             in
             cond_list @ [ cond ], result, cnt)
          ([], result, i)
          cond_list
      in
      let p2, result, cnt =
        substitute_expr_in_prop'
          pred
          convert
          p2
          expr_from
          expr_to
          (if i = 0 then 0 else cnt)
          result
      in
      Imply (cond_list, p2), result, cnt
    | Type typ -> Type typ, result, i
  in
  substitute_expr_in_prop' pred convert target expr_from expr_to i []
;;

let apply_intro name facts goal =
  match goal with
  | Forall (var_list, goal) ->
    let typ =
      try List.assoc name var_list with
      | _ -> failwith "there is no such variable"
    in
    let var_list = List.filter (fun (name', _) -> name' <> name) var_list in
    let new_goal = if List.is_empty var_list then goal else Forall (var_list, goal) in
    facts @ [ name, typ ], new_goal
  | Imply (cond_list, p2) ->
    facts @ [ name, List.hd cond_list ], Imply (List.tl cond_list, p2)
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
    let var_list = List.filter (fun (name', _) -> name' <> name) var_list in
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
                        { Ir.desc = Ir.Var (arg ^ string_of_int (counter ()))
                        ; Ir.typ = Ir.typ_of_string arg
                        })
                     arg_types )
           in
           let new_facts =
             [ ( "Base" ^ string_of_int (counter ())
               , Eq
                   ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                   , Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name } ) )
             ]
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
               Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
               0
           in
           let new_goal =
             if List.is_empty var_list then new_goal else Forall (var_list, new_goal)
           in
           let facts =
             List.map
               (fun (name, prop) ->
                  ( name
                  , let prop, _, _ =
                      substitute_expr_in_prop
                        Ir.is_equal_expr
                        (fun _ _ expr_to -> expr_to, [])
                        prop
                        Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                        Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
                        0
                    in
                    prop ))
               facts
           in
           facts @ new_facts, new_goal
         | _ ->
           let new_args, new_rec_args =
             partition_and_transform
               (fun arg -> List.mem arg rec_args)
               (fun arg ->
                  Ir.
                    { desc = Var (arg ^ string_of_int (counter ()))
                    ; typ = Ir.typ_of_string arg
                    })
               arg_types
           in
           let inductive_case =
             match constr with
             | Ir.Constructor constr -> Ir.Call (constr, new_args)
           in
           let ihs =
             List.map
               (fun arg ->
                  ( "IH" ^ string_of_int (counter ())
                  , let prop, _, _ =
                      substitute_expr_in_prop
                        Ir.is_equal_expr
                        (fun _ _ expr_to -> expr_to, [])
                        goal
                        Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                        arg
                        0
                    in
                    if List.is_empty var_list then prop else Forall (var_list, prop) ))
               new_rec_args
           in
           let new_facts =
             ihs
             @ [ ( "Inductive" ^ string_of_int (counter ())
                 , Eq
                     ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                     , Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name } ) )
               ]
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
               Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
               0
           in
           let new_goal =
             if List.is_empty var_list then new_goal else Forall (var_list, new_goal)
           in
           let facts =
             List.map
               (fun (name, prop) ->
                  ( name
                  , let prop, _, _ =
                      substitute_expr_in_prop
                        Ir.is_equal_expr
                        (fun _ _ expr_to -> expr_to, [])
                        prop
                        Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                        Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
                        0
                    in
                    prop ))
               facts
           in
           facts @ new_facts, new_goal)
      decl
  | _ -> failwith "not implemented"
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
       name = name' && List.for_all2 (fun a b -> forall_target var_list a b) args' args
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
            cases'
            cases
     | _ -> false)
  | Ir.LetIn (let_list, e) ->
    let new_expr =
      List.fold_left
        (fun e (name, e') ->
           let exp, _, _ =
             substitute_expr_in_expr
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               e
               Ir.{ desc = Var name; typ = e'.typ }
               e'
               0
               []
           in
           exp)
        e
        let_list
    in
    forall_target var_list target new_expr
  | Ir.IfthenElse (e1, e2, e3) ->
    (match target.Ir.desc with
     | Ir.IfthenElse (e1', e2', e3') ->
       forall_target var_list e1' e1
       && forall_target var_list e2' e2
       && forall_target var_list e3' e3
     | _ -> false)
  | _ -> false
;;

let convert_in_rewrite target expr_from expr_to =
  match expr_from.Ir.desc with
  | Ir.Var _ -> expr_to, [ expr_from, expr_to ]
  | Ir.Call (name, args) ->
    (match target.Ir.desc with
     | Ir.Call (name', args') ->
       if name = name'
       then (
         let args = List.combine args args' in
         ( List.fold_left
             (fun expr_to (arg, arg') ->
                let exp, _, _ =
                  substitute_expr_in_expr
                    Ir.is_equal_expr
                    (fun _ _ expr_to -> expr_to, [])
                    expr_to
                    arg
                    arg'
                    0
                    []
                in
                exp)
             expr_to
             args
         , args ))
       else failwith "The function name is not equal"
     | _ -> failwith "Not rewritable")
  | _ -> failwith "The source is not a variable"
;;

let apply_rewrite (facts : fact list) (goal : goal) fact_label target_label i =
  let source = List.assoc fact_label facts in
  let cond_list, var_list, expr_from, expr_to =
    match source with
    | Eq (lhs, rhs) -> [], [], lhs, rhs
    | Forall (var_list, Eq (lhs, rhs)) -> [], var_list, lhs, rhs
    | Imply (cond_list, Eq (lhs, rhs)) -> cond_list, [], lhs, rhs
    | Forall (var_list, Imply (cond_list, Eq (lhs, rhs))) -> cond_list, var_list, lhs, rhs
    | _ -> failwith "Not rewritable"
  in
  match target_label with
  | "goal" ->
    let new_goal, match_list, _ =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        goal
        expr_from
        expr_to
        i
    in
    if
      not
        (List.for_all
           (fun (e1, _) ->
              List.exists
                (fun (e2, _) ->
                   match e2.Ir.desc with
                   | Var var -> e1 = var
                   | _ -> failwith "not implemented")
                match_list)
           var_list)
    then failwith "Cannot find matched variable"
    else (
      let new_task =
        List.map
          (fun cond ->
             List.fold_left
               (fun cond (e1, e2) ->
                  let prop, _, _ =
                    substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to, [])
                      cond
                      e1
                      e2
                      0
                  in
                  prop)
               cond
               match_list)
          cond_list
      in
      [ facts, new_goal ] @ List.map (fun goal -> facts, goal) new_task)
  | _ ->
    let target_fact = List.assoc target_label facts in
    let new_fact, match_list, _ =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        target_fact
        expr_from
        expr_to
        i
    in
    let fact =
      List.map
        (fun (name, prop) -> if name = target_label then name, new_fact else name, prop)
        facts
    in
    let new_task =
      List.map
        (fun cond ->
           List.fold_left
             (fun cond (e1, e2) ->
                let prop, _, _ =
                  substitute_expr_in_prop
                    Ir.is_equal_expr
                    (fun _ _ expr_to -> expr_to, [])
                    cond
                    e1
                    e2
                    0
                in
                prop)
             cond
             match_list)
        cond_list
    in
    [ fact, goal ] @ List.map (fun goal -> facts, goal) new_task
;;

let apply_rewrite_reverse facts goal fact_label target_label i =
  let source = List.assoc fact_label facts in
  let cond_list, var_list, expr_from, expr_to =
    match source with
    | Eq (lhs, rhs) -> [], [], rhs, lhs
    | Forall (var_list, Eq (lhs, rhs)) -> [], var_list, rhs, lhs
    | Imply (cond_list, Eq (lhs, rhs)) -> cond_list, [], rhs, lhs
    | Forall (var_list, Imply (cond_list, Eq (lhs, rhs))) -> cond_list, var_list, rhs, lhs
    | _ -> failwith "Not rewritable"
  in
  match target_label with
  | "goal" ->
    let new_goal, match_list, _ =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        goal
        expr_from
        expr_to
        i
    in
    let new_facts =
      List.map
        (fun cond ->
           ( "Cond" ^ string_of_int (counter ())
           , List.fold_left
               (fun cond (e1, e2) ->
                  let prop, _, _ =
                    substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to, [])
                      cond
                      e1
                      e2
                      0
                  in
                  prop)
               cond
               match_list ))
        cond_list
    in
    let _ = cond_list in
    [ facts @ new_facts, new_goal ]
  | _ ->
    let target_fact = List.assoc target_label facts in
    let new_fact, match_list, _ =
      substitute_expr_in_prop
        (forall_target var_list)
        convert_in_rewrite
        target_fact
        expr_from
        expr_to
        i
    in
    let fact =
      List.map
        (fun (name, prop) -> if name = target_label then name, new_fact else name, prop)
        facts
    in
    let new_facts =
      List.map
        (fun cond ->
           ( "Cond" ^ string_of_int (counter ())
           , List.fold_left
               (fun cond (e1, e2) ->
                  let prop, _, _ =
                    substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to, [])
                      cond
                      e1
                      e2
                      0
                  in
                  prop)
               cond
               match_list ))
        cond_list
    in
    [ fact @ new_facts, goal ]
;;

let apply_case expr facts goal =
  match expr.Ir.typ with
  | Tbool ->
    let new_fact1 =
      "case" ^ string_of_int (counter ()), Eq (expr, Ir.{ desc = Bool true; typ = Tbool })
    in
    let new_fact2 =
      "case" ^ string_of_int (counter ()), Eq (expr, Ir.{ desc = Bool false; typ = Tbool })
    in
    let new_goal1, _, _ =
      substitute_expr_in_prop
        Ir.is_equal_expr
        (fun _ _ expr_to -> expr_to, [])
        goal
        expr
        Ir.{ desc = Bool true; typ = Tbool }
        0
    in
    let new_goal2, _, _ =
      substitute_expr_in_prop
        Ir.is_equal_expr
        (fun _ _ expr_to -> expr_to, [])
        goal
        expr
        Ir.{ desc = Bool false; typ = Tbool }
        0
    in
    [ facts @ [ new_fact1 ], new_goal1; facts @ [ new_fact2 ], new_goal2 ]
  | _ -> failwith "This expression is not bool type"
;;

let apply_strong_induction env name facts goal =
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
                        { Ir.desc = Ir.Var (arg ^ string_of_int (counter ()))
                        ; Ir.typ = Ir.typ_of_string arg
                        })
                     arg_types )
           in
           let new_facts =
             [ ( "Base" ^ string_of_int (counter ())
               , Eq
                   ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                   , Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name } ) )
             ]
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
               Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
               0
           in
           let facts =
             List.map
               (fun (name, prop) ->
                  ( name
                  , let prop, _, _ =
                      substitute_expr_in_prop
                        Ir.is_equal_expr
                        (fun _ _ expr_to -> expr_to, [])
                        prop
                        Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                        Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
                        0
                    in
                    prop ))
               facts
           in
           facts @ new_facts, new_goal
         | _ ->
           let new_args =
             List.map
               (fun arg ->
                  Ir.
                    { desc = Var (arg ^ string_of_int (counter ()))
                    ; typ = Ir.typ_of_string arg
                    })
               arg_types
           in
           let inductive_case =
             match constr with
             | Ir.Constructor constr -> Ir.Call (constr, new_args)
           in
           let ihs =
             let precedent_var = typ_name ^ string_of_int (counter ()) in
             let precedent =
               Ir.{ desc = Var precedent_var; typ = Ir.typ_of_string typ_name }
             in
             let consequent, _, _ =
               substitute_expr_in_prop
                 Ir.is_equal_expr
                 (fun _ _ expr_to -> expr_to, [])
                 goal
                 Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                 precedent
                 0
             in
             ( "SIH" ^ string_of_int (counter ())
             , Forall
                 ( [ precedent_var, Type typ_name ]
                 , Imply
                     ( [ Lt
                           ( precedent
                           , Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
                           )
                       ]
                     , consequent ) ) )
           in
           let new_facts =
             ihs
             :: [ ( "Inductive" ^ string_of_int (counter ())
                  , Eq
                      ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                      , Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name } ) )
                ]
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
               Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
               0
           in
           let facts =
             List.map
               (fun (name, prop) ->
                  ( name
                  , let prop, _, _ =
                      substitute_expr_in_prop
                        Ir.is_equal_expr
                        (fun _ _ expr_to -> expr_to, [])
                        prop
                        Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                        Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
                        0
                    in
                    prop ))
               facts
           in
           facts @ new_facts, new_goal)
      decl
  | _ -> failwith "not implemented"
;;

let rec get_type_in_prop name prop =
  match prop with
  | Eq (e1, e2) ->
    (match Ir.get_type_in_expr name e1 with
     | Some typ -> Some typ
     | None -> Ir.get_type_in_expr name e2)
  | Le (e1, e2) ->
    (match Ir.get_type_in_expr name e1 with
     | Some typ -> Some typ
     | None -> Ir.get_type_in_expr name e2)
  | Lt (e1, e2) ->
    (match Ir.get_type_in_expr name e1 with
     | Some typ -> Some typ
     | None -> Ir.get_type_in_expr name e2)
  | And (p1, p2) ->
    (match get_type_in_prop name p1 with
     | Some typ -> Some typ
     | None -> get_type_in_prop name p2)
  | Or (p1, p2) ->
    (match get_type_in_prop name p1 with
     | Some typ -> Some typ
     | None -> get_type_in_prop name p2)
  | Not p -> get_type_in_prop name p
  | Forall (var_list, p) ->
    if List.exists (fun (name', _) -> name = name') var_list
    then None
    else get_type_in_prop name p
  | Imply (cond_list, p2) ->
    List.fold_left
      (fun acc cond ->
         match acc with
         | Some _ -> acc
         | None -> get_type_in_prop name cond)
      None
      (cond_list @ [ p2 ])
  | Type typ -> Some (Ir.typ_of_string typ)
;;

let apply_destruct env name facts goal =
  let typ_name =
    match get_type_in_prop name goal with
    | Some typ -> typ |> Ir.pp_typ
    | _ -> failwith "there is no such variable"
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
                      { Ir.desc = Ir.Var (arg ^ string_of_int (counter ()))
                      ; Ir.typ = Ir.typ_of_string arg
                      })
                   arg_types )
         in
         let new_facts =
           [ ( "Base" ^ string_of_int (counter ())
             , Eq
                 ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                 , Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name } ) )
           ]
         in
         let new_goal, _, _ =
           substitute_expr_in_prop
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to, [])
             goal
             Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
             Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
             0
         in
         let facts =
           List.map
             (fun (name, prop) ->
                ( name
                , let prop, _, _ =
                    substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to, [])
                      prop
                      Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                      Ir.{ desc = base_case; typ = Ir.typ_of_string typ_name }
                      0
                  in
                  prop ))
             facts
         in
         facts @ new_facts, new_goal
       | _ ->
         let new_args =
           List.map
             (fun arg ->
                Ir.
                  { desc = Var (arg ^ string_of_int (counter ()))
                  ; typ = Ir.typ_of_string arg
                  })
             arg_types
         in
         let inductive_case =
           match constr with
           | Ir.Constructor constr -> Ir.Call (constr, new_args)
         in
         let new_facts =
           [ ( "Inductive" ^ string_of_int (counter ())
             , Eq
                 ( Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                 , Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name } ) )
           ]
         in
         let new_goal, _, _ =
           substitute_expr_in_prop
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to, [])
             goal
             Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
             Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
             0
         in
         let facts =
           List.map
             (fun (name, prop) ->
                ( name
                , let prop, _, _ =
                    substitute_expr_in_prop
                      Ir.is_equal_expr
                      (fun _ _ expr_to -> expr_to, [])
                      prop
                      Ir.{ desc = Var name; typ = Ir.typ_of_string typ_name }
                      Ir.{ desc = inductive_case; typ = Ir.typ_of_string typ_name }
                      0
                  in
                  prop ))
             facts
         in
         facts @ new_facts, new_goal)
    decl
;;

let rec get_case_match expr pat =
  match expr.Ir.desc, pat with
  | _, Ir.Pat_Var var' -> [ Ir.{ desc = Var var'; typ = expr.typ }, expr ]
  (* we need to check type *)
  | Ir.Call (constr, arg_list), Ir.Pat_Constr (constr', pat_list) ->
    if constr = constr'
    then
      if arg_list = [] && pat_list = []
      then
        [ ( Ir.{ desc = Call (constr', []); typ = expr.typ }
          , Ir.{ desc = Call (constr, []); typ = expr.typ } )
        ]
      else
        List.fold_left2
          (fun (acc, is_done) e p ->
             if is_done
             then [], true
             else (
               let next = get_case_match e p in
               if next = [] then [], true else acc @ next, false))
          ([], false)
          arg_list
          pat_list
        |> fst
    else []
  | _ -> []
;;

let rec simplify_expr (env : Ir.t) expr =
  match expr.Ir.desc with
  | Ir.Var _ -> expr
  | Ir.Call (name, args) ->
    let args = List.map (simplify_expr env) args in
    (try
       let decl = Ir.find_decl name env in
       let decl_args, fun_decl =
         match decl with
         | Ir.NonRec (_, args, e) -> args, e
         | Ir.Rec (_, args, e) -> args, e
         | _ -> failwith "This expression is not a function"
       in
       let new_expr =
         List.fold_left2
           (fun e name arg ->
              let exp, _, _ =
                substitute_expr_in_expr
                  Ir.is_equal_expr
                  (fun _ _ expr_to -> expr_to, [])
                  e
                  Ir.{ desc = Var name; typ = arg.typ }
                  arg
                  0
                  []
              in
              exp)
           fun_decl
           decl_args
           args
       in
       simplify_expr env new_expr
     with
     | _ -> Ir.{ desc = Call (name, args); typ = expr.typ })
  | Ir.Match (e, cases) ->
    let e = simplify_expr env e in
    let new_expr =
      List.fold_left
        (fun acc case ->
           match acc with
           | Some _ -> acc
           | None ->
             (match case with
              | Ir.Case (pat, e') ->
                let match_list = get_case_match e pat in
                if match_list = []
                then acc
                else (
                  let new_expr =
                    List.fold_left
                      (fun e (e1, e2) ->
                         let exp, _, _ =
                           substitute_expr_in_expr
                             Ir.is_equal_expr
                             (fun _ _ expr_to -> expr_to, [])
                             e
                             e1
                             e2
                             0
                             []
                         in
                         exp)
                      e'
                      match_list
                  in
                  Some new_expr)))
        None
        cases
    in
    new_expr |> Option.get
  | Ir.LetIn (let_list, e) ->
    let new_expr =
      List.fold_left
        (fun e (name, e') ->
           let exp, _, _ =
             substitute_expr_in_expr
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               e
               Ir.{ desc = Var name; typ = e'.typ }
               e'
               0
               []
           in
           exp)
        e
        let_list
    in
    simplify_expr env new_expr
  | Ir.IfthenElse (e1, e2, e3) ->
    let e1 = simplify_expr env e1 in
    (match e1.Ir.desc with
     | Ir.Bool true -> simplify_expr env e2
     | Ir.Bool false -> simplify_expr env e3
     | _ -> Ir.{ desc = IfthenElse (e1, e2, e3); typ = e2.typ })
  | _ -> failwith "not implemented"
;;

let rec simplify_prop env prop =
  match prop with
  | Eq (e1, e2) ->
    let e1 = simplify_expr env e1 in
    let e2 = simplify_expr env e2 in
    Eq (e1, e2)
  | Le (e1, e2) ->
    let e1 = simplify_expr env e1 in
    let e2 = simplify_expr env e2 in
    Le (e1, e2)
  | Lt (e1, e2) ->
    let e1 = simplify_expr env e1 in
    let e2 = simplify_expr env e2 in
    Lt (e1, e2)
  | And (p1, p2) ->
    let p1 = simplify_prop env p1 in
    let p2 = simplify_prop env p2 in
    And (p1, p2)
  | Or (p1, p2) ->
    let p1 = simplify_prop env p1 in
    let p2 = simplify_prop env p2 in
    Or (p1, p2)
  | Not p ->
    let p = simplify_prop env p in
    Not p
  | Forall (var_list, p) ->
    let p = simplify_prop env p in
    Forall (var_list, p)
  | Imply (cond_list, p2) ->
    let cond_list = List.map (simplify_prop env) cond_list in
    let p2 = simplify_prop env p2 in
    Imply (cond_list, p2)
  | Type typ -> Type typ
;;

let apply_simpl env facts goal target =
  match target with
  | "goal" ->
    let new_goal = simplify_prop env goal in
    facts, new_goal
  | _ ->
    let new_fact = List.assoc target facts in
    let new_fact = simplify_prop env new_fact in
    let facts =
      List.map
        (fun (name, prop) -> if name = target then name, new_fact else name, prop)
        facts
    in
    facts, goal
;;

let apply_assert prop t =
  let lemma_name = "lemma" ^ string_of_int (counter ()) in
  let t = List.map (fun (facts, goal) -> facts @ [ lemma_name, prop ], goal) t in
  let lemma = [], prop in
  lemma :: t
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
  | Destruct name -> apply_destruct env name facts goal @ List.tl t
  | Case expr -> apply_case expr facts goal @ List.tl t
  | SimplIn target -> apply_simpl env facts goal target :: List.tl t
  | Reflexivity -> apply_eq goal @ List.tl t
  | Assert prop -> apply_assert prop t
;;

let mk_proof program_a program_b func_name =
  (* dummy *)
  let env = program_a @ program_b in
  ignore func_name;
  ignore program_a;
  ignore program_b;
  let facts = [] in
  let goal =
    Forall
      ( [ "a", Type "nat"; "b", Type "nat" ]
      , Eq
          ( Ir.
              { desc =
                  Call
                    ( "natadd_ta1"
                    , [ Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
                      ; Ir.{ desc = Var "b"; typ = Ir.typ_of_string "nat" }
                      ] )
              ; typ = Ir.typ_of_string "nat"
              }
          , Ir.
              { desc =
                  Call
                    ( "natadd_ta2"
                    , [ Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
                      ; Ir.{ desc = Var "b"; typ = Ir.typ_of_string "nat" }
                      ] )
              ; typ = Ir.typ_of_string "nat"
              } ) )
  in
  let lemma =
    Forall
      ( [ "a", Type "nat" ]
      , Eq
          ( Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
          , Ir.
              { desc =
                  Call
                    ( "natadd_ta2"
                    , [ Ir.{ desc = Call ("ZERO", []); typ = Ir.typ_of_string "nat" }
                      ; Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
                      ] )
              ; typ = Ir.typ_of_string "nat"
              } ) )
  in
  let lemma2 =
    Forall
      ( [ "a", Type "nat"; "b", Type "nat" ]
      , Eq
          ( Ir.
              { desc =
                  Call
                    ( "natadd_ta2"
                    , [ Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
                      ; Ir.{ desc = Var "b"; typ = Ir.typ_of_string "nat" }
                      ] )
              ; typ = Ir.typ_of_string "nat"
              }
          , Ir.
              { desc =
                  Call
                    ( "natadd_ta2"
                    , [ Ir.{ desc = Var "b"; typ = Ir.typ_of_string "nat" }
                      ; Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
                      ] )
              ; typ = Ir.typ_of_string "nat"
              } ) )
  in
  let _ = ignore (lemma, lemma2) in
  let tactics =
    [ Induction "a"
    ; SimplIn "goal"
    ; Induction "b"
    ; SimplIn "goal"
    ; Reflexivity
    ; SimplIn "goal"
    ; RewriteReverse ("IH7", "goal", 0)
    ; Reflexivity
    ; SimplIn "goal"
    ; Intro "b"
    ; RewriteInAt ("IH3", "goal", 0)
    ; Assert lemma2
    ; Induction "a"
    ; SimplIn "goal"
    ; Induction "b"
    ; SimplIn "goal"
    ; Reflexivity
    ; SimplIn "goal"
    ; RewriteInAt ("IH16", "goal", 0)
    ; Reflexivity
    ; SimplIn "goal"
    ; Induction "b"
    ; SimplIn "goal"
    ; Assert lemma
    ; Induction "a"
    ; SimplIn "goal"
    ; Reflexivity
    ; SimplIn "goal"
    ; RewriteReverse ("IH25", "goal", 0)
    ; Reflexivity
    ; RewriteReverse ("lemma22", "goal", 0)
    ; Reflexivity
    ; SimplIn "goal"
    ; RewriteReverse ("IH12", "goal", 0)
    ; SimplIn "goal"
    ; RewriteInAt ("IH20", "goal", 0)
    ; RewriteInAt ("IH12", "goal", 0)
    ; Reflexivity
    ; RewriteInAt ("lemma9", "goal", 0)
    ; SimplIn "goal"
    ; Reflexivity
    ]
  in
  List.fold_left (fun t tactic -> apply_tactic t env tactic) [ facts, goal ] tactics
  |> pp_t
  |> print_endline
;;

let parse_expr goal src =
  let expr = src |> Lexing.from_string |> Parse.expression in
  let free_vars = Ir.get_free_vars expr in
  let binding =
    List.map (fun var -> var, get_type_in_prop var goal |> Option.get) free_vars
  in
  Ir.ir_of_parsetree expr binding
;;

let rec parse_prop src binding =
  let parts = String.split_on_char ',' src in
  match parts with
  | [ src ] ->
    let parts = String.split_on_char '=' src in
    let lhs = List.hd parts |> Lexing.from_string |> Parse.expression in
    let rhs = List.nth parts 1 |> Lexing.from_string |> Parse.expression in
    let lhs = Ir.ir_of_parsetree lhs binding in
    let rhs = Ir.ir_of_parsetree rhs binding in
    Eq (lhs, rhs)
  | quantifer :: prop ->
    let quantifer = String.split_on_char ' ' quantifer in
    let quantifer = String.concat "" quantifer in
    let quantifer = String.split_on_char '(' quantifer in
    let quantifer = List.tl quantifer in
    let qvars =
      List.map
        (fun qvar ->
           match String.split_on_char ':' qvar with
           | [ var; typ ] ->
             let typ = String.split_on_char ')' typ |> List.hd in
             var, Type typ
           | _ -> failwith "not implemented")
        quantifer
    in
    let binding =
      List.map
        (fun qvar ->
           match String.split_on_char ':' qvar with
           | [ var; typ ] ->
             let typ = String.split_on_char ')' typ |> List.hd in
             var, Ir.typ_of_string typ
           | _ -> failwith "not implemented")
        quantifer
    in
    let prop = String.concat " " prop in
    Forall (qvars, parse_prop prop binding)
  | _ -> failwith "not implemented"
;;

let parse_tactic t s =
  let _, goal = List.hd t in
  let parts = String.split_on_char ' ' s in
  let name = List.hd parts in
  let args = List.tl parts in
  match name with
  | "intro" -> Intro (List.hd args)
  | "rewrite" ->
    if List.nth args 0 = "<-"
    then
      RewriteReverse
        ( List.nth args 1
        , List.nth args 3
        , if List.nth args 5 = "*" then 0 else int_of_string (List.nth args 5) )
    else
      RewriteInAt
        ( List.nth args 0
        , List.nth args 2
        , if List.nth args 4 = "*" then 0 else int_of_string (List.nth args 4) )
  | "induction" -> Induction (List.hd args)
  | "strong_induction" -> StrongInduction (List.hd args)
  | "destruct" -> Destruct (List.hd args)
  | "simpl" -> SimplIn (List.hd args)
  | "reflexivity" -> Reflexivity
  | "case" -> Case (parse_expr goal (String.concat " " args))
  | "assert" -> Assert (parse_prop (String.concat " " args) [])
  | _ -> failwith "not implemented"
;;

let proof_top program_a program_b =
  let goal =
    Forall
      ( [ "a", Type "nat"; "b", Type "nat" ]
      , Eq
          ( Ir.
              { desc =
                  Call
                    ( "natadd_ta1"
                    , [ Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
                      ; Ir.{ desc = Var "b"; typ = Ir.typ_of_string "nat" }
                      ] )
              ; typ = Ir.typ_of_string "nat"
              }
          , Ir.
              { desc =
                  Call
                    ( "natadd_ta2"
                    , [ Ir.{ desc = Var "a"; typ = Ir.typ_of_string "nat" }
                      ; Ir.{ desc = Var "b"; typ = Ir.typ_of_string "nat" }
                      ] )
              ; typ = Ir.typ_of_string "nat"
              } ) )
  in
  let env = program_a @ program_b in
  let init = [ [], goal ] in
  let rec loop t =
    pp_t t |> print_endline;
    print_newline ();
    let s = read_line () in
    print_newline ();
    let t =
      try apply_tactic t env (parse_tactic t s) with
      | e ->
        Printexc.to_string e |> print_endline;
        t
    in
    loop t
  in
  loop init
;;
