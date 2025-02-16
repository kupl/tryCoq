open Sexplib.Std

type t = lemma_stack * conjecture list * tactic list [@@deriving sexp]
and lemma_stack = theorem list [@@deriving sexp]
and conjecture = state list * goal [@@deriving sexp]
and state = fact list * goal [@@deriving sexp]
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
  | Type of Ir.typ
[@@deriving sexp]

and expr = Ir.expr [@@deriving sexp]
and theorem = tactic list * string * goal [@@deriving sexp]

and tactic =
  | Intro of string
  | Induction of string
  | StrongInduction of string
  | SimplIn of string
  | RewriteInAt of string * string * int
  | RewriteReverse of string * string * int
  | Destruct of string
  | Case of expr
  | Reflexivity
  | Discriminate
  | Assert of prop
[@@deriving sexp]

type env = Ir.t [@@deriving sexp]

type debug_tactic =
  | AllLemma
  | AllConj
  | AllState
[@@deriving sexp]

let mk_intro name = Intro name
let mk_induction name = Induction name
let mk_strong_induction name = StrongInduction name
let mk_simpl_in target = SimplIn target
let mk_rewrite_in_at fact goal i = RewriteInAt (fact, goal, i)
let mk_rewrite_reverse fact goal i = RewriteReverse (fact, goal, i)
let mk_destruct name = Destruct name
let mk_case expr = Case expr
let mk_reflexivity = Reflexivity
let mk_discriminate = Discriminate
let mk_assert prop = Assert prop

let get_lemma_stack (t : t) =
  let lemma_stack, _, _ = t in
  lemma_stack
;;

let get_conj_list (t : t) =
  let _, conj_list, _ = t in
  conj_list
;;

let get_tactic_history (t : t) =
  let _, _, tactic_list = t in
  tactic_list
;;

let get_first_state (t : t) =
  let conj_list = get_conj_list t in
  List.hd conj_list |> fst |> List.hd
;;

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
let string_of_state state = state |> sexp_of_state |> Sexplib.Sexp.to_string
let string_of_theorem t = t |> sexp_of_theorem |> Sexplib.Sexp.to_string
let string_of_tactic t = t |> sexp_of_tactic |> Sexplib.Sexp.to_string
let string_of_prop p = p |> sexp_of_prop |> Sexplib.Sexp.to_string
let string_of_expr e = e |> sexp_of_expr |> Sexplib.Sexp.to_string
let pp_expr = Ir.pp_expr

let rec pp_prop prop =
  (* let pp_expr = fun a -> sexp_of_expr a |> Sexplib.Sexp.to_string in *)
  match prop with
  | Eq (e1, e2) -> pp_expr e1 ^ " = " ^ pp_expr e2
  | Le (e1, e2) -> pp_expr e1 ^ " <= " ^ pp_expr e2
  | Lt (e1, e2) -> pp_expr e1 ^ " < " ^ pp_expr e2
  | And (p1, p2) -> pp_prop p1 ^ " /\\ " ^ pp_prop p2
  | Or (p1, p2) -> pp_prop p1 ^ " \\/ " ^ pp_prop p2
  | Not p -> "not " ^ pp_prop p
  | Forall (var_list, p) ->
    "forall "
    ^ (List.map (fun (name, typ) -> "(" ^ name ^ ":" ^ pp_prop typ ^ ")") var_list
       |> String.concat " ")
    ^ ", "
    ^ pp_prop p
  | Imply (cond_list, p2) ->
    (List.map (fun cond -> pp_prop cond) cond_list |> String.concat "->")
    ^ " -> "
    ^ pp_prop p2
  | Type typ -> Ir.pp_typ typ
;;

let pp_fact (name, prop) = name ^ " : " ^ pp_prop prop

let pp_tactic tactic =
  match tactic with
  | Intro name -> "intro " ^ name
  | RewriteInAt (fact, goal, i) ->
    "rewrite " ^ fact ^ " in " ^ goal ^ " at " ^ string_of_int i
  | RewriteReverse (fact, goal, i) ->
    "rewrite <- " ^ fact ^ " in " ^ goal ^ " at " ^ string_of_int i
  | Induction name -> "induction " ^ name
  | StrongInduction name -> "strong induction " ^ name
  | Destruct name -> "destruct " ^ name
  | Case expr -> "case " ^ Ir.pp_expr expr
  | SimplIn target -> "simpl in " ^ target
  | Reflexivity -> "reflexivity"
  | Assert prop -> "assert " ^ pp_prop prop
  | Discriminate -> "discriminate"
;;

let pp_theorem (tactics, name, goal) =
  "Theorem "
  ^ name
  ^ " : \n"
  ^ pp_prop goal
  ^ "Proof.\n"
  ^ (List.map pp_tactic tactics |> String.concat "\n")
  ^ "\nQed.\n"
;;

let pp_lemma_stack (stack : lemma_stack) =
  List.map (fun (_, name, goal) -> name ^ " : " ^ pp_prop goal) stack
  |> String.concat "\n\n"
;;

let pp_conjecture ?(all : bool = false) (conj : conjecture) =
  let state_list, conj_goal = conj in
  if List.is_empty state_list
  then "No goal"
  else (
    let print_goal ((facts, goal), i) =
      string_of_int (i + 1)
      ^ (match i with
         | 0 -> "st"
         | 1 -> "nd"
         | 2 -> "rd"
         | _ -> "th")
      ^ " goal of"
      ^ " : "
      ^ pp_prop conj_goal
      ^ "\n"
      ^ (List.map pp_fact facts |> String.concat "\n")
      ^ "\n---------------------------------------\n"
      ^ pp_prop goal
    in
    (match all with
     | true ->
       List.map print_goal (List.combine state_list (range 0 (List.length state_list)))
     | false ->
       [ print_goal (List.hd state_list, 0)
       ; (List.length state_list - 1 |> string_of_int) ^ " goal(s) more..."
       ])
    |> String.concat "\n\n")
;;

let pp_t ?(debug_tactic : debug_tactic option = None) (t : t) =
  let all_lemma, all_conjecture, all_state =
    match debug_tactic with
    | Some AllLemma -> true, false, false
    | Some AllConj -> false, true, true
    | Some AllState -> false, false, true
    | None -> false, false, false
  in
  let lemma_stack, conjecture_list, _ = t in
  (if all_lemma then "Lemma stack : \n" ^ pp_lemma_stack lemma_stack else "")
  ^ "\n\n"
  ^
  if all_conjecture
  then (
    let str_conj = List.map (fun conj -> pp_conjecture ~all:true conj) conjecture_list in
    String.concat "\n\n" str_conj)
  else if List.is_empty conjecture_list
  then "No conjecture"
  else
    pp_conjecture ~all:all_state (List.hd conjecture_list)
    ^ "\n\n"
    ^ (List.length conjecture_list - 1 |> string_of_int)
    ^ " conjecture(s) more..."
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

let apply_intro name state : state =
  let facts, goal = state in
  match goal with
  | Forall (var_list, goal) ->
    if name = "*"
    then facts @ var_list, goal
    else (
      let typ =
        try List.assoc name var_list with
        | _ -> failwith "there is no such variable"
      in
      let var_list = List.filter (fun (name', _) -> name' <> name) var_list in
      let new_goal = if List.is_empty var_list then goal else Forall (var_list, goal) in
      facts @ [ name, typ ], new_goal)
  | Imply (cond_list, p2) ->
    facts @ [ name, List.hd cond_list ], Imply (List.tl cond_list, p2)
  | _ -> failwith "There is no term that can be introduced"
;;

let rec apply_eq goal =
  match goal with
  | Eq (e1, e2) ->
    if Ir.is_equal_expr e1 e2 then [] else failwith "LHS and RHS are not equal"
  | Forall (_, goal) -> apply_eq goal
  | _ -> failwith "The goal is not an equality"
;;

let apply_induction env name state : state list =
  let facts, goal = state in
  match goal with
  | Forall (var_list, goal) ->
    let typ =
      try List.assoc name var_list with
      | _ -> failwith "there is no such variable"
    in
    let var_list = List.filter (fun (name', _) -> name' <> name) var_list in
    let typ =
      match typ with
      | Type typ -> typ
      | _ -> failwith "not implemented"
    in
    let typ_args, (origin_args, decl) =
      match typ with
      | Ir.Talgebraic (typ_name, typ_list) ->
        ( typ_list
        , (try Ir.find_decl typ_name env |> Ir.get_typ_decl with
           | _ -> failwith ("cannot found such type : " ^ typ_name)) )
      | _ -> failwith "This type is not algebraic"
    in
    let typ_match = List.combine origin_args typ_args in
    let decl =
      List.map
        (fun (constr, arg_types) ->
           constr, List.map (fun arg -> Ir.substitute_typ arg typ_match) arg_types)
        decl
    in
    List.map
      (fun (constr, arg_types) ->
         let rec_args = List.filter (fun arg -> typ = arg) arg_types in
         let arg_bind =
           List.map
             (fun arg -> (arg |> Ir.var_of_typ) ^ string_of_int (counter ()), arg)
             arg_types
         in
         match rec_args with
         | [] ->
           let base_case =
             match constr with
             | Ir.Constructor constr ->
               Ir.Call
                 ( constr
                 , List.map (fun (name, typ) -> Ir.{ desc = Var name; typ }) arg_bind )
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ }
               Ir.{ desc = base_case; typ }
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
                        Ir.{ desc = Var name; typ }
                        Ir.{ desc = base_case; typ }
                        0
                    in
                    prop ))
               facts
           in
           let typ_facts = List.map (fun (name, typ) -> name, Type typ) arg_bind in
           typ_facts @ facts, new_goal
         | _ ->
           let new_args, new_rec_args =
             partition_and_transform
               (fun arg -> List.mem arg rec_args)
               (fun arg ->
                  Ir.
                    { desc = Var ((arg |> Ir.var_of_typ) ^ string_of_int (counter ()))
                    ; typ = arg
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
                        Ir.{ desc = Var name; typ }
                        arg
                        0
                    in
                    if List.is_empty var_list then prop else Forall (var_list, prop) ))
               new_rec_args
           in
           let new_facts =
             ihs
             @ [ ( "Inductive" ^ string_of_int (counter ())
                 , Eq (Ir.{ desc = Var name; typ }, Ir.{ desc = inductive_case; typ }) )
               ]
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ }
               Ir.{ desc = inductive_case; typ }
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
                        Ir.{ desc = Var name; typ }
                        Ir.{ desc = inductive_case; typ }
                        0
                    in
                    prop ))
               facts
           in
           let typ_facts =
             List.map
               (fun exp ->
                  ( (match exp.Ir.desc with
                     | Var name -> name
                     | _ -> failwith "dead point")
                  , Type exp.Ir.typ ))
               new_args
           in
           typ_facts @ facts @ new_facts, new_goal)
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
      Ir.is_typ_contained lhs_typ target_typ)
    else Ir.is_equal_expr source target
  | Ir.Call (name, args) ->
    (match target.Ir.desc with
     | Ir.Call (name', args') ->
       let result =
         name = name' && List.for_all2 (fun a b -> forall_target var_list a b) args' args
       in
       result
     | _ -> false)
  | Ir.Match (match_list1, cases) ->
    (match target.Ir.desc with
     | Ir.Match (match_list2, cases') ->
       List.for_all2 (forall_target var_list) match_list1 match_list2
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
;;

let rec get_match_var (match_list : (expr * expr) list) =
  List.fold_left
    (fun acc (expr_from, expr_to) ->
       match expr_from.Ir.desc with
       | Ir.Var _ -> (expr_from, expr_to) :: acc
       | Ir.Call (_, args) ->
         (match expr_to.Ir.desc with
          | Ir.Call (_, args') ->
            List.fold_left
              (fun acc (arg, arg') -> get_match_var [ arg, arg' ] @ acc)
              acc
              (List.combine args args')
          | _ -> failwith "not implemented")
       | _ -> acc)
    []
    match_list
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
         let args = get_match_var args in
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

let apply_rewrite lemma_stack state fact_label target_label i : state list =
  let facts, goal = state in
  let lemma_list = List.map (fun (_, name, prop) -> name, prop) lemma_stack in
  let source = List.assoc fact_label (facts @ lemma_list) in
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
                   | _ -> false)
                match_list)
           var_list)
    then (
      match_list
      |> List.iter (fun (a, b) -> Printf.printf "%s |> %s\n" (pp_expr a) (pp_expr b));
      failwith "Cannot find matched variable")
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

let apply_rewrite_reverse lemma_stack state fact_label target_label i : state list =
  let facts, goal = state in
  let lemma_list = List.map (fun (_, name, prop) -> name, prop) lemma_stack in
  let source = List.assoc fact_label (facts @ lemma_list) in
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
    if
      not
        (List.for_all
           (fun (e1, _) ->
              List.exists
                (fun (e2, _) ->
                   match e2.Ir.desc with
                   | Var var -> e1 = var
                   | _ -> false)
                match_list)
           var_list)
    then (
      match_list
      |> List.iter (fun (a, b) -> Printf.printf "%s |> %s\n" (pp_expr a) (pp_expr b));
      failwith "Cannot find matched variable")
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

let apply_strong_induction env name state : state list =
  let facts, goal = state in
  match goal with
  | Forall (var_list, goal) ->
    let var_list = List.filter (fun (name', _) -> name' <> name) var_list in
    let typ =
      try List.assoc name var_list with
      | _ -> failwith "there is no such variable"
    in
    let typ =
      match typ with
      | Type typ -> typ
      | _ -> failwith "not implemented"
    in
    let typ_args, (origin_args, decl) =
      match typ with
      | Ir.Talgebraic (typ_name, typ_list) ->
        ( typ_list
        , (try Ir.find_decl typ_name env |> Ir.get_typ_decl with
           | _ -> failwith ("cannot found such type : " ^ typ_name)) )
      | _ -> failwith "This type is not algebraic"
    in
    let typ_match = List.combine origin_args typ_args in
    let decl =
      List.map
        (fun (constr, arg_types) ->
           constr, List.map (fun arg -> Ir.substitute_typ arg typ_match) arg_types)
        decl
    in
    List.map
      (fun (constr, arg_types) ->
         let rec_args = List.filter (fun arg -> arg = typ) arg_types in
         let arg_bind =
           List.map
             (fun arg -> (arg |> Ir.var_of_typ) ^ string_of_int (counter ()), arg)
             arg_types
         in
         match rec_args with
         | [] ->
           let base_case =
             match constr with
             | Ir.Constructor constr ->
               Ir.Call
                 ( constr
                 , List.map (fun (name, typ) -> Ir.{ desc = Ir.Var name; typ }) arg_bind
                 )
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ }
               Ir.{ desc = base_case; typ }
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
                        Ir.{ desc = Var name; typ }
                        Ir.{ desc = base_case; typ }
                        0
                    in
                    prop ))
               facts
           in
           facts, new_goal
         | _ ->
           let new_args, _ =
             partition_and_transform
               (fun arg -> List.mem arg rec_args)
               (fun arg ->
                  Ir.
                    { desc = Var ((arg |> Ir.var_of_typ) ^ string_of_int (counter ()))
                    ; typ = arg
                    })
               arg_types
           in
           let inductive_case =
             match constr with
             | Ir.Constructor constr -> Ir.Call (constr, new_args)
           in
           let ihs =
             let precedent_var = (typ |> Ir.var_of_typ) ^ string_of_int (counter ()) in
             let precedent = Ir.{ desc = Var precedent_var; typ } in
             let consequent, _, _ =
               substitute_expr_in_prop
                 Ir.is_equal_expr
                 (fun _ _ expr_to -> expr_to, [])
                 goal
                 Ir.{ desc = Var name; typ }
                 precedent
                 0
             in
             ( "SIH" ^ string_of_int (counter ())
             , Forall
                 ( [ precedent_var, Type typ ]
                 , Imply
                     ([ Lt (precedent, Ir.{ desc = inductive_case; typ }) ], consequent)
                 ) )
           in
           let new_facts =
             ihs
             :: [ ( "Inductive" ^ string_of_int (counter ())
                  , Eq (Ir.{ desc = Var name; typ }, Ir.{ desc = inductive_case; typ }) )
                ]
           in
           let new_goal, _, _ =
             substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               Ir.{ desc = Var name; typ }
               Ir.{ desc = inductive_case; typ }
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
                        Ir.{ desc = Var name; typ }
                        Ir.{ desc = inductive_case; typ }
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
  | Type typ -> Some typ
;;

let rec get_case_match expr_list pat =
  match expr_list with
  | [ expr ] ->
    (match expr.Ir.desc, pat with
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
         else (
           let result =
             List.fold_left2
               (fun (acc, is_done) e p ->
                  if is_done
                  then [], true
                  else (
                    let next = get_case_match [ e ] p in
                    if next = [] then [], true else acc @ next, false))
               ([], false)
               arg_list
               pat_list
             |> fst
           in
           result)
       else []
     | _ -> [])
  | _ ->
    (match pat with
     | Ir.Pat_Tuple l ->
       List.fold_left2
         (fun (is_done, acc) e pat ->
            if is_done
            then true, []
            else (
              let result = get_case_match [ e ] pat in
              if result = [] then true, [] else false, acc @ result))
         (false, [])
         expr_list
         l
       |> snd
     | _ -> failwith "pattern matching is ill-formed")
;;

let rec simplify_expr (env : Ir.t) expr =
  match expr.Ir.desc with
  | Ir.Var _ -> expr
  | Ir.Call (name, args) ->
    let args = List.map (simplify_expr env) args in
    (try
       let decl_args, fun_decl =
         let decl = Ir.find_decl name env in
         match decl with
         | Ir.NonRec (_, args, e) -> args, e
         | Ir.Rec (_, args, e) -> args, e
         | _ -> failwith "This expression is not a function"
       in
       let fun_body =
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
       let new_expr = simplify_expr env fun_body in
       if new_expr = fun_body
       then Ir.{ desc = Call (name, args); typ = expr.typ }
       else new_expr
     with
     | exn ->
       ignore exn;
       (* print_endline (Printexc.to_string exn); *)
       Ir.{ desc = Call (name, args); typ = expr.typ })
  | Ir.Match (match_list, cases) ->
    let match_list = List.map (simplify_expr env) match_list in
    let new_expr =
      List.fold_left
        (fun acc case ->
           match acc with
           | Some _ -> acc
           | None ->
             (match case with
              | Ir.Case (pat, e') ->
                let expr_match_list = get_case_match match_list pat in
                if expr_match_list = []
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
                      expr_match_list
                  in
                  Some new_expr)))
        None
        cases
    in
    (match new_expr with
     | None -> Ir.{ desc = Match (match_list, cases); typ = expr.typ }
     | Some e -> simplify_expr env e)
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

let apply_simpl env state target : state =
  let facts, goal = state in
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

let apply_assert prop t : t =
  let conj = [ [], prop ], prop in
  let lemma_stack, conj_list, tactic_list = t in
  lemma_stack, conj :: conj_list, tactic_list @ [ mk_assert prop ]
;;

let apply_destruct env name state : state list =
  let facts, goal = state in
  let typ =
    match get_type_in_prop name goal with
    | Some typ -> typ
    | _ -> failwith ("there is no such variable : " ^ name)
  in
  let typ_args, (origin_args, decl) =
    match typ with
    | Ir.Talgebraic (typ_name, typ_list) ->
      ( typ_list
      , (try Ir.find_decl typ_name env |> Ir.get_typ_decl with
         | _ -> failwith ("cannot found such type : " ^ typ_name)) )
    | _ -> failwith "This type is not algebraic"
  in
  let typ_match = List.combine origin_args typ_args in
  let decl =
    List.map
      (fun (constr, arg_types) ->
         constr, List.map (fun arg -> Ir.substitute_typ arg typ_match) arg_types)
      decl
  in
  List.map
    (fun (constr, arg_types) ->
       let rec_args = List.filter (fun arg -> arg = typ) arg_types in
       let arg_bind =
         List.map
           (fun arg -> (arg |> Ir.var_of_typ) ^ string_of_int (counter ()), arg)
           arg_types
       in
       match rec_args with
       | [] ->
         let base_case =
           match constr with
           | Ir.Constructor constr ->
             Ir.Call
               ( constr
               , List.map (fun (name, typ) -> Ir.{ desc = Ir.Var name; typ }) arg_bind )
         in
         let new_facts =
           [ ( "Dest" ^ string_of_int (counter ())
             , Eq (Ir.{ desc = Var name; typ }, Ir.{ desc = base_case; typ }) )
           ]
         in
         let new_goal, _, _ =
           substitute_expr_in_prop
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to, [])
             goal
             Ir.{ desc = Var name; typ }
             Ir.{ desc = base_case; typ }
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
                      Ir.{ desc = Var name; typ }
                      Ir.{ desc = base_case; typ }
                      0
                  in
                  prop ))
             facts
         in
         facts @ new_facts, new_goal
       | _ ->
         let new_args, _ =
           partition_and_transform
             (fun arg -> List.mem arg rec_args)
             (fun arg ->
                Ir.
                  { desc = Var ((arg |> Ir.var_of_typ) ^ string_of_int (counter ()))
                  ; typ = arg
                  })
             arg_types
         in
         let inductive_case =
           match constr with
           | Ir.Constructor constr -> Ir.Call (constr, new_args)
         in
         let new_facts =
           [ ( "Inductive" ^ string_of_int (counter ())
             , Eq (Ir.{ desc = Var name; typ }, Ir.{ desc = inductive_case; typ }) )
           ]
         in
         let new_goal, _, _ =
           substitute_expr_in_prop
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to, [])
             goal
             Ir.{ desc = Var name; typ }
             Ir.{ desc = inductive_case; typ }
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
                      Ir.{ desc = Var name; typ }
                      Ir.{ desc = inductive_case; typ }
                      0
                  in
                  prop ))
             facts
         in
         facts @ new_facts, new_goal)
    decl
;;

let apply_case env expr state : state list =
  let facts, goal = state in
  let typ = expr.Ir.typ in
  let typ_args, (origin_args, decl) =
    match typ with
    | Ir.Talgebraic (typ_name, typ_list) ->
      ( typ_list
      , (try Ir.find_decl typ_name env |> Ir.get_typ_decl with
         | _ -> failwith ("cannot found such type : " ^ typ_name)) )
    | _ -> failwith "This type is not algebraic"
  in
  let typ_match = List.combine origin_args typ_args in
  let decl =
    List.map
      (fun (constr, arg_types) ->
         constr, List.map (fun arg -> Ir.substitute_typ arg typ_match) arg_types)
      decl
  in
  List.map
    (fun (constr, arg_types) ->
       let rec_args = List.filter (fun arg -> arg = typ) arg_types in
       let arg_bind =
         List.map
           (fun arg -> (arg |> Ir.var_of_typ) ^ string_of_int (counter ()), arg)
           arg_types
       in
       match rec_args with
       | [] ->
         let base_case =
           match constr with
           | Ir.Constructor constr ->
             Ir.Call
               (constr, List.map (fun (name, typ) -> Ir.{ desc = Var name; typ }) arg_bind)
         in
         let new_facts =
           [ "Case" ^ string_of_int (counter ()), Eq (expr, Ir.{ desc = base_case; typ })
           ]
         in
         let new_goal, _, _ =
           substitute_expr_in_prop
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to, [])
             goal
             expr
             Ir.{ desc = base_case; typ }
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
                      Ir.{ desc = Var name; typ }
                      Ir.{ desc = base_case; typ }
                      0
                  in
                  prop ))
             facts
         in
         facts @ new_facts, new_goal
       | _ ->
         let new_args, _ =
           partition_and_transform
             (fun arg -> List.mem arg rec_args)
             (fun arg ->
                Ir.
                  { desc = Var ((arg |> Ir.var_of_typ) ^ string_of_int (counter ()))
                  ; typ = arg
                  })
             arg_types
         in
         let inductive_case =
           match constr with
           | Ir.Constructor constr -> Ir.Call (constr, new_args)
         in
         let new_facts =
           [ ( "Inductive" ^ string_of_int (counter ())
             , Eq (expr, Ir.{ desc = inductive_case; typ }) )
           ]
         in
         let new_goal, _, _ =
           substitute_expr_in_prop
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to, [])
             goal
             expr
             Ir.{ desc = inductive_case; typ }
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
                      Ir.{ desc = Var name; typ }
                      Ir.{ desc = inductive_case; typ }
                      0
                  in
                  prop ))
             facts
         in
         facts @ new_facts, new_goal)
    decl
;;

let apply_desrciminate env facts : state list =
  if
    List.exists
      (fun (_, prop) ->
         match prop with
         | Eq (e1, e2) ->
           let e1 = simplify_expr env e1 in
           let e2 = simplify_expr env e2 in
           Ir.absolute_neq e1 e2
         | _ -> false)
      facts
  then []
  else failwith "Cannot Discriminate"
;;

let apply_tactic (t : t) env tactic : t =
  let lemma_stack, conj_list, tactic_list = t in
  match tactic with
  | Assert prop -> apply_assert prop t
  | _ ->
    let fisrt_conj = List.hd conj_list in
    let state_list, conj_goal = fisrt_conj in
    let first_state = List.hd state_list in
    (match tactic with
     | Intro name ->
       ( lemma_stack
       , (apply_intro name first_state :: List.tl state_list, conj_goal)
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | RewriteInAt (fact, target_label, i) ->
       ( lemma_stack
       , ( apply_rewrite lemma_stack first_state fact target_label i @ List.tl state_list
         , conj_goal )
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | RewriteReverse (fact, target_label, i) ->
       ( lemma_stack
       , ( apply_rewrite_reverse lemma_stack first_state fact target_label i
           @ List.tl state_list
         , conj_goal )
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | Induction name ->
       ( lemma_stack
       , (apply_induction env name first_state @ List.tl state_list, conj_goal)
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | StrongInduction name ->
       ( lemma_stack
       , (apply_strong_induction env name first_state @ List.tl state_list, conj_goal)
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | Destruct name ->
       ( lemma_stack
       , (apply_destruct env name first_state @ List.tl state_list, conj_goal)
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | Case expr ->
       ( lemma_stack
       , (apply_case env expr first_state @ List.tl state_list, conj_goal)
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | SimplIn target ->
       ( lemma_stack
       , (apply_simpl env first_state target :: List.tl state_list, conj_goal)
         :: List.tl conj_list
       , tactic_list @ [ tactic ] )
     | Reflexivity ->
       let _, goal = first_state in
       let _ = apply_eq goal in
       let remain_states = List.tl state_list in
       (match remain_states with
        | [] ->
          ( lemma_stack @ [ [], "lemma" ^ string_of_int (counter ()), conj_goal ]
          , List.tl conj_list
          , tactic_list @ [ tactic ] )
        | _ ->
          ( lemma_stack
          , (remain_states, conj_goal) :: List.tl conj_list
          , tactic_list @ [ tactic ] ))
     | Discriminate ->
       let facts, _ = first_state in
       let _ = apply_desrciminate env facts in
       let remain_states = List.tl state_list in
       (match remain_states with
        | [] ->
          ( lemma_stack @ [ [], "lemma" ^ string_of_int (counter ()), conj_goal ]
          , List.tl conj_list
          , tactic_list @ [ tactic ] )
        | _ ->
          ( lemma_stack
          , (remain_states, conj_goal) :: List.tl conj_list
          , tactic_list @ [ tactic ] ))
     | _ -> failwith "not implemented")
;;

let parse_expr goal src decls =
  let expr = src |> Lexing.from_string |> Parse.expression in
  let free_vars = Ir.get_free_vars expr in
  let binding =
    List.map (fun var -> var, get_type_in_prop var goal |> Option.get) free_vars
  in
  Ir.ir_of_parsetree expr binding decls
;;

let parse_forall_vars str =
  let var_regex = Str.regexp "( *\\([^:()]+\\) *: *\\([^()]+\\) *)" in
  let rec extract acc pos =
    try
      ignore (Str.search_forward var_regex str pos);
      let var = String.trim (Str.matched_group 1 str) in
      let typ = String.trim (Str.matched_group 2 str) in
      extract ((var, typ) :: acc) (Str.match_end ())
    with
    | Not_found -> List.rev acc
  in
  extract [] 0
;;

let rec parse_prop src binding decls =
  let parts = String.split_on_char ',' src in
  match parts with
  | [ src ] ->
    let parts = String.split_on_char '=' src in
    let lhs = List.hd parts |> Lexing.from_string |> Parse.expression in
    let rhs = List.nth parts 1 |> Lexing.from_string |> Parse.expression in
    let lhs = Ir.ir_of_parsetree lhs binding decls in
    let rhs = Ir.ir_of_parsetree rhs binding decls in
    Eq (lhs, rhs)
  | quantifier :: prop ->
    let binding = parse_forall_vars quantifier in
    let binding = List.map (fun (var, typ) -> var, Ir.parse_typ typ) binding in
    let qvars = List.map (fun (var, typ) -> var, Type typ) binding in
    let prop = String.concat " " prop in
    Forall (qvars, parse_prop prop binding decls)
  | _ -> failwith "not implemented"
;;

let parse_tactic (t : t) src decls =
  let parts = String.split_on_char ' ' src in
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
  | "simpl" ->
    (match args with
     | _ :: [ hd ] -> SimplIn hd
     | [] -> SimplIn "goal"
     | _ -> failwith "not implemented")
  | "reflexivity" -> Reflexivity
  | "case" ->
    let state = get_first_state t in
    let goal = state |> snd in
    Case (parse_expr goal (String.concat " " args) decls)
  | "assert" -> Assert (parse_prop (String.concat " " args) [] decls)
  | "discriminate" -> Discriminate
  | _ -> failwith "wrong tactic"
;;

let proof_top env =
  let init = [], [], [] in
  let rec loop ?(debug_tactic : debug_tactic option = None) t =
    print_newline ();
    pp_t ~debug_tactic t |> print_endline;
    print_newline ();
    print_string ">>> ";
    match read_line () with
    | "allstate" -> loop ~debug_tactic:(Some AllState) t
    | "alllemma" -> loop ~debug_tactic:(Some AllLemma) t
    | "allconj" -> loop ~debug_tactic:(Some AllConj) t
    | s ->
      let t =
        try apply_tactic t env (parse_tactic t s env) with
        | exn ->
          print_endline (Printexc.to_string exn);
          t
      in
      (* let t = apply_tactic t env (parse_tactic t s env) in *)
      loop t
  in
  loop init
;;

let empty_t : t = [], [], []
