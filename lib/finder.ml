type t = Proof.t
type env = Proof.env
type state = Proof.state
type lemma_stack = Proof.lemma_stack
type lemma = Proof.goal
type expr = Proof.expr

let is_duplicated (env : env) (t : t) (lemma : lemma) : bool =
  ignore (env, t, lemma);
  failwith "TODO"
;;

let find_common_subterm expr1 expr2 : expr list =
  let l_expr_list = Prover.collect_expr_in_expr expr1 in
  let r_expr_list = Prover.collect_expr_in_expr expr2 in
  let common_term = List.filter (fun expr -> List.mem expr r_expr_list) l_expr_list in
  List.filter
    (fun expr ->
       match expr.Ir.desc with
       | Var _ -> false
       | _ -> true)
    common_term
;;

let find_common_subterm_in_prop (goal : Proof.goal) : expr list =
  match goal with
  | Forall _ -> []
  | Eq (expr1, expr2) -> find_common_subterm expr1 expr2
  | _ -> []
;;

let rec coellect_var_in_pattern (pattern : Ir.pattern) : string list =
  match pattern with
  | Ir.Pat_Var name -> [ name ]
  | Ir.Pat_Constr (_, pat_list) ->
    List.map coellect_var_in_pattern pat_list |> List.concat
  | Ir.Pat_Tuple pat_list -> List.map coellect_var_in_pattern pat_list |> List.concat
  | _ -> []
;;

let rec collect_free_var_in_expr (expr : expr) (binding : string list)
  : (string * Proof.prop) list
  =
  match expr.desc with
  | Var name -> if List.mem name binding then [] else [ name, Proof.Type expr.typ ]
  | Match (match_list, case_list) ->
    let var_in_match =
      List.map (fun e -> collect_free_var_in_expr e binding) match_list |> List.concat
    in
    let var_in_case =
      List.map
        (fun case ->
           match case with
           | Ir.Case (pat, e) ->
             let new_bind = coellect_var_in_pattern pat in
             collect_free_var_in_expr e (binding @ new_bind))
        case_list
      |> List.concat
    in
    var_in_match @ var_in_case
  | LetIn (assign, e) ->
    let var_in_assign =
      List.map (fun (_, body) -> collect_free_var_in_expr body binding) assign
      |> List.concat
    in
    let new_bind = List.map (fun (name, _) -> name) assign in
    var_in_assign @ collect_free_var_in_expr e (binding @ new_bind)
  | Call (_, args) ->
    List.map (fun e -> collect_free_var_in_expr e binding) args |> List.concat
;;

let rec collect_free_var_in_prop (goal : Proof.prop) (binding : string list)
  : (string * Proof.prop) list
  =
  match goal with
  | Forall (var_list, prop) ->
    let new_bind = List.map fst var_list in
    collect_free_var_in_prop prop (binding @ new_bind)
  | Eq (lhs, rhs) ->
    collect_free_var_in_expr lhs binding @ collect_free_var_in_expr rhs binding
  | _ -> []
;;

let naive_generalize env (goal : Proof.goal) t : lemma list =
  let goal = Proof.simplify_prop env goal in
  let trivial =
    match goal with
    | Proof.Forall (_, Eq (lhs, rhs)) | Proof.Eq (lhs, rhs) -> lhs = rhs
    | _ -> false
  in
  match trivial with
  | true -> []
  | _ ->
    let just_generalize_var =
      collect_free_var_in_prop goal [] |> List.sort_uniq compare
    in
    let just_generalize_new_goal =
      if List.is_empty just_generalize_var
      then []
      else [ Proof.Forall (just_generalize_var, goal) ]
    in
    let t = Proof.(create_t ~proof:t.proof ~counter:t.counter ()) in
    let common_subterm = find_common_subterm_in_prop goal in
    let common_subterm = List.sort_uniq compare common_subterm in
    let new_qvars =
      List.map
        (fun expr ->
           Ir.
             { desc = Var (var_of_typ expr.typ ^ string_of_int (Proof.get_counter t))
             ; typ = expr.typ
             })
        common_subterm
    in
    let new_goals =
      List.map2
        (fun subterm var ->
           let new_goal, _, _ =
             Proof.substitute_expr_in_prop
               Ir.is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               goal
               subterm
               var
               0
           in
           new_goal)
        common_subterm
        new_qvars
    in
    let qvars_list =
      List.map
        (fun new_goal -> collect_free_var_in_prop new_goal [] |> List.sort_uniq compare)
        new_goals
    in
    just_generalize_new_goal
    @ List.fold_left2
        (fun acc qvars new_goal ->
           if List.is_empty qvars then acc else Proof.Forall (qvars, new_goal) :: acc)
        []
        qvars_list
        new_goals
;;

let make_lemmas (env : env) (t_list : t list) : (t * lemma) list =
  let lemmas =
    List.map
      (fun t ->
         let state = Proof.get_first_state t in
         let _, goal = state in
         let lemmas = naive_generalize env goal t in
         List.map (fun lemma -> t, lemma) lemmas)
      t_list
    |> List.concat
  in
  let lemmas =
    List.fold_left
      (fun acc (t, lemma) ->
         let lemma_stack = Proof.get_lemma_stack t in
         if
           List.exists
             (fun (t', lemma') ->
                let lemma_stack' = Proof.get_lemma_stack t' in
                lemma_stack' = lemma_stack
                && Proof.simplify_prop env lemma = Proof.simplify_prop env lemma')
             acc
         then acc
         else (t, Proof.simplify_prop env lemma) :: acc)
      []
      lemmas
  in
  let _ = lemmas |> List.iter (fun (_, lemma) -> Proof.pp_prop lemma |> print_endline) in
  lemmas
;;
