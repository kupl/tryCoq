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

let naive_generalize (goal : Proof.goal) : lemma list =
  let common_subterm = find_common_subterm_in_prop goal in
  let new_qvars =
    List.map (fun expr -> Ir.var_of_typ expr.Ir.typ, expr.Ir.typ) common_subterm
  in
  let new_goal =
    List.fold_left2
      (fun acc expr (var_name, typ) ->
         let new_goal, _, _ =
           Proof.substitute_expr_in_prop
             Ir.is_equal_expr
             (fun _ _ expr_to -> expr_to, [])
             acc
             expr
             Ir.{ desc = Var var_name; typ }
             0
         in
         new_goal)
      goal
      common_subterm
      new_qvars
  in
  let qvars = List.map (fun (var_name, typ) -> var_name, Proof.Type typ) new_qvars in
  if List.is_empty qvars then [] else [ Forall (qvars, new_goal) ]
;;

let make_lemmas (env : env) (t_list : t list) : (t * lemma) list =
  ignore env;
  let lemmas =
    List.map
      (fun t ->
         let state = Proof.get_first_state t in
         let _, goal = state in
         let lemmas = naive_generalize goal in
         List.map (fun lemma -> t, lemma) lemmas)
      t_list
    |> List.concat
  in
  let _ = lemmas |> List.iter (fun (_, lemma) -> Proof.pp_prop lemma |> print_endline) in
  lemmas
;;
