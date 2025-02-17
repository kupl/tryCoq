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
  let qvars = collect_free_var_in_prop new_goal [] in
  let qvars =
    List.fold_left (fun acc var -> if List.mem var acc then acc else var :: acc) [] qvars
  in
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
