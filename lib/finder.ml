open Sexplib.Std

type t = Proof.t
type env = Proof.env
type state = Proof.state
type lemma_stack = Proof.lemma_stack
type lemma = Proof.goal
type expr = Proof.expr

type subtree =
  { desc : sub_desc
  ; typ : Ir.typ
  }
[@@deriving sexp]

and sub_desc =
  | Sub_Var of string
  | Sub_Call of string * subtree option list
[@@deriving sexp]

let rec pp_subtree (subtree : subtree) : string =
  match subtree.desc with
  | Sub_Var name -> name
  | Sub_Call (name, args) ->
    let args =
      List.map
        (fun arg ->
           match arg with
           | Some arg -> pp_subtree arg
           | None -> "_")
        args
    in
    name ^ "(" ^ String.concat ", " args ^ ")"
;;

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

let is_concerned fact binding =
  let free_vars = collect_free_var_in_prop fact [] in
  match fact with
  | Proof.Type _ -> false
  | _ -> List.for_all (fun (name, _) -> List.mem name binding) free_vars
;;

let split_t t : t list =
  let lemma_stack = Proof.get_lemma_stack t in
  let tactics = Proof.get_tactic_history t in
  let states, _ = Proof.get_conj_list t |> List.hd in
  List.map
    (fun state ->
       let dummy_goal = Proof.Type Ir.Tany in
       Proof.(
         create_t
           ~proof:(lemma_stack, [ [ state ], dummy_goal ], tactics)
           ~counter:t.counter
           ()))
    states
;;

let progress_with_split env t : t list =
  let t_list = split_t t in
  List.fold_left
    (fun acc t ->
       match Prover.progress_single_thread env t with
       | Some t ->
         List.fold_left
           (fun acc t ->
              match Prover.progress_single_thread env t with
              | Some t -> t :: acc
              | _ -> acc)
           acc
           (split_t t)
       | None -> acc)
    []
    t_list
;;

let filtering_concerned_fact facts goal =
  let free_var = collect_free_var_in_prop goal [] |> List.sort_uniq compare in
  let facts =
    List.filter
      (fun (name, _) -> if String.starts_with ~prefix:"IH" name then false else true)
      facts
  in
  let facts =
    List.filter (fun (_, fact) -> is_concerned fact (List.map fst free_var)) facts
  in
  facts
;;

let rec find_all_subtree expr =
  let rec find_all_subtree_from_root expr =
    match expr.Ir.desc with
    | Var name -> [ { desc = Sub_Var name; typ = expr.typ } ]
    | Call (name, args) ->
      if List.is_empty args
      then [ { desc = Sub_Call (name, []); typ = expr.typ } ]
      else (
        let args_subtree = List.map (fun arg -> find_all_subtree_from_root arg) args in
        let args_cand =
          List.fold_left
            (fun acc nth_arg_cand ->
               List.map
                 (fun pre_args ->
                    List.map (fun arg -> pre_args @ [ Some arg ]) nth_arg_cand
                    @ [ pre_args @ [ None ] ])
                 acc
               |> List.concat)
            ((args_subtree |> List.hd |> List.map (fun arg -> [ Some arg ]))
             @ [ [ None ] ])
            (args_subtree |> List.tl)
        in
        List.map (fun args -> { desc = Sub_Call (name, args); typ = expr.typ }) args_cand)
    | _ -> []
  in
  let root_subtree = find_all_subtree_from_root expr in
  let sub_subtree =
    match expr.Ir.desc with
    | Var _ -> find_all_subtree_from_root expr
    | Call (_, args) -> List.map (fun arg -> find_all_subtree arg) args |> List.concat
    | _ -> []
  in
  root_subtree @ sub_subtree |> List.sort_uniq compare
;;

let subtree_height subtree =
  let rec subtree_height_from_root subtree =
    match subtree.desc with
    | Sub_Var _ -> 1
    | Sub_Call (_, args) ->
      List.map
        (fun arg ->
           match arg with
           | Some arg -> subtree_height_from_root arg
           | None -> 0)
        args
      |> List.fold_left max 0
      |> ( + ) 1
  in
  subtree_height_from_root subtree
;;

let find_larget_common_subtree expr1 expr2 =
  let subtree_list1 = find_all_subtree expr1 in
  let subtree_list2 = find_all_subtree expr2 in
  let common_subtree =
    List.filter (fun subtree -> List.mem subtree subtree_list2) subtree_list1
  in
  let largest_common_subtree =
    List.fold_left
      (fun max subtree ->
         if subtree_height max > subtree_height subtree then max else subtree)
      (List.hd common_subtree)
      (List.tl common_subtree)
    (* None is less than Var *)
  in
  largest_common_subtree
;;

let rec is_included subtree1 subtree2 =
  match subtree2.desc with
  | Sub_Var _ -> subtree1 = subtree2
  | Sub_Call (_, args) ->
    subtree1 = subtree2
    || List.exists
         (fun arg ->
            match arg with
            | Some arg -> is_included subtree1 arg
            | None -> true
            (* have to check type *))
         args
;;

let catch_recursive_pattern expr_list =
  let range = Proof.range 0 (List.length expr_list - 1) in
  let common_subtree_list =
    List.map
      (fun i ->
         let expr1 = List.nth expr_list i in
         let expr2 = List.nth expr_list (i + 1) in
         find_larget_common_subtree expr1 expr2)
      range
  in
  let range = Proof.range 0 (List.length common_subtree_list - 1) in
  if
    List.exists
      (fun i ->
         let subtree1 = List.nth common_subtree_list i in
         let subtree2 = List.nth common_subtree_list (i + 1) in
         not (is_included subtree1 subtree2))
      range
  then []
  else common_subtree_list
;;

let pattern_recognition state_list : lemma =
  let goals = List.map snd state_list in
  let lhs_list = List.map (fun goal -> Proof.get_lhs goal) goals in
  let rhs_list = List.map (fun goal -> Proof.get_rhs goal) goals in
  let lhs_common_subtree = catch_recursive_pattern lhs_list in
  let rhs_common_subtree = catch_recursive_pattern rhs_list in
  let _ =
    lhs_common_subtree |> List.iter (fun subtree -> pp_subtree subtree |> print_endline)
  in
  let _ =
    rhs_common_subtree |> List.iter (fun subtree -> pp_subtree subtree |> print_endline)
  in
  Proof.Type Ir.Tany
;;

let symbolic_execution env t : state list list =
  let state = Proof.get_first_state t in
  let facts, goal = state in
  let facts = filtering_concerned_fact facts goal in
  let base_hypothesis = [ facts, goal ] in
  let rec symbolic_execution_by_depth env t depth (acc : state list) : state list list =
    if depth = 0
    then [ acc ]
    else (
      let state = Proof.get_first_state t in
      let lemma_stack = Proof.get_lemma_stack t in
      let facts, goal = state in
      let vars = collect_free_var_in_prop goal [] in
      let vars =
        List.filter (fun (var, _) -> Prover.is_decreasing_var env state var) vars
      in
      if List.is_empty vars
      then [ acc ]
      else (
        let new_goal = Proof.Forall ([ List.hd vars ], goal) in
        let facts = filtering_concerned_fact facts new_goal in
        let dummy_goal = Proof.Type Ir.Tany in
        let new_conj = [ facts, new_goal ], dummy_goal in
        let new_t =
          Proof.(
            create_t
              ~proof:(lemma_stack, [ new_conj ], Proof.get_tactic_history t)
              ~counter:t.counter
              ())
        in
        let vars = List.map fst vars in
        let induction_tactic = Proof.Induction (List.hd vars) in
        let new_t = Proof.apply_tactic new_t env induction_tactic in
        let new_t_list = progress_with_split env new_t in
        let new_states =
          List.map
            (fun t ->
               let states, _ = Proof.get_conj_list t |> List.hd in
               states |> List.hd)
            new_t_list
        in
        let new_accs = List.map (fun state -> acc @ [ state ]) new_states in
        let result =
          List.map2
            (fun t new_acc -> symbolic_execution_by_depth env t (depth - 1) new_acc)
            new_t_list
            new_accs
        in
        List.concat result))
  in
  symbolic_execution_by_depth env t 2 base_hypothesis
;;

let naive_generalize env (goal : Proof.goal) t : lemma list =
  let goal = Proof.simplify_prop env goal in
  let trivial =
    match goal with
    | Proof.Forall (_, _) -> true
    | Proof.Eq (lhs, rhs) -> lhs = rhs
    | Proof.Imply (_, Forall (_, _)) -> true
    | Proof.Imply (_, Eq (lhs, rhs)) -> lhs = rhs
    | _ -> false
  in
  match trivial with
  | true -> []
  | _ ->
    let _ = print_endline "*******" in
    let _ =
      symbolic_execution env t
      |> List.iter (fun state_list ->
        let _ = print_endline "state_list" in
        let _ =
          state_list |> List.iter (fun (_, goal) -> Proof.pp_prop goal |> print_endline)
        in
        let _ = state_list |> pattern_recognition in
        ())
    in
    let _ = print_endline "*******" in
    let t = Proof.(create_t ~proof:t.proof ~counter:t.counter ()) in
    let just_generalize_var =
      collect_free_var_in_prop goal [] |> List.sort_uniq compare
    in
    let facts = Proof.get_first_state t |> fst in
    let facts = filtering_concerned_fact facts goal in
    let facts = List.map snd facts in
    let facts = List.map Proof.rename_prop facts in
    let just_generalize_new_goal =
      if List.is_empty just_generalize_var
      then []
      else if List.is_empty facts
      then [ Proof.Forall (just_generalize_var, goal) ]
      else [ Proof.Forall (just_generalize_var, Proof.Imply (facts, goal)) ]
    in
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
    let new_facts_list =
      List.map2
        (fun subterm var ->
           List.map
             (fun fact ->
                let new_fact, _, _ =
                  Proof.substitute_expr_in_prop
                    Ir.is_equal_expr
                    (fun _ _ expr_to -> expr_to, [])
                    fact
                    subterm
                    var
                    0
                in
                new_fact)
             facts)
        common_subterm
        new_qvars
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
    let new_facts_list =
      List.map2
        (fun facts qvars ->
           List.filter (fun fact -> is_concerned fact (List.map fst qvars)) facts)
        new_facts_list
        qvars_list
    in
    let new_state = List.combine new_facts_list new_goals in
    just_generalize_new_goal
    @ List.fold_left2
        (fun acc qvars (new_facts, new_goal) ->
           if List.is_empty qvars
           then acc
           else if List.is_empty new_facts
           then Proof.Forall (qvars, new_goal) :: acc
           else Proof.Forall (qvars, Proof.Imply (new_facts, new_goal)) :: acc)
        []
        qvars_list
        new_state
;;

let make_lemmas (env : env) (stuck_list : Prover.ProofSet.t) lemma_list : (t * lemma) list
  =
  let lemmas =
    List.map
      (fun t ->
         let state = Proof.get_first_state t in
         let _, goal = state in
         let lemmas = naive_generalize env goal t in
         List.map (fun lemma -> t, lemma) lemmas)
      (Prover.ProofSet.to_list stuck_list)
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
  let lemmas =
    List.filter
      (fun (_, lemma) ->
         not (List.exists (fun (_, old_lemma) -> old_lemma = lemma) lemma_list))
      lemmas
  in
  let _ = lemmas |> List.iter (fun (_, lemma) -> Proof.pp_prop lemma |> print_endline) in
  lemmas
;;
