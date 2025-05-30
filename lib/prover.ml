type t = Proof.t
type env = Proof.env
type state = Proof.state
type lemma_stack = Proof.lemma_stack
type tactic = Proof.tactic
type expr = Proof.expr
type graph = Egraph.L.op Egraph.Egraph.t

module WorkList = CCHeap.Make_from_compare (struct
    type t = Proof.t * tactic * Proof.t * int * int

    let compare (t1, _, _, r1, ord1) (t2, _, _, r2, ord2) =
      let conjs1 = Proof.get_conj_list t1 |> List.length in
      let conjs2 = Proof.get_conj_list t2 |> List.length in
      let goals1 = Proof.get_goal_list t1 |> List.length in
      let goals2 = Proof.get_goal_list t2 |> List.length in
      if r1 = r2
      then
        if conjs1 = conjs2
        then if goals1 = goals2 then compare ord1 ord2 else compare goals1 goals2
        else compare conjs1 conjs2
      else compare r1 r2
    ;;
  end)

module ProofSet = CCSet.Make (struct
    type t = Proof.t

    let compare = compare
  end)

let make_order_counter () =
  let count = ref 0 in
  fun () ->
    incr count;
    !count
;;

let rec split pred lst =
  match lst with
  | [] -> [], []
  | hd :: tl ->
    if pred hd
    then (
      let a, b = split pred tl in
      hd :: a, b)
    else (
      let a, b = split pred tl in
      a, hd :: b)
;;

let order_counter = make_order_counter ()

let rec is_sub_list pred lst1 lst2 =
  match lst1, lst2 with
  | hd1 :: tl1, hd2 :: tl2 -> if pred hd1 hd2 then is_sub_list pred tl1 tl2 else false
  | [], _ -> true
  | _, [] -> false
;;

let is_sub_t t1 t2 =
  let conjs1 = Proof.get_conj_list t1 in
  let conjs2 = Proof.get_conj_list t2 in
  let state_list1 = List.map fst conjs1 |> List.concat in
  let state_list2 = List.map fst conjs2 |> List.concat in
  let state_list1 = List.map (fun (fact_list, goal, _) -> fact_list, goal) state_list1 in
  let state_list2 = List.map (fun (fact_list, goal, _) -> fact_list, goal) state_list2 in
  is_sub_list
    (fun (fact_list1, goal1) (fact_list2, goal2) ->
       Proof.compare_fact_list fact_list1 fact_list2 && goal1 = goal2)
    (List.rev state_list1)
    (List.rev state_list2)
;;

let deduplicate_worklist worklist t =
  let len1 = WorkList.size worklist in
  let worklist =
    WorkList.filter (fun (proof_t, _, _, _, _) -> not (is_sub_t t proof_t)) worklist
  in
  let len2 = WorkList.size worklist in
  let _ = print_endline ("Deduplication: " ^ string_of_int (len1 - len2)) in
  worklist
;;

let rec collect_fname_in_expr env expr =
  match expr.Ir.desc with
  | Ir.Call (name, args) ->
    let decl = Ir.find_decl name env in
    let acc =
      match decl with
      | Some (Ir.Rec _) -> [ name ]
      | _ -> []
    in
    List.fold_left (fun acc arg -> acc @ collect_fname_in_expr env arg) acc args
  | Ir.Var _ -> []
  | Ir.LetIn (assign_list, body) ->
    List.fold_left
      (fun acc (_, exp) -> acc @ collect_fname_in_expr env exp)
      []
      assign_list
    @ collect_fname_in_expr env body
  | Ir.Match (_, case_list) ->
    (* List.fold_left (fun acc exp -> acc @ collect_fname_in_expr env exp) [] match_list
    @  *)
    List.fold_left
      (fun acc case ->
         match case with
         | Ir.Case (_, exp) -> acc @ collect_fname_in_expr env exp)
      []
      case_list
;;

let rec collect_fname_in_prop env goal =
  match goal with
  | Proof.Forall (_, prop) -> collect_fname_in_prop env prop
  | Proof.Eq (lhs, rhs) | Proof.Le (lhs, rhs) | Proof.Lt (lhs, rhs) ->
    collect_fname_in_expr env lhs @ collect_fname_in_expr env rhs
  | Proof.Or (lhs, rhs) -> collect_fname_in_prop env lhs @ collect_fname_in_prop env rhs
  | Proof.Not prop -> collect_fname_in_prop env prop
  | Proof.Imply (cond_list, prop) ->
    List.fold_left (fun acc cond -> acc @ collect_fname_in_prop env cond) [] cond_list
    @ collect_fname_in_prop env prop
  | _ -> []
;;

let rec collect_var_in_prop prop =
  match prop with
  | Proof.Forall (_, prop) -> collect_var_in_prop prop
  | Proof.Eq (lhs, rhs) | Proof.Le (lhs, rhs) | Proof.Lt (lhs, rhs) ->
    Ir.collect_var_in_expr lhs @ Ir.collect_var_in_expr rhs
  | Proof.And (lhs, rhs) | Proof.Or (lhs, rhs) ->
    collect_var_in_prop lhs @ collect_var_in_prop rhs
  | Proof.Not prop -> collect_var_in_prop prop
  | Proof.Imply (cond_list, prop) ->
    List.fold_left (fun acc cond -> acc @ collect_var_in_prop cond) [] cond_list
    @ collect_var_in_prop prop
  | _ -> []
;;

let get_decreasing_arg_index env fname =
  let fun_decl = Ir.find_decl fname env |> Option.get in
  let args, fun_expr =
    match fun_decl with
    | Ir.NonRec (_, args, fun_expr) -> args, fun_expr
    | Ir.Rec (_, args, fun_expr) -> args, fun_expr
    | _ -> failwith "Not a function declaration"
  in
  match fun_expr.desc with
  | Ir.Match (match_list, _) ->
    List.fold_left
      (fun acc arg ->
         if
           List.exists
             (fun exp ->
                match exp.Ir.desc with
                | Ir.Var v -> v = arg
                | _ -> false)
             match_list
         then acc @ [ List.find_index (fun a -> a = arg) args |> Option.get ]
         else acc)
      []
      args
  | _ -> []
;;

let rec get_nth_arg_in_expr fname i expr =
  match expr.Ir.desc with
  | Ir.Call (name, args) ->
    if name = fname
    then [ List.nth args i ]
    else List.fold_left (fun acc exp -> acc @ get_nth_arg_in_expr fname i exp) [] args
  | Ir.Var _ -> []
  | Ir.LetIn (assign_list, body) ->
    List.fold_left
      (fun acc (_, exp) -> acc @ get_nth_arg_in_expr fname i exp)
      []
      assign_list
    @ get_nth_arg_in_expr fname i body
  | Ir.Match (match_list, case_list) ->
    List.fold_left (fun acc exp -> acc @ get_nth_arg_in_expr fname i exp) [] match_list
    @ List.fold_left
        (fun acc case ->
           match case with
           | Ir.Case (_, exp) -> acc @ get_nth_arg_in_expr fname i exp)
        []
        case_list
;;

let rec get_nth_arg_in_prop fname i prop =
  match prop with
  | Proof.Forall (_, prop) -> get_nth_arg_in_prop fname i prop
  | Proof.Eq (lhs, rhs) ->
    get_nth_arg_in_expr fname i lhs @ get_nth_arg_in_expr fname i rhs
  | Proof.Le (lhs, rhs) ->
    get_nth_arg_in_expr fname i lhs @ get_nth_arg_in_expr fname i rhs
  | Proof.Lt (lhs, rhs) ->
    get_nth_arg_in_expr fname i lhs @ get_nth_arg_in_expr fname i rhs
  | Proof.And (lhs, rhs) ->
    get_nth_arg_in_prop fname i lhs @ get_nth_arg_in_prop fname i rhs
  | Proof.Or (lhs, rhs) ->
    get_nth_arg_in_prop fname i lhs @ get_nth_arg_in_prop fname i rhs
  | Proof.Not prop -> get_nth_arg_in_prop fname i prop
  | Proof.Imply (cond_list, prop) ->
    List.fold_left (fun acc cond -> acc @ get_nth_arg_in_prop fname i cond) [] cond_list
    @ get_nth_arg_in_prop fname i prop
  | _ -> []
;;

let collect_decreasing_arg env state =
  let _, goal, _ = state in
  let fname_list = collect_fname_in_prop env goal in
  List.fold_left
    (fun acc fname ->
       let arg_index_list = get_decreasing_arg_index env fname in
       List.fold_left
         (fun acc arg_index ->
            let arg_list = get_nth_arg_in_prop fname arg_index goal in
            acc @ arg_list)
         acc
         arg_index_list)
    []
    fname_list
  |> List.fold_left
       (fun acc arg ->
          match arg.Ir.desc with
          | Ir.Var v -> v :: acc
          | _ -> acc)
       []
;;

let is_decreasing_var env (state : state) var_name =
  let _, goal, _ = state in
  let fname_list = collect_fname_in_prop env goal in
  List.exists
    (fun fname ->
       let arg_index_list = get_decreasing_arg_index env fname in
       List.exists
         (fun arg_index ->
            let arg_list = get_nth_arg_in_prop fname arg_index goal in
            List.exists
              (fun arg ->
                 match arg.Ir.desc with
                 | Ir.Var v -> v = var_name
                 | _ -> false)
              arg_list)
         arg_index_list)
    fname_list
;;

let is_mk (state : state) var_name =
  let _, goal, _ = state in
  let lhs = Proof.get_lhs goal in
  let rhs = Proof.get_rhs goal in
  let rec is_mk_arg expr =
    match expr.Ir.desc with
    | Ir.Call (name, args) ->
      if String.starts_with ~prefix:"mk" name
      then
        List.exists
          (fun arg ->
             match arg.Ir.desc with
             | Ir.Var var -> var = var_name
             | _ -> false)
          args
      else List.exists is_mk_arg args
    | _ -> false
  in
  is_mk_arg lhs || is_mk_arg rhs
;;

let apply_tactic t tactic : t option =
  (* this function prune fact conversion *)
  try
    let next_t = Proof.apply_tactic t tactic in
    let _, goal, _ = Proof.get_first_state t in
    try
      let _, next_goal, _ = Proof.get_first_state next_t in
      if goal = next_goal then None else Some next_t
    with
    | _ -> Some next_t
  with
  | _ -> None
;;

let is_duplicated new_t state_list =
  let lemma_stack = Proof.get_lemma_stack new_t in
  let next_conj = Proof.get_conj_list new_t in
  ProofSet.exists
    (fun old_t ->
       let lemma_stack' = Proof.get_lemma_stack old_t in
       let conj_list = Proof.get_conj_list old_t in
       lemma_stack = lemma_stack' && List.for_all2 Proof.compare_conj next_conj conj_list)
    state_list
;;

let rec collect_expr_in_expr expr =
  match expr.Ir.desc with
  | Ir.Call (_, args) ->
    List.fold_left (fun acc arg -> acc @ collect_expr_in_expr arg) [ expr ] args
  | Ir.Var _ -> [ expr ]
  | Ir.LetIn (assign_list, body) ->
    List.fold_left
      (fun acc (_, exp) -> acc @ collect_expr_in_expr exp)
      [ expr ]
      assign_list
    @ collect_expr_in_expr body
  | Ir.Match (match_list, case_list) ->
    List.fold_left (fun acc exp -> acc @ collect_expr_in_expr exp) [ expr ] match_list
    @ List.fold_left
        (fun acc case ->
           match case with
           | Ir.Case (_, exp) -> acc @ collect_expr_in_expr exp)
        [ expr ]
        case_list
;;

let rec collect_expr_in_prop prop =
  match prop with
  | Proof.Forall (_, prop) -> collect_expr_in_prop prop
  | Proof.Eq (lhs, rhs) | Proof.Le (lhs, rhs) | Proof.Lt (lhs, rhs) ->
    collect_expr_in_expr lhs @ collect_expr_in_expr rhs
  | Proof.And (lhs, rhs) | Proof.Or (lhs, rhs) ->
    collect_expr_in_prop lhs @ collect_expr_in_prop rhs
  | Proof.Not prop -> collect_expr_in_prop prop
  | Proof.Imply (cond_list, prop) ->
    List.fold_left (fun acc cond -> acc @ collect_expr_in_prop cond) [] cond_list
    @ collect_expr_in_prop prop
  | _ -> []
;;

let collect_qvar_in_prop prop =
  match prop with
  | Proof.Forall (var_name, _) -> List.map fst var_name
  | _ -> []
;;

let rec collect_non_qvar_in_expr expr qvar_list =
  match expr.Ir.desc with
  | Ir.Var v -> if List.mem v qvar_list then [] else [ v ]
  | Ir.Call (_, args) ->
    List.fold_left (fun acc arg -> acc @ collect_non_qvar_in_expr arg qvar_list) [] args
  | Ir.LetIn (assign_list, body) ->
    List.fold_left
      (fun acc (_, exp) -> acc @ collect_non_qvar_in_expr exp qvar_list)
      []
      assign_list
    @ collect_non_qvar_in_expr body qvar_list
  | Ir.Match (match_list, case_list) ->
    List.fold_left
      (fun acc exp -> acc @ collect_non_qvar_in_expr exp qvar_list)
      []
      match_list
    @ List.fold_left
        (fun acc case ->
           match case with
           | Ir.Case (_, exp) -> acc @ collect_non_qvar_in_expr exp qvar_list)
        []
        case_list
;;

let collect_non_qvar_in_prop prop =
  let rec collect_non_qvar_in_prop' prop qvar_list =
    match prop with
    | Proof.Forall (var_name, prop) ->
      let var_name = List.map fst var_name in
      collect_non_qvar_in_prop' prop (qvar_list @ var_name)
    | Proof.Eq (lhs, rhs) | Proof.Le (lhs, rhs) | Proof.Lt (lhs, rhs) ->
      List.fold_left
        (fun acc exp -> acc @ collect_non_qvar_in_expr exp qvar_list)
        []
        [ lhs; rhs ]
    | Proof.And (lhs, rhs) | Proof.Or (lhs, rhs) ->
      List.fold_left
        (fun acc prop -> acc @ collect_non_qvar_in_prop' prop qvar_list)
        []
        [ lhs; rhs ]
    | Proof.Not prop -> collect_non_qvar_in_prop' prop qvar_list
    | Proof.Imply (cond_list, prop) ->
      List.fold_left
        (fun acc cond -> acc @ collect_non_qvar_in_prop' cond qvar_list)
        []
        cond_list
      @ collect_non_qvar_in_prop' prop qvar_list
    | _ -> qvar_list
  in
  collect_non_qvar_in_prop' prop []
;;

let collect_fact_name (state : state) =
  let fact_list, _, _ = state in
  List.fold_left
    (fun acc (name, fact) ->
       match fact with
       | Proof.Type _ -> acc
       | _ -> acc @ [ name ])
    []
    fact_list
;;

let collect_lemma_name (lemma_stack : lemma_stack) =
  List.fold_left (fun acc (name, _) -> acc @ [ name ]) [] lemma_stack
;;

let mk_candidates t =
  let lemma_stack = Proof.get_lemma_stack t in
  let state = Proof.get_first_state t in
  let _, goal, _ = state in
  let number_list = [ 0; 1; 2; 3 ] in
  let expr_list = collect_expr_in_prop goal |> List.sort_uniq compare in
  let qvar_list = collect_qvar_in_prop goal |> List.sort_uniq compare in
  let non_qvar_list = collect_non_qvar_in_prop goal |> List.sort_uniq compare in
  let fact_name_list = collect_fact_name state |> List.sort_uniq compare in
  let lemma_name_list = collect_lemma_name lemma_stack |> List.sort_uniq compare in
  let intro_list = List.map (fun v -> Proof.mk_intro v) qvar_list in
  let intro_list =
    match goal with
    | Proof.Imply (_, _) ->
      intro_list @ [ Proof.mk_intro ("Cond" ^ string_of_int (Proof.fact_index t "Cond")) ]
    | _ -> intro_list
  in
  let induction_list = List.map (fun v -> Proof.mk_induction v) qvar_list in
  let strong_induction_list = List.map (fun v -> Proof.mk_strong_induction v) qvar_list in
  let simpl_in_list =
    List.map (fun v -> Proof.mk_simpl_in v) (fact_name_list @ [ "goal" ])
  in
  let src_list = fact_name_list @ lemma_name_list in
  let target_list = fact_name_list @ [ "goal" ] in
  let rewrite_list =
    List.map
      (fun src ->
         List.map
           (fun target ->
              List.map (fun i -> Proof.mk_rewrite_in_at src target i) number_list)
           target_list)
      src_list
    |> List.concat
    |> List.concat
  in
  let rewrite_reverse_list =
    List.map
      (fun src ->
         List.map
           (fun target ->
              List.map (fun i -> Proof.mk_rewrite_reverse src target i) number_list)
           target_list)
      src_list
    |> List.concat
    |> List.concat
  in
  let destruct_list = List.map (fun v -> Proof.mk_destruct v) non_qvar_list in
  let case_list = List.map (fun v -> Proof.mk_case v) expr_list in
  intro_list
  @ induction_list
  @ strong_induction_list
  @ simpl_in_list
  @ rewrite_list
  @ rewrite_reverse_list
  @ destruct_list
  @ case_list
  @ [ Proof.mk_reflexivity; Proof.mk_discriminate ]
;;

let cost_insert = 1
let cost_delete = 1
let cost_substitute = 1

let edit_distance str1 str2 =
  let len1 = String.length str1 in
  let len2 = String.length str2 in
  let dp = Array.make_matrix (len1 + 1) (len2 + 1) 0 in
  (* 초기화 *)
  for i = 0 to len1 do
    dp.(i).(0) <- i
  done;
  for j = 0 to len2 do
    dp.(0).(j) <- j
  done;
  (* DP 테이블 채우기 *)
  for i = 1 to len1 do
    for j = 1 to len2 do
      if str1.[i - 1] = str2.[j - 1]
      then dp.(i).(j) <- dp.(i - 1).(j - 1) (* 같으면 교체가 필요 없음 *)
      else
        dp.(i).(j)
        <- min
             (dp.(i - 1).(j) + 1) (* 삭제 *)
             (min (dp.(i).(j - 1) + 1) (* 삽입 *) (dp.(i - 1).(j - 1) + 1))
        (* 교체 *)
    done
  done;
  dp.(len1).(len2)
;;

let get_difference expr1 expr2 = edit_distance (Proof.pp_expr expr1) (Proof.pp_expr expr2)

let rec get_both_hand prop =
  match prop with
  | Proof.Eq (lhs, rhs) -> lhs, rhs
  | Proof.Forall (_, prop) -> get_both_hand prop
  | Proof.Imply (_, prop) -> get_both_hand prop
  | _ -> failwith ("Not an equation : " ^ Proof.pp_prop prop)
;;

let is_more_similar prop1 prop2 =
  let lhs1, rhs1 = get_both_hand prop1 in
  let lhs2, rhs2 = get_both_hand prop2 in
  let prev_difference = get_difference lhs1 rhs1 in
  let next_difference = get_difference lhs2 rhs2 in
  prev_difference > next_difference
;;

let how_good_rewrite (prev_t : t) (new_t : t) : int option =
  let prev_state = Proof.get_first_state prev_t in
  let new_state = Proof.get_first_state new_t in
  let _, prev_goal, _ = prev_state in
  let _, new_goal, _ = new_state in
  match is_more_similar prev_goal new_goal with
  | true -> Some 1
  | false -> None
;;

let rec is_if_then_else_in_expr src expr =
  match expr.Ir.desc with
  | Ir.Match (match_list, case_list) ->
    (match match_list with
     | [ e1 ] ->
       (match e1.typ, case_list with
        | ( Talgebraic ("bool", [])
          , [ Ir.Case (Pat_Constr ("true", []), _); Case (Pat_Constr ("false", []), _) ] )
          -> src = e1
        | _ ->
          List.exists (fun exp -> is_if_then_else_in_expr src exp) match_list
          || List.exists
               (fun case ->
                  match case with
                  | Ir.Case (_, exp) -> is_if_then_else_in_expr src exp)
               case_list)
     | _ ->
       List.exists (fun exp -> is_if_then_else_in_expr src exp) match_list
       || List.exists
            (fun case ->
               match case with
               | Ir.Case (_, exp) -> is_if_then_else_in_expr src exp)
            case_list)
  | Ir.LetIn (assign_list, body) ->
    List.exists (fun (_, exp) -> is_if_then_else_in_expr src exp) assign_list
    || is_if_then_else_in_expr src body
  | Ir.Call (_, args) -> List.exists (fun arg -> is_if_then_else_in_expr src arg) args
  | Ir.Var _ -> false
;;

let rec is_if_then_else_in_prop src goal =
  match goal with
  | Proof.Eq (lhs, rhs) | Proof.Le (lhs, rhs) | Proof.Lt (lhs, rhs) ->
    is_if_then_else_in_expr src lhs || is_if_then_else_in_expr src rhs
  | Proof.Or (lhs, rhs) ->
    is_if_then_else_in_prop src lhs || is_if_then_else_in_prop src rhs
  | Proof.Not prop -> is_if_then_else_in_prop src prop
  | Proof.Imply (cond_list, prop) ->
    List.exists (fun cond -> is_if_then_else_in_prop src cond) cond_list
    || is_if_then_else_in_prop src prop
  | _ -> false
;;

let rec is_case_match_in_expr src expr =
  match expr.Ir.desc with
  | Ir.Match (match_list, case_list) ->
    (match match_list with
     | [ e1 ] -> e1 = src
     | _ ->
       List.exists (fun exp -> is_case_match_in_expr src exp) match_list
       || List.exists
            (fun case ->
               match case with
               | Ir.Case (_, exp) -> is_case_match_in_expr src exp)
            case_list)
  | Ir.LetIn (assign_list, body) ->
    List.exists (fun (_, exp) -> is_case_match_in_expr src exp) assign_list
    || is_case_match_in_expr src body
  | Ir.Call (_, args) -> List.exists (fun arg -> is_case_match_in_expr src arg) args
  | Ir.Var _ -> false
;;

let rec is_case_match src goal =
  match goal with
  | Proof.Eq (lhs, rhs) | Proof.Le (lhs, rhs) | Proof.Lt (lhs, rhs) ->
    is_case_match_in_expr src lhs || is_case_match_in_expr src rhs
  | Proof.Or (lhs, rhs) -> is_case_match src lhs || is_case_match src rhs
  | Proof.Not prop -> is_case_match src prop
  | Proof.Imply (cond_list, prop) ->
    List.exists (fun cond -> is_case_match src cond) cond_list || is_case_match src prop
  | _ -> false
;;

let useless_rewrite tactic =
  match tactic with
  | Proof.RewriteInAt (src, target, _) ->
    src = target
    || String.starts_with ~prefix:"Inductive" src
    || String.starts_with ~prefix:"Inductive" target
    || String.starts_with ~prefix:"Base" src
    || String.starts_with ~prefix:"Base" target
    (* || String.starts_with ~prefix:"IH" target *)
  | Proof.RewriteReverse (src, target, _) ->
    src = target
    || String.starts_with ~prefix:"Inductive" src
    || String.starts_with ~prefix:"Inductive" target
    || String.starts_with ~prefix:"Base" src
    || String.starts_with ~prefix:"Base" target
    (* || String.starts_with ~prefix:"IH" target *)
    || (String.starts_with ~prefix:"Case" src && String.starts_with ~prefix:"goal" target)
  | _ -> false
;;

let rank_tactic t tactic next_t valid_tactics real_tactics stateset : int option =
  (* this function be executed after is_valid, is_duplicated *)
  ignore real_tactics;
  let env = t.Proof.env in
  let state = Proof.get_first_state t in
  let _, goal, _ = state in
  let decreasing_vars = collect_decreasing_arg env state in
  let all_vars = collect_var_in_prop goal in
  let non_decreasing_vars =
    List.filter (fun v -> not (List.mem v decreasing_vars)) all_vars
  in
  let qvar_list = collect_qvar_in_prop goal in
  match tactic with
  | Proof.Intro var_name ->
    if
      List.exists (fun tactic -> tactic = Proof.SimplIn "goal") valid_tactics
      || List.exists
           (fun tactic ->
              match tactic with
              | Proof.Induction v -> v <> var_name
              | _ -> false)
           real_tactics
    then None
    else if is_mk state var_name
    then (
      let qvar_list = List.filter (fun v -> v <> var_name) qvar_list in
      if List.exists (fun qvar -> List.mem qvar decreasing_vars) qvar_list
      then if List.mem var_name non_decreasing_vars then Some 3 else None
      else Some 2)
    else if List.exists (fun var -> var = var_name) decreasing_vars
    then None
    else Some 1
  | Proof.Induction var_name ->
    if List.exists (fun tactic -> tactic = Proof.SimplIn "goal") valid_tactics
    then None
    else if not (List.exists (fun var -> var = var_name) decreasing_vars)
    then None
    else if is_mk state var_name
    then (
      let qvar_list = List.filter (fun v -> v <> var_name) qvar_list in
      if
        List.exists
          (fun qvar -> List.exists (fun var -> var = qvar) decreasing_vars)
          qvar_list
      then None
      else Some 2)
    else Some 0
  | Proof.SimplIn "goal" -> Some 0
  | Proof.SimplIn _ -> None
  | Proof.RewriteInAt (src, target, _) ->
    if String.starts_with ~prefix:"Case" src && String.starts_with ~prefix:"Case" target
    then (
      match apply_tactic next_t Proof.Discriminate with
      | Some _ -> Some 0
      | _ -> None)
    else if String.starts_with ~prefix:"lhs" src || String.starts_with ~prefix:"rhs" src
    then None
    else (
      let _, goal, _ = Proof.get_first_state t in
      let _, new_goal, _ = Proof.get_first_state next_t in
      if is_more_similar goal new_goal then Some 1 else Some 2)
  | Proof.RewriteReverse (src, target, _) ->
    if String.starts_with ~prefix:"Case" src && String.starts_with ~prefix:"Case" target
    then (
      match apply_tactic next_t Proof.Discriminate with
      | Some _ -> Some 0
      | _ -> None)
    else (
      let _, goal, _ = Proof.get_first_state t in
      let _, new_goal, _ = Proof.get_first_state next_t in
      let lhs = Proof.get_lhs goal in
      let rhs = Proof.get_rhs goal in
      let new_lhs = Proof.get_lhs new_goal in
      let new_rhs = Proof.get_rhs new_goal in
      if
        (new_lhs <> lhs && String.starts_with ~prefix:"rhs" src)
        || (new_rhs <> rhs && String.starts_with ~prefix:"lhs" src)
      then None
      else if is_more_similar goal new_goal
      then Some 1
      else Some 2)
  | Proof.Destruct _ -> None
  | Proof.Case expr ->
    (match expr.Ir.desc with
     | Var _ -> None
     | _ ->
       let _, goal, _ = state in
       if List.exists (fun tactic -> tactic = Proof.SimplIn "goal") valid_tactics
       then None
       else if is_if_then_else_in_prop expr goal
       then Some 2
       else if
         let new_t = Proof.apply_tactic next_t (Proof.SimplIn "goal") in
         is_case_match expr goal && not (is_duplicated new_t stateset)
       then Some 3
       else None)
  | Proof.Reflexivity -> Some 0
  | Proof.Discriminate -> Some 0
  | _ -> None
;;

let rank_tactics t valid_tactics (new_worklist : (tactic * t) list) stateset
  : (t * tactic * t * int * int) list
  =
  let trivial, non_trivial =
    split
      (fun (tactic, _) ->
         match tactic with
         | Proof.Reflexivity | Proof.Discriminate -> true
         | _ -> false)
      new_worklist
  in
  let real_tactic = List.map fst non_trivial in
  match trivial with
  | [] ->
    let worklist =
      List.fold_left
        (fun acc (tactic, next_t) ->
           let r = rank_tactic t tactic next_t valid_tactics real_tactic stateset in
           match r with
           | Some r -> acc @ [ t, tactic, next_t, r, order_counter () ]
           | _ -> acc)
        []
        non_trivial
    in
    if
      List.for_all
        (fun (_, tactic, _, _, _) ->
           match tactic with
           | Proof.Case _ -> true
           | _ -> false)
        worklist
    then List.map (fun (t, tactic, next_t, _, ord) -> t, tactic, next_t, 0, ord) worklist
    else worklist
  | (tactic, next_t) :: _ -> [ t, tactic, next_t, 0, order_counter () ]
;;

let prune_rank_worklist_update_state_list t candidates statelist =
  let candidates = List.filter (fun c -> not (useless_rewrite c)) candidates in
  let new_worklist =
    List.fold_left
      (fun acc tactic ->
         match apply_tactic t tactic with
         | Some next_t -> acc @ [ tactic, next_t ]
         | None -> acc)
      []
      candidates
  in
  let valid_tactics = List.map fst new_worklist in
  let new_worklist, statelist =
    List.fold_left
      (fun (worklist, state_list) (tactic, next_t) ->
         if is_duplicated next_t state_list
         then worklist, state_list
         else worklist @ [ tactic, next_t ], ProofSet.add next_t state_list)
      ([], statelist)
      new_worklist
  in
  let worklist = rank_tactics t valid_tactics new_worklist statelist in
  WorkList.of_list worklist, statelist
;;

let is_stuck worklist = WorkList.is_empty worklist
