open Sexplib.Std

type t = Proof.t
type env = Proof.env
type state = Proof.state
type lemma_stack = Proof.lemma_stack
type lemma = Proof.goal
type expr = Proof.expr

type subtree =
  { desc : sub_desc option
  ; typ : Ir.typ
  }
[@@deriving sexp]

and sub_desc =
  | Sub_Var of string
  | Sub_Call of string * subtree list
[@@deriving sexp]

let rec to_sub expr =
  match expr.Ir.desc with
  | Var name -> { desc = Some (Sub_Var name); typ = expr.typ }
  | Call (name, args) ->
    let args = List.map to_sub args in
    { desc = Some (Sub_Call (name, args)); typ = expr.typ }
  | _ -> { desc = None; typ = Tany }
;;

let rec pp_subtree (subtree : subtree) : string =
  match subtree.desc with
  | Some (Sub_Var name) -> name
  | Some (Sub_Call (name, args)) ->
    let args = List.map (fun arg -> pp_subtree arg) args in
    name ^ "(" ^ String.concat ", " args ^ ")"
  | None -> "_"
;;

let difference_of_subtree subtree1 subtree2 =
  (* subtree2 - subtree1 *)
  let rec difference_of_subtree subtree1 subtree2 =
    match subtree2.desc with
    | Some (Sub_Call (name, args)) ->
      if subtree1 = subtree2
      then { desc = None; typ = subtree2.typ }
      else (
        let new_args = List.map (fun arg -> difference_of_subtree subtree1 arg) args in
        { desc = Some (Sub_Call (name, new_args)); typ = subtree2.typ })
    | Some (Sub_Var _) ->
      if subtree1 = subtree2 then { desc = None; typ = subtree2.typ } else subtree2
    | None -> subtree2
  in
  difference_of_subtree subtree1 subtree2
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
  | Imply (conds, prop) ->
    let conds_vars =
      List.map (fun cond -> collect_free_var_in_prop cond binding) conds |> List.concat
    in
    let prop_vars = collect_free_var_in_prop prop binding in
    conds_vars @ prop_vars
  | _ -> []
;;

let rec collect_free_var_in_subtree (subtree : subtree) (binding : string list)
  : (string * Proof.prop) list
  =
  match subtree.desc with
  | Some (Sub_Var name) ->
    if List.mem name binding then [] else [ name, Proof.Type subtree.typ ]
  | Some (Sub_Call (_, args)) ->
    List.map (fun arg -> collect_free_var_in_subtree arg binding) args |> List.concat
  | None -> []
;;

let is_concerned fact binding =
  let free_vars = collect_free_var_in_prop fact [] in
  match fact with
  | Proof.Type _ -> false
  | _ -> List.for_all (fun (name, _) -> List.mem name binding) free_vars
;;

let filtering_concerned_fact (facts : Proof.fact list) goal =
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

let get_index_type_of_induction (env : env) (state : state) =
  let facts, _, _ = state in
  let last_induction =
    List.find
      (fun (name, _) ->
         String.starts_with ~prefix:"Inductive" name
         || String.starts_with ~prefix:"Base" name)
      (List.rev facts)
  in
  let constructor, typ =
    match last_induction with
    | _, Proof.Eq (_, expr) ->
      (match expr.Ir.desc with
       | Call (constr, _) -> Ir.Constructor constr, expr.typ
       | _ -> failwith "not implemented")
    | _ -> failwith "not implemented"
  in
  let typ_name =
    match typ with
    | Ir.Talgebraic (name, _) -> name
    | _ -> failwith "not implemented"
  in
  let typ_decl = Ir.find_decl typ_name env |> Option.get in
  match typ_decl with
  | Ir.TypeDecl (_, _, decl_list) ->
    List.find_index (fun (constr, _) -> constr = constructor) decl_list |> Option.get, typ
  | _ -> failwith "not implemented"
;;

let get_prev_tactics index (t : t) =
  let tactic = Proof.get_tactic_history t in
  let rec until_induction result tactics =
    match tactics with
    | [] -> failwith "no induction"
    | tactic :: rest ->
      (match tactic with
       | Proof.Induction _ -> result
       | _ -> until_induction (tactic :: result) rest)
  in
  let rec takeof_reflexivity n tactics =
    if n = 0
    then tactics
    else (
      match tactics with
      | [] -> []
      | tactic :: rest ->
        (match tactic with
         | Proof.Reflexivity | Discriminate -> takeof_reflexivity (n - 1) rest
         | Proof.Case _ -> takeof_reflexivity (n + 1) rest
         | _ -> takeof_reflexivity n rest))
  in
  tactic |> List.rev |> until_induction [] |> takeof_reflexivity index
;;

let make_next_step index ind_typ t : state option =
  try
    let env = t.Proof.env in
    let state = Proof.get_first_state t in
    let facts, goal, _ = state in
    let vars = collect_free_var_in_prop goal [] |> List.sort_uniq compare in
    let ind_var = List.find (fun (_, typ) -> typ = Proof.Type ind_typ) vars in
    let rest_vars =
      List.filter
        (fun (name, typ) ->
           match typ with
           | Proof.Type _ -> name <> fst ind_var
           | _ -> false)
        facts
    in
    let facts = filtering_concerned_fact facts goal in
    let facts = List.map snd facts in
    let facts = List.map Proof.rename_prop facts in
    let qvars, goal =
      match goal with
      | Proof.Forall (qvars, goal) -> qvars, goal
      | _ -> [], goal
    in
    let new_goal =
      if List.is_empty facts
      then Proof.Forall (ind_var :: qvars, goal)
      else Proof.Forall (ind_var :: qvars, Proof.Imply (facts, goal))
    in
    let lemma_stack = Proof.get_lemma_stack t in
    let dummy_goal = Proof.Type Ir.Tany in
    let new_t =
      Proof.create_t
        env
        ~proof:
          ( lemma_stack
          , [ [ rest_vars, new_goal, Proof.graph_of_prop new_goal ], dummy_goal ]
          , [] )
        ()
    in
    let new_t = Proof.apply_tactic new_t (Proof.Induction (ind_var |> fst)) in
    let conj, _ = Proof.get_conj_list new_t |> List.hd in
    let new_state = List.nth conj index in
    Some new_state
  with
  | _ -> None
;;

let fast_execution depth t : state list =
  let first_state = Proof.get_first_state t in
  let first_state =
    try Proof.apply_intro "*" first_state with
    | _ -> first_state
  in
  let index_typ_opt =
    try Some (get_index_type_of_induction t.Proof.env first_state) with
    | _ -> None
  in
  match index_typ_opt with
  | Some (index, ind_typ) ->
    let prev_tactics = get_prev_tactics index t in
    let _ = print_endline "previous tactics" in
    prev_tactics |> List.iter (fun tactic -> Proof.pp_tactic tactic |> print_endline);
    let range = Proof.range 0 depth in
    let t_of_state state =
      let lemma_stack = Proof.get_lemma_stack t in
      let tactics = Proof.get_tactic_history t in
      let dummy_goal = Proof.Type Ir.Tany in
      let new_conj = [ state ], dummy_goal in
      Proof.create_t t.Proof.env ~proof:(lemma_stack, [ new_conj ], tactics) ()
    in
    let execution_list =
      List.fold_left
        (fun (result, (t : t option)) _ ->
           match t with
           | Some t ->
             (match make_next_step index ind_typ t with
              | Some new_state ->
                (try
                   let new_t =
                     List.fold_left
                       (fun acc tactic -> Proof.apply_tactic acc tactic)
                       (new_state |> t_of_state)
                       prev_tactics
                   in
                   let new_state = Proof.get_first_state new_t in
                   let new_state =
                     try Proof.apply_intro "*" new_state with
                     | _ -> new_state
                   in
                   result @ [ new_state ], Some new_t
                 with
                 | _ -> [], None)
              | _ -> [], None)
           | _ -> [], None)
        ([ first_state ], Some t)
        range
    in
    execution_list |> fst
  | _ -> []
;;

let rec find_all_subtree expr =
  let rec find_all_subtree_from_root expr =
    match expr.Ir.desc with
    | Var name ->
      [ { desc = Some (Sub_Var name); typ = expr.typ }; { desc = None; typ = expr.typ } ]
    | Call (name, args) ->
      if List.is_empty args
      then
        [ { desc = Some (Sub_Call (name, [])); typ = expr.typ }
        ; { desc = None; typ = expr.typ }
        ]
      else (
        let args_subtree = List.map find_all_subtree_from_root args in
        let args_cand =
          List.fold_left
            (fun acc nth_arg_cand ->
               List.map
                 (fun pre_args -> List.map (fun arg -> pre_args @ [ arg ]) nth_arg_cand)
                 acc
               |> List.concat)
            (args_subtree |> List.hd |> List.map (fun arg -> [ arg ]))
            (args_subtree |> List.tl)
        in
        List.map
          (fun args -> { desc = Some (Sub_Call (name, args)); typ = expr.typ })
          args_cand
        @ [ { desc = None; typ = expr.typ } ])
    | _ -> []
  in
  let root_subtree = find_all_subtree_from_root expr in
  let sub_subtree =
    match expr.Ir.desc with
    | Var _ -> find_all_subtree_from_root expr
    | Call (_, args) -> List.map find_all_subtree args |> List.concat
    | _ -> []
  in
  root_subtree @ sub_subtree |> List.sort_uniq compare
;;

let number_of_vertices subtree =
  let rec number_of_vertices_from_root subtree =
    match subtree.desc with
    | Some (Sub_Call (_, args)) ->
      List.fold_left (fun acc arg -> acc + number_of_vertices_from_root arg) 1 args
    | Some (Sub_Var _) -> 1
    | None -> 0
  in
  number_of_vertices_from_root subtree
;;

let is_proper_subset subtree1 subtree2 =
  let rec is_proper_subset subtree1 subtree2 =
    match subtree2.desc with
    | Some (Sub_Call (_, args)) ->
      subtree1 = subtree2 || List.exists (fun arg -> is_proper_subset subtree1 arg) args
    | _ -> subtree1 = subtree2
  in
  if subtree1 = subtree2 then false else is_proper_subset subtree1 subtree2
;;

let rec is_strict_large subtree1 subtree2 =
  let rec is_matched subtree1 subtree2 =
    match subtree1.desc, subtree2.desc with
    | Some (Sub_Call (name1, args1)), Some (Sub_Call (name2, args2)) ->
      (name1 = name2 && List.for_all2 is_matched args1 args2)
      || List.exists (fun arg -> is_matched subtree1 arg) args2
    | None, _ -> true
    | _, _ -> subtree1 = subtree2
  in
  (* here *)
  match subtree1.desc, subtree2.desc with
  | Some (Sub_Call (name1, args1)), Some (Sub_Call (name2, args2)) ->
    (name1 = name2 && List.for_all2 is_matched args1 args2)
    || List.exists (fun arg -> is_strict_large subtree1 arg) args2
  | _, Some (Sub_Call (_, args)) ->
    List.exists (fun arg -> is_strict_large subtree1 arg) args
  | Some (Sub_Var var1), Some (Sub_Var var2) -> var1 = var2
  | None, _ -> true
  | _, _ -> false
;;

let find_larget_common_subtree expr1 expr2 =
  let subtree_list1 = find_all_subtree expr1 in
  let subtree_list2 = find_all_subtree expr2 in
  let common_subtree =
    List.filter (fun subtree -> List.mem subtree subtree_list2) subtree_list1
  in
  if List.is_empty common_subtree (* when meet match or letin expression *)
  then []
  else (
    let largest_common_subtree =
      List.fold_left
        (fun acc subtree ->
           let subtree_list =
             List.filter (fun subtree2 -> not (is_strict_large subtree2 subtree)) acc
           in
           if List.exists (fun subtree2 -> is_strict_large subtree subtree2) subtree_list
           then subtree_list
           else subtree :: subtree_list)
        []
        common_subtree
    in
    largest_common_subtree)
;;

let catch_recursive_pattern induction_var expr_list =
  (* In catching pattern, have to handle error! *)
  let rec get_parent source expr =
    match expr.Ir.desc with
    | Call (_, args) ->
      if List.exists (fun arg -> arg = source) args
      then Some expr
      else
        List.fold_left
          (fun (acc, is_done) arg ->
             if is_done
             then acc, true
             else (
               match get_parent source arg with
               | Some exp -> Some exp, true
               | _ -> None, false))
          (None, false)
          args
        |> fst
    | _ -> None
  in
  let get_lower (source : expr) parent =
    match parent.Ir.desc with
    | Call (name, args) ->
      { desc =
          Some
            (Sub_Call
               ( name
               , List.map
                   (fun arg ->
                      if arg = source
                      then { desc = None; typ = arg.typ }
                      else arg |> to_sub)
                   args ))
      ; typ = parent.typ
      }
    | _ -> failwith "not implemented"
  in
  let rec get_upper source expr =
    match expr.Ir.desc with
    | Call (name, args) ->
      if List.exists (fun arg -> arg = source) args
      then
        { desc =
            Some
              (Sub_Call
                 ( name
                 , List.map
                     (fun arg ->
                        if arg = source
                        then { desc = None; typ = expr.typ }
                        else arg |> to_sub)
                     args ))
        ; typ = expr.typ
        }
      else
        { desc = Some (Sub_Call (name, List.map (fun arg -> get_upper source arg) args))
        ; typ = expr.typ
        }
    | _ -> expr |> to_sub
  in
  let rec remove_upper induction_var upper expr =
    match expr.desc, upper.desc with
    | Some (Sub_Call (name1, args1)), Some (Sub_Call (name2, args2)) ->
      if name1 = name2
      then
        List.fold_left2
          (fun (acc, is_done) arg1 arg2 ->
             if is_done
             then acc, true
             else if arg1 = arg2 || arg2 = (induction_var |> to_sub)
             then acc, false
             else if arg2.desc = None
             then Some arg1, true
             else remove_upper induction_var arg1 arg2, true)
          (None, false)
          args1
          args2
        |> fst
      else None
    | _ -> None
    (* have to correct here *)
  in
  let remove_lower lower expr =
    match expr.desc with
    | Some (Sub_Call (name, args)) ->
      { desc =
          Some
            (Sub_Call
               ( name
               , List.map
                   (fun arg ->
                      if arg = lower then { desc = None; typ = arg.typ } else arg)
                   args ))
      ; typ = expr.typ
      }
    | Some (Sub_Var _) -> if expr = lower then { desc = None; typ = expr.typ } else expr
    | _ -> failwith "not implemented : remove_lower"
  in
  let first = List.hd expr_list in
  let second = List.hd (List.tl expr_list) in
  let first_vars = collect_free_var_in_expr first [] in
  let second_vars = collect_free_var_in_expr second [] in
  let new_vars = List.filter (fun var -> not (List.mem var first_vars)) second_vars in
  if List.is_empty new_vars
  then []
  else (
    let new_var =
      Ir.
        { desc = Var (List.hd new_vars |> fst)
        ; typ =
            (match List.hd new_vars |> snd with
             | Type typ -> typ
             | _ -> failwith "not implemented")
        }
    in
    let parent = get_parent new_var second in
    match parent with
    | None -> []
    | Some parent ->
      let lower = get_lower new_var parent in
      let upper = get_upper parent second in
      let recursive_expr_list =
        List.map
          (fun expr ->
             let expr = expr |> to_sub in
             match remove_upper induction_var upper expr with
             | Some subtree -> subtree |> remove_lower lower
             | None -> { desc = None; typ = Tany })
          expr_list
      in
      if
        List.exists
          (fun subtree -> Option.is_none subtree.desc)
          (List.tl recursive_expr_list)
      then []
      else recursive_expr_list)
;;

let expr_of_subtree subtree =
  let rec expr_of_subtree subtree =
    match subtree.desc with
    | Some (Sub_Call (name, args)) ->
      let args = List.map (fun arg -> expr_of_subtree arg) args in
      Ir.{ desc = Call (name, args); typ = subtree.typ }
    | Some (Sub_Var name) -> Ir.{ desc = Var name; typ = subtree.typ }
    | None -> failwith "subtree is not proper"
  in
  expr_of_subtree subtree
;;

let subtree_of_expr expr =
  let rec subtree_of_expr expr =
    match expr.Ir.desc with
    | Var name -> { desc = Some (Sub_Var name); typ = expr.typ }
    | Call (name, args) ->
      let args = List.map (fun arg -> subtree_of_expr arg) args in
      { desc = Some (Sub_Call (name, args)); typ = expr.typ }
    | _ -> { desc = None; typ = expr.typ }
  in
  subtree_of_expr expr
;;

let rec convert_diff_to_expr fun_name increase_arg base_args diff =
  match diff.desc with
  | Some (Sub_Call (name, args)) ->
    let args =
      List.map (fun arg -> convert_diff_to_expr fun_name increase_arg base_args arg) args
    in
    Ir.{ desc = Call (name, args); typ = diff.typ }
  | Some (Sub_Var _) -> Ir.{ desc = Var "hd"; typ = diff.typ }
  | None ->
    let increase_arg = Ir.{ increase_arg with desc = Var "tl" } in
    Ir.{ desc = Call (fun_name, increase_arg :: base_args); typ = diff.typ }
;;

let rec fill_subtreewith_expr subtree expr : expr =
  let _ = print_endline "subtree" in
  let _ = subtree |> pp_subtree |> print_endline in
  let _ = print_endline "expr" in
  let _ = expr |> Ir.pp_expr |> print_endline in
  match subtree.desc with
  | Some (Sub_Call (name, args)) ->
    let args = List.map (fun arg -> fill_subtreewith_expr arg expr) args in
    Ir.{ desc = Call (name, args); typ = subtree.typ }
  | Some (Sub_Var name) -> Ir.{ desc = Var name; typ = subtree.typ }
  | None -> expr
;;

let decl_of_subtree_difference fun_name base_case subtree_differnce =
  let increase_typ = collect_free_var_in_subtree (List.hd subtree_differnce) [] in
  let increase_typ =
    match increase_typ |> List.hd |> snd with
    | Proof.Type typ -> typ
    | _ -> failwith "not implemented"
  in
  let base_case_var = collect_free_var_in_subtree base_case [] in
  let base_case_var_expr =
    List.map
      (fun (name, typ) ->
         match typ with
         | Proof.Type typ -> Ir.{ desc = Var name; typ }
         | _ -> failwith "not implemented")
      base_case_var
  in
  let base_case_var = List.map fst base_case_var in
  let increase_arg =
    Ir.{ desc = Var "lst"; typ = Ir.Talgebraic ("list", [ increase_typ ]) }
  in
  let base_pattern = Ir.Case (Pat_Constr ("Nil", []), expr_of_subtree base_case) in
  let inductive_expr =
    convert_diff_to_expr
      fun_name
      increase_arg
      base_case_var_expr
      (List.hd subtree_differnce)
  in
  let inductive_pattern =
    Ir.Case (Pat_Constr ("Cons", [ Pat_Var "hd"; Pat_Var "tl" ]), inductive_expr)
  in
  let fun_body =
    Ir.
      { desc = Match ([ increase_arg ], [ base_pattern; inductive_pattern ])
      ; typ = Ir.Tany
      }
  in
  Ir.Rec (fun_name, "lst" :: base_case_var, fun_body)
;;

let helper_function_lemma (decl : Ir.decl) : lemma list =
  match decl with
  | Ir.Rec (fname, args, body) ->
    (match body.desc with
     | Match (match_list, case_list) ->
       List.map
         (fun case ->
            match match_list, case with
            | [ match_var ], Ir.Case (pat, expr) ->
              let new_arg = Ir.{ desc = Ir.expr_of_pattern pat; typ = match_var.typ } in
              let free_vars = collect_free_var_in_expr expr [] in
              let result =
                Proof.Forall
                  ( free_vars
                  , Proof.Eq
                      ( Ir.
                          { desc =
                              Call
                                ( fname
                                , new_arg
                                  :: List.map
                                       (fun arg ->
                                          let typ =
                                            match List.assoc arg free_vars with
                                            | Proof.Type typ -> typ
                                            | _ -> failwith "not implemented"
                                          in
                                          Ir.{ desc = Var arg; typ })
                                       (List.tl args) )
                          ; typ = expr.typ
                          }
                      , expr ) )
              in
              result
            | _ -> failwith "not implemented")
         case_list
     | _ -> failwith "not implemented")
  | _ -> failwith "this function is not recursive"
;;

let is_pattern increase_subtree =
  let rec comp subtree1 subtree2 =
    match subtree1.desc, subtree2.desc with
    | Some (Sub_Call (name1, args1)), Some (Sub_Call (name2, args2)) ->
      name1 = name2 && List.for_all2 comp args1 args2
    | Some (Sub_Var _), Some (Sub_Var _) -> true
    | None, None -> true
    | _, _ -> false
  in
  List.for_all
    (fun subtree ->
       let base = List.hd increase_subtree in
       comp subtree base)
    (List.tl increase_subtree)
;;

let make_helper_function_and_lemma ~is_lhs expr_list common_subtree increase_subtree i =
  let base_case = List.hd common_subtree in
  let free_vars = collect_free_var_in_subtree base_case [] in
  let free_vars_with_typ =
    List.map
      (fun (name, typ) ->
         match typ with
         | Proof.Type typ -> Ir.{ desc = Var name; typ }
         | _ -> failwith "not implemented")
      free_vars
  in
  let helper_decl =
    decl_of_subtree_difference
      ((if is_lhs then "mk_lhs" else "mk_rhs") ^ string_of_int i)
      base_case
      increase_subtree
  in
  let lemma = helper_function_lemma helper_decl in
  let increase_arg =
    match helper_decl with
    | Ir.Rec (_, args, body) ->
      let arg = List.hd args in
      let typ = Ir.get_type_in_expr arg body |> Option.get in
      Ir.{ desc = Var "lst"; typ }
    | _ -> failwith "not implemented"
  in
  let helper_call =
    Ir.
      { desc =
          Call
            ( (if is_lhs then "mk_lhs" else "mk_rhs") ^ string_of_int i
            , increase_arg :: free_vars_with_typ )
      ; typ = (common_subtree |> List.hd).typ
      }
  in
  let head =
    difference_of_subtree
      (List.nth common_subtree 1)
      (List.nth expr_list 1 |> subtree_of_expr)
  in
  let expr_with_helper = fill_subtreewith_expr head helper_call in
  helper_decl, lemma, expr_with_helper
;;

let pattern_recognition env ihs induction_var state_list : env * lemma list =
  let first_lhs = List.map (fun ih -> ih |> snd |> Proof.get_lhs) ihs in
  let first_rhs = List.map (fun ih -> ih |> snd |> Proof.get_rhs) ihs in
  let facts_list =
    List.map
      (fun state ->
         let facts, goal, _ = state in
         filtering_concerned_fact facts goal)
      state_list
  in
  let common_facts =
    try
      List.fold_left
        (fun acc facts ->
           List.filter (fun (_, fact) -> List.exists (fun (_, f) -> f = fact) facts) acc)
        (List.hd facts_list)
        (List.tl facts_list)
    with
    | _ -> List.concat facts_list
  in
  let common_facts = List.map snd common_facts in
  let goals = List.map (fun (_, goal, _) -> goal) state_list in
  let lhs_list = List.map (fun goal -> Proof.get_lhs goal) goals in
  let rhs_list = List.map (fun goal -> Proof.get_rhs goal) goals in
  let lhs_common_subtree = catch_recursive_pattern induction_var (first_lhs @ lhs_list) in
  let rhs_common_subtree = catch_recursive_pattern induction_var (first_rhs @ rhs_list) in
  if
    List.length lhs_common_subtree <> List.length rhs_common_subtree
    || List.is_empty lhs_common_subtree
  then [], []
  else (
    let range = Proof.range 0 (List.length lhs_common_subtree - 1) in
    let lhs_increase_subtree =
      List.map
        (fun i ->
           difference_of_subtree
             (List.nth lhs_common_subtree i)
             (List.nth lhs_common_subtree (i + 1)))
        range
    in
    let rhs_increase_subtree =
      List.map
        (fun i ->
           difference_of_subtree
             (List.nth rhs_common_subtree i)
             (List.nth rhs_common_subtree (i + 1)))
        range
    in
    if (not (is_pattern lhs_increase_subtree)) || not (is_pattern rhs_increase_subtree)
    then [], []
    else (
      let i = Ir.get_mk_index env + 1 in
      let lhs_decl, lhs_lemmas, lhs_expr =
        make_helper_function_and_lemma
          ~is_lhs:true
          lhs_list
          lhs_common_subtree
          lhs_increase_subtree
          i
      in
      let rhs_decl, rhs_lemmas, rhs_expr =
        make_helper_function_and_lemma
          ~is_lhs:false
          rhs_list
          rhs_common_subtree
          rhs_increase_subtree
          i
      in
      let goal =
        match common_facts with
        | [] -> Proof.Eq (lhs_expr, rhs_expr)
        | _ -> Proof.Imply (common_facts, Proof.Eq (lhs_expr, rhs_expr))
      in
      let free_vars = collect_free_var_in_prop goal [] |> List.sort_uniq compare in
      let goal = Proof.Forall (free_vars, goal) in
      let env = [ lhs_decl; rhs_decl ] in
      env, lhs_lemmas @ rhs_lemmas @ [ goal ]))
;;

let rec size_of_expr expr =
  match expr.Ir.desc with
  | Var _ -> 1
  | Call (_, args) -> 1 + List.fold_left (fun acc arg -> acc + size_of_expr arg) 0 args
  | Match (args, cases) ->
    List.fold_left (fun acc arg -> acc + size_of_expr arg) 0 args
    + List.fold_left
        (fun acc case ->
           acc
           +
           match case with
           | Ir.Case (_, e) -> size_of_expr e)
        0
        cases
  | LetIn (assign, e) ->
    List.fold_left (fun acc (_, body) -> acc + size_of_expr body) 0 assign
    + size_of_expr e
;;

let rec generalize_common_subterm goal =
  let common_expr_list = find_common_subterm_in_prop goal in
  let common_expr_list =
    List.filter (fun expr -> expr.Ir.typ |> Ir.pp_typ <> "bool") common_expr_list
  in
  if List.is_empty common_expr_list
  then goal
  else (
    let max_expr, max =
      List.fold_left
        (fun (max_expr, max) expr ->
           let size = size_of_expr expr in
           if size > max then expr, size else max_expr, max)
        (List.hd common_expr_list, size_of_expr (List.hd common_expr_list))
        (List.tl common_expr_list)
    in
    let free_vars = collect_free_var_in_expr max_expr [] |> List.sort_uniq compare in
    if free_vars = [] || max = 1
    then goal
    else (
      let new_goal, _, _ =
        Proof.substitute_expr_in_prop
          Ir.is_equal_expr
          (fun _ _ expr_to -> expr_to, [])
          goal
          max_expr
          Ir.
            { desc = Var ("arg" ^ string_of_int (get_global_cnt ()))
            ; typ = max_expr.Ir.typ
            }
          0
          false
      in
      if
        List.exists
          (fun (name, typ) ->
             match typ with
             | Proof.Type typ -> Proof.is_contained Ir.{ desc = Var name; typ } new_goal
             | _ -> false)
          free_vars
      then goal
      else generalize_common_subterm new_goal))
;;

let naive_generalize t =
  let state = Proof.get_first_state t in
  let facts, goal, _ = state in
  let vars = collect_free_var_in_prop goal [] |> List.sort_uniq compare in
  if List.is_empty vars
  then None
  else (
    let facts = filtering_concerned_fact facts goal in
    let facts = List.map snd facts in
    let facts = List.map Proof.rename_prop facts in
    let goal =
      match goal with
      | Proof.Forall (_, goal) -> goal
      | _ -> goal
    in
    let generalize_common_subterm = generalize_common_subterm goal in
    let generalize_common_subterm =
      if List.is_empty facts
      then generalize_common_subterm
      else Proof.Imply (facts, generalize_common_subterm)
    in
    let generalize_common_subterm_goal =
      let qvars =
        collect_free_var_in_prop generalize_common_subterm [] |> List.sort_uniq compare
      in
      Some (Proof.Forall (qvars, generalize_common_subterm))
    in
    generalize_common_subterm_goal)
;;

let rec is_trivial goal =
  match goal with
  | Proof.Eq (lhs, rhs) -> Ir.is_equal_expr lhs rhs
  | Proof.Forall (_, goal) -> is_trivial goal
  | Proof.Imply (_, goal) -> is_trivial goal
  | _ -> false
;;

let get_induction_var t =
  let facts, _, _ = Proof.get_first_state t in
  let _, induction_fact =
    List.find
      (fun (name, _) ->
         String.starts_with ~prefix:"Inductive" name
         || String.starts_with ~prefix:"Base" name)
      facts
  in
  let induction_var =
    match induction_fact with
    | Proof.Eq (lhs, rhs) ->
      let rhs_vars = collect_free_var_in_expr rhs [] in
      let recursive_var =
        List.find
          (fun (_, typ) ->
             match typ with
             | Proof.Type typ -> typ = lhs.Ir.typ
             | _ -> false)
          rhs_vars
      in
      let recursive_var =
        Ir.
          { desc = Var (fst recursive_var)
          ; typ =
              (match snd recursive_var with
               | Proof.Type typ -> typ
               | _ -> failwith "Unexpected type")
          }
      in
      recursive_var
    | _ -> failwith "Induction fact is not a Forall"
  in
  induction_var
;;

let advanced_generalize t : (t * lemma list) option =
  let first_state = Proof.get_first_state t in
  let facts, goal, _ = first_state in
  match is_trivial goal with
  | true -> None
  | false ->
    let ihs = List.filter (fun (name, _) -> String.starts_with ~prefix:"IH" name) facts in
    let state_list = fast_execution 2 t in
    (match state_list with
     | [] ->
       (match naive_generalize t with
        | Some lemma -> Some (t, [ lemma ])
        | _ -> None)
     | _ ->
       let induction_var = get_induction_var t in
       let new_env, lemma_list = pattern_recognition t.env ihs induction_var state_list in
       let new_env = List.map Ir.rename_decl new_env in
       if List.is_empty lemma_list
       then (
         match naive_generalize t with
         | Some lemma -> Some (t, [ lemma ])
         | _ -> None)
       else (
         let new_t =
           List.fold_left
             (fun acc decl -> Proof.apply_tactic acc (Proof.Define decl))
             t
             new_env
         in
         Some (new_t, lemma_list)))
;;

let make_lemmas_by_advanced_generalize (t : t) lemma_set : (t * lemma list) option =
  let t_lemma = advanced_generalize t in
  let original_goal = Proof.get_conj_list t |> List.hd |> snd in
  let t_lemma =
    match t_lemma with
    | Some (new_t, lemmas) ->
      if
        List.for_all
          (fun lemma ->
             Prover.LemmaSet.exists
               (fun (goal', lemma', _) -> original_goal = goal' && lemma = lemma')
               lemma_set)
          lemmas
        && not (List.is_empty lemmas)
      then None
      else if
        List.for_all
          (fun lemma ->
             Prover.LemmaSet.exists
               (fun (_, lemma', tactic) -> lemma = lemma' && not (List.is_empty tactic))
               lemma_set)
          lemmas
        && not (List.is_empty lemmas)
      then (
        let pre_lemmas =
          List.map
            (fun lemma ->
               List.find
                 (fun (_, lemma', tactic) -> lemma = lemma' && not (List.is_empty tactic))
                 (lemma_set |> Prover.LemmaSet.to_list))
            lemmas
        in
        let new_t =
          List.fold_left
            (fun acc (_, _, tactic) ->
               List.fold_left (fun acc tactic -> Proof.apply_tactic acc tactic) acc tactic)
            new_t
            pre_lemmas
        in
        Some (new_t, []))
      else t_lemma
    | None -> None
  in
  t_lemma
;;
