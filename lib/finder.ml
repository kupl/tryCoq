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
  | _ -> failwith "not implemented"
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

let is_duplicated (t : t) (lemma : lemma) : bool =
  ignore (t, lemma);
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

let split_t t : t list =
  let lemma_stack = Proof.get_lemma_stack t in
  let tactics = Proof.get_tactic_history t in
  let states, _ = Proof.get_conj_list t |> List.hd in
  List.map
    (fun state ->
       let dummy_goal = Proof.Type Ir.Tany in
       Proof.(
         create_t
           t.env
           ~proof:(lemma_stack, [ [ state ], dummy_goal ], tactics)
           ~counter:t.counter
           ()))
    states
;;

let progress_with_split t : t list =
  let t_list = split_t t in
  List.fold_left
    (fun acc t ->
       match Prover.progress_single_thread t with
       | Some t ->
         List.fold_left
           (fun acc t ->
              match Prover.progress_single_thread t with
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

let new_catch_recursive_pattern env expr_list =
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
  let rec remove_upper new_var upper expr =
    match expr.desc, upper.desc with
    | Some (Sub_Call (name1, args1)), Some (Sub_Call (name2, args2)) ->
      if name1 = name2
      then
        List.fold_left2
          (fun (acc, is_done) arg1 arg2 ->
             if is_done
             then acc, true
             else if arg1 = arg2 || arg2 = new_var
             then acc, false
             else if arg2.desc = None
             then Some arg1, true
             else remove_upper new_var arg1 arg2, true)
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
    | _ -> failwith "not implemented"
  in
  let first = List.hd expr_list in
  let second = List.hd (List.tl expr_list) in
  let first_vars = collect_free_var_in_expr first [] in
  let second_vars = collect_free_var_in_expr second [] in
  let new_vars = List.filter (fun var -> not (List.mem var first_vars)) second_vars in
  let new_vars =
    List.filter
      (fun var ->
         not
           (Prover.is_decreasing_var
              env
              ([], Proof.Eq (second, second), Egraph.Egraph.init ())
              (fst var)))
      new_vars
  in
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
  let lower = get_lower new_var (parent |> Option.get) in
  let upper = get_upper (parent |> Option.get) second in
  let _ = parent |> Option.get |> Ir.pp_expr |> print_endline in
  let _ = lower |> pp_subtree |> print_endline in
  let _ = upper |> pp_subtree |> print_endline in
  let recursive_expr_list =
    List.map
      (fun expr ->
         let expr = expr |> to_sub in
         match remove_upper (new_var |> to_sub) upper expr with
         | Some subtree -> subtree |> remove_lower lower
         | None -> failwith "cannot find recursive expr")
      expr_list
  in
  recursive_expr_list |> List.tl
;;

let catch_recursive_pattern env expr_list =
  ignore env;
  let _ = print_endline "mmmmmmmmmmmmmmmmmm" in
  let _ = expr_list |> List.iter (fun expr -> Proof.pp_expr expr |> print_endline) in
  let range = Proof.range 0 (List.length expr_list - 1) in
  let common_subtree_list, _ =
    List.fold_left
      (fun (acc, is_done) i ->
         if is_done
         then [], true
         else (
           let expr1 = List.nth expr_list i in
           let expr2 = List.nth expr_list (i + 1) in
           match find_larget_common_subtree expr1 expr2 with
           | [] -> [], true
           | subtree -> acc @ [ subtree ], false))
      ([], false)
      range
  in
  if List.is_empty common_subtree_list
  then []
  else (
    let common_subtree_cand_list =
      List.fold_left
        (fun acc subtree_cand ->
           List.map
             (fun cand -> List.map (fun scenario -> scenario @ [ cand ]) acc)
             subtree_cand
           |> List.concat)
        (List.hd common_subtree_list |> List.map (fun subtree -> [ subtree ]))
        (common_subtree_list |> List.tl)
    in
    let _ =
      common_subtree_cand_list
      |> List.iter (fun subtree_list ->
        let _ = print_endline "common_subtree_cand_list----------" in
        subtree_list |> List.iter (fun subtree -> pp_subtree subtree |> print_endline))
    in
    let common_subtree_cand_list =
      List.filter
        (fun subtree_list ->
           let range = Proof.range 0 (List.length subtree_list - 1) in
           List.for_all
             (fun i ->
                let subtree1 = List.nth subtree_list i in
                let subtree2 = List.nth subtree_list (i + 1) in
                is_proper_subset subtree1 subtree2)
             range)
        common_subtree_cand_list
    in
    if List.is_empty common_subtree_cand_list
    then []
    else
      List.fold_left
        (fun acc subtree_list ->
           if List.length acc > List.length subtree_list then acc else subtree_list)
        (List.hd common_subtree_cand_list)
        (List.tl common_subtree_cand_list))
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

let pattern_recognition env ihs state_list : env * lemma list =
  (* let first_lhs = List.map (fun ih -> ih |> snd |> Proof.get_lhs) ihs in
  let first_rhs = List.map (fun ih -> ih |> snd |> Proof.get_rhs) ihs in *)
  let goals = List.map (fun (_, goal, _) -> goal) state_list in
  let lhs_list = List.map (fun goal -> Proof.get_lhs goal) goals in
  let rhs_list = List.map (fun goal -> Proof.get_rhs goal) goals in
  (* let lhs_common_subtree_cand =
    List.map (fun lhs -> catch_recursive_pattern env (lhs :: lhs_list)) first_lhs
    @ [ catch_recursive_pattern env lhs_list ]
  in
  let rhs_common_subtree_cand =
    List.map (fun rhs -> catch_recursive_pattern env (rhs :: rhs_list)) first_rhs
    @ [ catch_recursive_pattern env rhs_list ]
  in
  let lhs_common_subtree =
    List.fold_left
      (fun acc subtree_list ->
         if List.length acc > List.length subtree_list then acc else subtree_list)
      (List.hd lhs_common_subtree_cand)
      (List.tl lhs_common_subtree_cand)
  in
  let rhs_common_subtree =
    List.fold_left
      (fun acc subtree_list ->
         if List.length acc > List.length subtree_list then acc else subtree_list)
      (List.hd rhs_common_subtree_cand)
      (List.tl rhs_common_subtree_cand)
  in
  let _ = ignore lhs_common_subtree in
  let _ = ignore rhs_common_subtree in *)
  ignore ihs;
  let lhs_common_subtree = new_catch_recursive_pattern env lhs_list in
  let rhs_common_subtree = new_catch_recursive_pattern env rhs_list in
  let _ =
    lhs_common_subtree |> List.iter (fun subtree -> pp_subtree subtree |> print_endline)
  in
  let _ =
    rhs_common_subtree |> List.iter (fun subtree -> pp_subtree subtree |> print_endline)
  in
  let _ = failwith "asdf" in
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
    let lhs_base_case = List.hd lhs_common_subtree in
    let lhs_free_vars = collect_free_var_in_subtree lhs_base_case [] in
    let lhs_free_vars_with_typ =
      List.map
        (fun (name, typ) ->
           match typ with
           | Proof.Type typ -> Ir.{ desc = Var name; typ }
           | _ -> failwith "not implemented")
        lhs_free_vars
    in
    let rhs_base_case = List.hd rhs_common_subtree in
    let rhs_free_vars = collect_free_var_in_subtree rhs_base_case [] in
    let rhs_free_vars_with_typ =
      List.map
        (fun (name, typ) ->
           match typ with
           | Proof.Type typ -> Ir.{ desc = Var name; typ }
           | _ -> failwith "not implemented")
        rhs_free_vars
    in
    (* have to add index for mk function *)
    let mk_lhs = decl_of_subtree_difference "mk_lhs" lhs_base_case lhs_increase_subtree in
    let mk_rhs = decl_of_subtree_difference "mk_rhs" rhs_base_case rhs_increase_subtree in
    let lhs_lemma = helper_function_lemma mk_lhs in
    let rhs_lemma = helper_function_lemma mk_rhs in
    let increase_typ = lhs_free_vars_with_typ |> List.hd |> Ir.(fun x -> x.typ) in
    let increase_arg =
      Ir.{ desc = Var "lst"; typ = Ir.Talgebraic ("list", [ increase_typ ]) }
    in
    let new_lhs =
      Ir.
        { desc = Call ("mk_lhs", increase_arg :: lhs_free_vars_with_typ)
        ; typ = (lhs_common_subtree |> List.hd).typ
        }
    in
    let new_rhs =
      Ir.
        { desc = Call ("mk_rhs", increase_arg :: rhs_free_vars_with_typ)
        ; typ = (rhs_common_subtree |> List.hd).typ
        }
    in
    let lhs_head =
      difference_of_subtree
        (List.hd lhs_common_subtree)
        (List.hd lhs_list |> subtree_of_expr)
    in
    let rhs_head =
      difference_of_subtree
        (List.hd rhs_common_subtree)
        (List.hd rhs_list |> subtree_of_expr)
    in
    let lhs = fill_subtreewith_expr lhs_head new_lhs in
    let rhs = fill_subtreewith_expr rhs_head new_rhs in
    let goal = Proof.Eq (lhs, rhs) in
    let free_vars = collect_free_var_in_prop goal [] |> List.sort_uniq compare in
    let goal = Proof.Forall (free_vars, goal) in
    let env = [ mk_lhs; mk_rhs ] in
    env, lhs_lemma @ rhs_lemma @ [ goal ])
;;

let symbolic_execution t : state list list =
  let state = Proof.get_first_state t in
  let facts, goal, _ = state in
  let facts = filtering_concerned_fact facts goal in
  let base_hypothesis = [ facts, goal, Proof.graph_of_prop goal ] in
  let rec symbolic_execution_by_depth t depth (acc : state list) : state list list =
    let env = t.Proof.env in
    if depth = 0
    then [ acc ]
    else (
      let state = Proof.get_first_state t in
      let lemma_stack = Proof.get_lemma_stack t in
      let facts, goal, _ = state in
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
        let new_conj = [ facts, new_goal, Proof.graph_of_prop new_goal ], dummy_goal in
        let new_t =
          Proof.(
            create_t
              t.env
              ~proof:(lemma_stack, [ new_conj ], Proof.get_tactic_history t)
              ~counter:t.counter
              ())
        in
        let vars = List.map fst vars in
        let induction_tactic = Proof.Induction (List.hd vars) in
        let new_t = Proof.apply_tactic new_t induction_tactic in
        let new_t_list = progress_with_split new_t in
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
            (fun t new_acc -> symbolic_execution_by_depth t (depth - 1) new_acc)
            new_t_list
            new_accs
        in
        List.concat result))
  in
  let result = symbolic_execution_by_depth t 3 base_hypothesis in
  List.filter (fun state_list -> List.length state_list > 3) result
;;

let advanced_generalize t : (t * lemma list) list =
  let first_state = Proof.get_first_state t in
  let facts, _, _ = first_state in
  let ihs = List.filter (fun (name, _) -> String.starts_with ~prefix:"IH" name) facts in
  let execution_list = symbolic_execution t in
  let env_lemma_pairs =
    List.map (fun state_list -> pattern_recognition t.env ihs state_list) execution_list
  in
  let env_lemma_pairs =
    List.filter (fun (_, lemma) -> not (List.is_empty lemma)) env_lemma_pairs
  in
  let env_lemma_pairs =
    List.map
      (fun (new_env, lemma) -> { t with env = t.env @ new_env }, lemma)
      env_lemma_pairs
  in
  env_lemma_pairs
;;

let make_lemmas_by_advanced_generalize (stuck_list : Prover.ProofSet.t) lemma_list
  : (t * lemma list) list
  =
  let lemmas =
    List.map advanced_generalize (Prover.ProofSet.to_list stuck_list) |> List.concat
  in
  let lemmas =
    List.fold_left
      (fun (acc : (t * lemma list) list) (t, lemma_list) ->
         let lemma_stack = Proof.get_lemma_stack t in
         if
           List.exists
             (fun (t', lemma_list') ->
                let lemma_stack' = Proof.get_lemma_stack t' in
                lemma_stack' = lemma_stack
                && List.map (Proof.simplify_prop t'.env) lemma_list
                   = List.map (Proof.simplify_prop t'.env) lemma_list')
             acc
         then acc
         else (t, lemma_list) :: acc)
      []
      lemmas
  in
  let lemmas =
    List.filter
      (fun (_, lemma) ->
         not (List.exists (fun (_, old_lemma) -> old_lemma = lemma) lemma_list))
      lemmas
  in
  lemmas
;;

(* let naive_generalize (goal : Proof.goal) t : lemma list =
  let env = t.Proof.env in
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
      symbolic_execution t
      |> List.iter (fun state_list ->
        let _ = print_endline "state_list" in
        let _ =
          state_list |> List.iter (fun (_, goal) -> Proof.pp_prop goal |> print_endline)
        in
        ())
    in
    let _ = print_endline "*******" in
    let t = Proof.(create_t t.env ~proof:t.proof ~counter:t.counter ()) in
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

let make_lemmas (stuck_list : Prover.ProofSet.t) lemma_list : (t * lemma) list =
  let lemmas =
    List.map
      (fun t ->
         let state = Proof.get_first_state t in
         let _, goal = state in
         let lemmas = naive_generalize goal t in
         (* convert this part to take env *)
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
                && Proof.simplify_prop t'.env lemma = Proof.simplify_prop t'.env lemma')
             acc
         then acc
         else (t, Proof.simplify_prop t.env lemma) :: acc)
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
;; *)
