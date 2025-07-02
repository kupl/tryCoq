let split_once c str =
  try
    let idx = String.index str c in
    [ String.sub str 0 idx; String.sub str (idx + 1) (String.length str - idx - 1) ]
  with
  | Not_found -> [ str ]
;;

let axiom_to_prop env src : Proof.theorem list =
  let src = String.split_on_char '\n' src in
  List.map
    (fun src ->
       match split_once ':' src with
       | [ name; prop ] ->
         let name = String.trim name in
         let prop = Proof.parse_prop prop [] env in
         if
           try
             let _ = Str.search_forward (Str.regexp "eqb_eq") name 0 in
             true
           with
           | _ -> false
         then name, Proof.simplify_prop env prop
         else name, prop
       | _ -> failwith "axiom format error")
    src
;;

let proof_top definition axiom program_a program_b =
  let definition = Parser.parse definition in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let definition = definition |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  (* let _ = definition |> Ir.sexp_of_t |> Sexplib.Sexp.to_string |> print_endline in *)
  let _ = program_a |> Ir.sexp_of_t |> Sexplib.Sexp.to_string |> print_endline in
  let env = definition @ program_a @ program_b in
  let axiom = axiom |> axiom_to_prop env in
  let init_t = Proof.create_t env ~proof:(axiom, [], []) () in
  Proof.proof_top init_t
;;

let rec split_tale lst =
  match lst with
  | [ tl ] -> [], tl
  | hd :: tl -> hd :: fst (split_tale tl), snd (split_tale tl)
  | _ -> failwith "length has to be greater than 1"
;;

let make_progress_counter () =
  let count = ref 0 in
  fun () ->
    incr count;
    !count
;;

let progress_counter = make_progress_counter ()

let get_proof_of_lemma t =
  let tactic_list = Proof.get_tactic_history t in
  let rec aux tactic_list result =
    match tactic_list with
    | [] -> []
    | Proof.Assert lemma :: _ -> Proof.Assert lemma :: result
    | hd :: tl -> aux tl (result @ [ hd ])
  in
  aux (List.rev tactic_list) []
;;

let is_end_of_conj t next_t =
  let conj_len = Proof.get_conj_list t |> List.length in
  let next_conj_len = Proof.get_conj_list next_t |> List.length in
  conj_len > next_conj_len
;;

let get_conj_goal t =
  let conj_list = Proof.get_conj_list t in
  match conj_list with
  | [] -> failwith "conj_list is empty"
  | hd :: _ -> snd hd
;;

let rec progress worklist statelist stuck_goals lemma_set =
  match Prover.WorkList.is_empty worklist with
  | true -> failwith "worklist is empty"
  | false ->
    let prev_worklist, work = Prover.WorkList.take_exn worklist in
    let t, tactic, next_t, r, _ = work in
    let _ = print_endline "=================================================" in
    let i = progress_counter () in
    let _ = print_endline ("Progress: " ^ string_of_int i) in
    let _ = Proof.pp_t t |> print_endline in
    let _ =
      print_endline (">>> " ^ Proof.pp_tactic tactic ^ "(rank : " ^ string_of_int r ^ ")")
    in
    let _ = Proof.pp_t next_t |> print_endline in
    let lemma_set =
      match is_end_of_conj t next_t with
      | true ->
        let lemma_list = Proof.get_lemma_stack next_t in
        let lemma = List.hd (List.rev lemma_list) |> snd in
        let tactics = get_proof_of_lemma next_t in
        let original_goal = get_conj_goal t in
        let lemma_set = Prover.LemmaSet.add (original_goal, lemma, tactics) lemma_set in
        lemma_set
      | false -> lemma_set
    in
    (* let _ = if i = 72 then Proof.proof_top next_t in *)
    (match next_t.proof with
     | _, [], proof -> Prover.ProofSet.empty, Some proof, next_t.env
     | _ ->
       let prev_worklist =
         match tactic with
         | Proof.Reflexivity | Proof.Discriminate ->
           Prover.deduplicate_worklist prev_worklist next_t
         | _ -> prev_worklist
       in
       let tactic_list = Prover.mk_candidates next_t in
       let worklist, statelist =
         Prover.prune_rank_worklist_update_state_list next_t tactic_list statelist
       in
       let _ =
         print_endline
           ("Tactic List : "
            ^ string_of_int (List.length (worklist |> Prover.WorkList.to_list)))
       in
       let _ =
         Prover.WorkList.iter
           (fun (_, tactic, _, r, _) ->
              Proof.pp_tactic tactic ^ "(rank:" ^ string_of_int r ^ ")" |> print_endline)
           worklist
       in
       let _, next_goal, _ = Proof.get_first_state next_t in
       if Prover.is_stuck worklist && List.for_all (fun x -> x <> next_goal) stuck_goals
       then (
         let t_lemma = Finder.make_lemmas_by_advanced_generalize next_t lemma_set in
         match t_lemma with
         | Some (new_t, assert_list) ->
           let new_t, tactic, r, assert_list =
             match assert_list with
             | [] ->
               let prev_lemma_list = Proof.get_lemma_stack t in
               let new_lemma_list = Proof.get_lemma_stack new_t in
               let assert_list =
                 List.filter (fun x -> not (List.mem x prev_lemma_list)) new_lemma_list
               in
               let last_lemma, _ = List.hd (List.rev assert_list) in
               ( new_t
               , Proof.mk_rewrite_in_at last_lemma "goal" 0
               , -1
               , assert_list |> List.map snd )
             | _ ->
               let new_env =
                 List.filter (fun x -> not (List.mem x next_t.env)) new_t.env
               in
               let _ = print_endline "New Env" in
               let _ = new_env |> Ir.pp_t |> print_endline in
               let _ = print_endline "Lemma List" in
               let _ =
                 assert_list |> List.iter (fun x -> Proof.pp_prop x |> print_endline)
               in
               let _ = print_endline "End of Lemma List" in
               let heads, tl = split_tale assert_list in
               let new_t =
                 match heads with
                 | [ lhs1; lhs2; rhs1; rhs2 ] ->
                   let new_t = Proof.apply_assert lhs1 new_t in
                   let new_t = Proof.apply_tactic new_t (Proof.SimplIn "goal") in
                   let new_t =
                     Proof.apply_tactic ~is_lhs:(Some true) new_t Proof.Reflexivity
                   in
                   let new_t = Proof.apply_assert lhs2 new_t in
                   let new_t = Proof.apply_tactic new_t (Proof.SimplIn "goal") in
                   let new_t =
                     Proof.apply_tactic ~is_lhs:(Some true) new_t Proof.Reflexivity
                   in
                   let new_t = Proof.apply_assert rhs1 new_t in
                   let new_t = Proof.apply_tactic new_t (Proof.SimplIn "goal") in
                   let new_t =
                     Proof.apply_tactic ~is_lhs:(Some false) new_t Proof.Reflexivity
                   in
                   let new_t = Proof.apply_assert rhs2 new_t in
                   let new_t = Proof.apply_tactic new_t (Proof.SimplIn "goal") in
                   Proof.apply_tactic ~is_lhs:(Some false) new_t Proof.Reflexivity
                 | [] -> t
                 | _ -> failwith "length has to be 1 or 4"
               in
               new_t, Proof.mk_assert tl, 0, assert_list
           in
           let original_goal = get_conj_goal next_t in
           let lemma_set =
             Prover.LemmaSet.add_list
               lemma_set
               (List.map (fun lemma -> original_goal, lemma, []) assert_list)
           in
           let new_state = Proof.apply_tactic new_t tactic in
           progress
             (Prover.WorkList.add
                prev_worklist
                ( new_t
                , tactic
                , Proof.apply_tactic new_t tactic
                , r
                , Prover.order_counter () ))
             (Prover.ProofSet.add new_state statelist)
             (next_goal :: stuck_goals)
             lemma_set
         | None -> progress prev_worklist statelist (next_goal :: stuck_goals) lemma_set)
       else
         progress
           (Prover.WorkList.merge prev_worklist worklist)
           statelist
           stuck_goals
           lemma_set)
;;

let proof_auto definition axiom program_a program_b goal =
  let definition = Parser.parse definition in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let definition = definition |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let env = definition @ program_a @ program_b in
  let axiom = axiom |> axiom_to_prop env in
  let init_t = Proof.create_t env ~proof:(axiom, [], []) () in
  let first_assertion = Proof.parse_tactic init_t goal in
  let next_t = Proof.apply_tactic init_t first_assertion in
  let worklist =
    Prover.WorkList.of_list
      [ init_t, first_assertion, next_t, 0, Prover.order_counter () ]
  in
  match progress worklist Prover.ProofSet.empty [] Prover.LemmaSet.empty with
  | _, Some proof, env ->
    print_endline "Proof Success";
    print_endline "Helper Functions";
    Ir.pp_t
      (List.filter
         (fun decl ->
            match decl with
            | Ir.TypeDecl _ -> false
            | _ -> String.starts_with ~prefix:"mk" (Ir.get_fun_name decl))
         env)
    |> print_endline;
    print_endline "Proof";
    List.iter print_endline (List.map Proof.pp_tactic proof);
    print_endline "Qed"
  | _, None, _ -> print_endline "Fail"
;;
