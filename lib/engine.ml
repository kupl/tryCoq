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
    | hd :: tl -> aux tl (hd :: result)
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

let is_lhs lemma =
  let lhs = Proof.get_lhs lemma in
  match lhs.Ir.desc with
  | Ir.Call (fname, _) -> String.starts_with ~prefix:"mk_lhs" fname
  | _ -> false
;;

let count_tale_rewrite_simpl tactics =
  let rec count_tale_rewrite_simpl tactics =
    match tactics with
    | hd :: tl ->
      (match hd with
       | Proof.RewriteInAt _ | Proof.RewriteReverse _ -> 1 + count_tale_rewrite_simpl tl
       | Proof.SimplIn _ -> 1 + count_tale_rewrite_simpl tl
       | _ -> 1)
    | [] -> 1
  in
  count_tale_rewrite_simpl tactics
;;

let get_previous_state (t : Prover.proof_node) statelist =
  let prev_tactics = Proof.get_tactic_history t.t in
  let index = count_tale_rewrite_simpl prev_tactics in
  let rec get_previous_state (t : Prover.proof_node) statelist i =
    match i with
    | 1 -> [ t ]
    | _ ->
      let parent_id = t.parent in
      let parent_node = Prover.ProofSet.find parent_id statelist in
      t :: get_previous_state parent_node statelist (i - 1)
  in
  get_previous_state t statelist index
;;

let apply_and_get_lemmas (new_t : Prover.proof_node) assert_list (work : Prover.workelt) =
  match assert_list with
  | [] ->
    let prev_lemma_list = Proof.get_lemma_stack work.t.t in
    let new_lemma_list = Proof.get_lemma_stack work.next_t.t in
    let assert_list =
      List.filter (fun x -> not (List.mem x prev_lemma_list)) new_lemma_list
    in
    new_t, Proof.SimplIn "goal", -1, assert_list |> List.map snd
  | _ ->
    let new_env = List.filter (fun x -> not (List.mem x work.next_t.t.env)) new_t.t.env in
    (match new_env with
     | [] ->
       let heads, tl = split_tale assert_list in
       let new_t =
         List.fold_left
           (fun t lemma -> Prover.just_apply_tactic t (Proof.Assert lemma))
           new_t
           heads
       in
       new_t, Proof.mk_assert tl, 0, assert_list
     | _ ->
       let _ = print_endline "New Env" in
       let _ = new_env |> Ir.pp_t |> print_endline in
       let _ = print_endline "Lemma List" in
       let _ = assert_list |> List.iter (fun x -> Proof.pp_prop x |> print_endline) in
       let _ = print_endline "End of Lemma List" in
       let heads, tl = split_tale assert_list in
       let new_t =
         List.fold_left
           (fun t lemma ->
              let t = Prover.just_apply_tactic t (Proof.Assert lemma) in
              Prover.just_apply_tactic ~is_lhs:(Some (is_lhs lemma)) t Proof.Reflexivity)
           new_t
           heads
       in
       new_t, Proof.mk_assert tl, 0, assert_list)
;;

let rec progress worklist statelist lemma_set =
  match Prover.WorkList.is_empty worklist with
  | true -> failwith "worklist is empty"
  | false ->
    let prev_worklist, work = Prover.WorkList.take_exn worklist in
    let _ = print_endline "=================================================" in
    let i = progress_counter () in
    let _ = print_endline ("Progress: " ^ string_of_int i) in
    let _ = Proof.pp_t work.t.t |> print_endline in
    let _ =
      print_endline
        (">>> " ^ Proof.pp_tactic work.tactic ^ "(rank : " ^ string_of_int work.rank ^ ")")
    in
    let _ = Proof.pp_t work.next_t.t |> print_endline in
    (* let _ = if i = 11 then Proof.proof_top work.next_t.t in *)
    let lemma_set =
      match is_end_of_conj work.t.t work.next_t.t with
      | true ->
        let lemma_list = Proof.get_lemma_stack work.next_t.t in
        let lemma = List.hd (List.rev lemma_list) |> snd in
        let tactics = get_proof_of_lemma work.next_t.t in
        let original_goal = get_conj_goal work.t.t in
        let lemma_set = Prover.LemmaSet.add (original_goal, lemma, tactics) lemma_set in
        lemma_set
      | false -> lemma_set
    in
    (match work.next_t.t.proof with
     | _, [], proof -> Prover.ProofSet.empty, Some proof
     | _ ->
       let prev_worklist =
         match work.tactic with
         | Proof.Reflexivity | Proof.Discriminate ->
           Prover.deduplicate_worklist prev_worklist work.next_t.t
         | _ -> prev_worklist
       in
       let tactic_list = Prover.mk_candidates work.next_t.t in
       let worklist, statelist, is_stuck =
         Prover.prune_rank_worklist_update_state_list work.next_t tactic_list statelist
       in
       let _ =
         print_endline
           ("Tactic List : "
            ^ string_of_int (List.length (worklist |> Prover.WorkList.to_list)))
       in
       let _ =
         Prover.WorkList.iter
           (fun elt ->
              Proof.pp_tactic elt.tactic ^ "(rank:" ^ string_of_int elt.rank ^ ")"
              |> print_endline)
           worklist
       in
       (match is_stuck with
        | true ->
          let previous_states = get_previous_state work.next_t statelist in
          let t_lemmas_list =
            List.map (fun t -> Finder.find_lemma t lemma_set) previous_states
            |> List.concat
          in
          let pattern_lemmas =
            List.filter (fun (_, lemmas) -> List.length lemmas > 1) t_lemmas_list
          in
          (match pattern_lemmas with
           | [] ->
             (match t_lemmas_list with
              | (new_t, assert_list) :: _ ->
                let new_t, tactic, r, assert_list =
                  apply_and_get_lemmas new_t assert_list work
                in
                let _ = new_t.t |> Proof.pp_t |> print_endline in
                let original_goal = get_conj_goal work.next_t.t in
                let lemma_set =
                  Prover.LemmaSet.add_list
                    lemma_set
                    (List.map (fun lemma -> original_goal, lemma, []) assert_list)
                in
                let new_state = Prover.just_apply_tactic new_t tactic in
                progress
                  (Prover.WorkList.add
                     prev_worklist
                     { t = new_t
                     ; tactic
                     ; next_t = new_state
                     ; rank = r
                     ; order = Prover.order_counter ()
                     })
                  (Prover.ProofSet.add new_state.id new_state statelist)
                  lemma_set
              | [] -> progress prev_worklist statelist lemma_set)
           | _ ->
             let new_worklist, new_state_list, new_lemma_set =
               List.fold_left
                 (fun (worklist, statelist, lemma_set) (new_t, assert_list) ->
                    let new_t, tactic, r, assert_list =
                      apply_and_get_lemmas new_t assert_list work
                    in
                    let _ = new_t.t |> Proof.pp_t |> print_endline in
                    let original_goal = get_conj_goal work.next_t.t in
                    let lemma_set =
                      Prover.LemmaSet.add_list
                        lemma_set
                        (List.map (fun lemma -> original_goal, lemma, []) assert_list)
                    in
                    let new_state = Prover.just_apply_tactic new_t tactic in
                    let new_state_list =
                      Prover.ProofSet.add new_state.id new_state statelist
                    in
                    let new_worklist =
                      Prover.WorkList.add
                        worklist
                        { t = new_t
                        ; tactic
                        ; next_t = new_state
                        ; rank = r
                        ; order = Prover.order_counter ()
                        }
                    in
                    new_worklist, new_state_list, lemma_set)
                 (prev_worklist, statelist, lemma_set)
                 pattern_lemmas
             in
             progress new_worklist new_state_list new_lemma_set)
        | false ->
          progress (Prover.WorkList.merge prev_worklist worklist) statelist lemma_set))
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
  let id = Prover.get_id () in
  let (init_t : Prover.proof_node) = Prover.{ t = init_t; id; parent = -1 } in
  let next_t = Prover.just_apply_tactic init_t first_assertion in
  let worklist =
    Prover.WorkList.of_list
      [ { t = init_t
        ; tactic = first_assertion
        ; next_t
        ; rank = 0
        ; order = Prover.order_counter ()
        }
      ]
  in
  match progress worklist Prover.ProofSet.empty Prover.LemmaSet.empty with
  | _, Some proof ->
    print_endline "Proof Success";
    print_endline "Proof";
    List.iter print_endline (List.map Proof.pp_tactic proof);
    print_endline "Qed"
  | _, None -> print_endline "Fail"
;;

let proof_top definition axiom program_a program_b =
  let definition = Parser.parse definition in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let definition = definition |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let env = definition @ program_a @ program_b in
  let axiom = axiom |> axiom_to_prop env in
  let init_t = Proof.create_t env ~proof:(axiom, [], []) () in
  Proof.proof_top init_t
;;
