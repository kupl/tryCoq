let proof_top std_lib program_a program_b =
  let std_lib = Parser.parse std_lib in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let std_lib = std_lib |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  (* let _ = std_lib |> Ir.sexp_of_t |> Sexplib.Sexp.to_string |> print_endline in *)
  let _ = program_a |> Ir.sexp_of_t |> Sexplib.Sexp.to_string |> print_endline in
  let env = std_lib @ program_a @ program_b in
  let init_t = Proof.create_t env () in
  Proof.proof_top init_t
;;

(*
   let rec loop worklist old_lemma_list =
  let stuck_list, proof = Prover.(progress worklist ProofSet.empty ProofSet.empty) in
  match proof with
  | Some _ -> [], proof
  | None ->
    let lemma_list = Finder.make_lemmas stuck_list old_lemma_list in
    let _ = print_endline ("Lemma List : " ^ string_of_int (List.length lemma_list)) in
    let _ =
      List.iter
        (fun (t, lemma) ->
           let _, goal = Proof.get_first_state t in
           let _ = print_endline "Goal and Lemma" in
           Proof.pp_prop goal |> print_endline;
           Proof.pp_prop lemma |> print_endline)
        lemma_list
    in
    if List.is_empty lemma_list
    then failwith "lemma does not exists"
    else (
      let new_worklist =
        List.map (fun (t, goal) -> t, Proof.mk_assert goal, 0) lemma_list
        |> Prover.WorkList.of_list
      in
      loop new_worklist (lemma_list @ old_lemma_list))
;; *)
let rec split_tale lst =
  match lst with
  | [ tl ] -> [], tl
  | hd :: tl -> hd :: fst (split_tale tl), snd (split_tale tl)
  | _ -> failwith "length has to be greater than 1"
;;

let rec progress worklist statelist old_lemma_list =
  match Prover.WorkList.is_empty worklist with
  | true -> failwith "worklist is empty"
  | false ->
    let prev_worklist, work = Prover.WorkList.take_exn worklist in
    let t, tactic, r = work in
    let _ = print_endline "=================================================" in
    let i = Prover.synth_counter () in
    let _ = print_endline ("Progress: " ^ string_of_int i) in
    let _ = Proof.pp_t t |> print_endline in
    let _ =
      print_endline (">>> " ^ Proof.pp_tactic tactic ^ "(rank : " ^ string_of_int r ^ ")")
    in
    let next_t = Proof.apply_tactic t tactic in
    let _ = Proof.pp_t next_t |> print_endline in
    let _ = if i = 258 then Proof.proof_top next_t in
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
           (fun (_, tactic, _) -> Proof.pp_tactic tactic |> print_endline)
           worklist
       in
       if Prover.is_stuck worklist
       then (
         let lemma_list =
           Finder.make_lemmas_by_advanced_generalize next_t old_lemma_list
         in
         let _ =
           print_endline ("Lemma List : " ^ string_of_int (List.length lemma_list))
         in
         let _ =
           List.iter
             (fun (t, lemma_list) ->
                let _, goal, _ = Proof.get_first_state t in
                let _ = print_endline "Goal and Lemma" in
                Proof.pp_prop goal |> print_endline;
                lemma_list
                |> List.iter (fun lemma -> lemma |> Proof.pp_prop |> print_endline))
             lemma_list
         in
         let new_worklist =
           List.map
             (fun (t, assert_list) ->
                let heads, tl = split_tale assert_list in
                let new_t =
                  match heads with
                  | [ lhs1; lhs2; rhs1; rhs2 ] ->
                    let new_t = Proof.apply_assert lhs1 t in
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
                new_t, Proof.mk_assert tl, 0)
             lemma_list
         in
         let new_state_list =
           List.map (fun (t, tactic, _) -> Proof.apply_tactic t tactic) new_worklist
           |> Prover.ProofSet.of_list
         in
         progress
           (Prover.WorkList.add_list prev_worklist new_worklist)
           (Prover.ProofSet.union statelist new_state_list)
           (old_lemma_list @ lemma_list))
       else
         progress (Prover.WorkList.merge prev_worklist worklist) statelist old_lemma_list)
;;

(* let rec loop_advanced worklist statelist old_lemma_list =
  let stuck_list, proof, env = Prover.(progress worklist statelist ProofSet.empty) in
  match proof with
  | Some _ -> [], proof, env
  | None ->
    let lemma_list =
      Finder.make_lemmas_by_advanced_generalize stuck_list old_lemma_list
    in
    let _ = print_endline ("Lemma List : " ^ string_of_int (List.length lemma_list)) in
    let _ =
      List.iter
        (fun (t, lemma_list) ->
           let _, goal, _ = Proof.get_first_state t in
           let _ = print_endline "Goal and Lemma" in
           Proof.pp_prop goal |> print_endline;
           lemma_list |> List.iter (fun lemma -> lemma |> Proof.pp_prop |> print_endline))
        lemma_list
    in
    if List.is_empty lemma_list
    then failwith "lemma does not exists"
    else (
      let new_worklist =
        List.map
          (fun (t, assert_list) ->
             let heads, tl = split_tale assert_list in
             let new_t =
               match heads with
               | [ lhs1; lhs2; rhs1; rhs2 ] ->
                 let new_t = Proof.apply_assert lhs1 t in
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
               | _ -> failwith "length has to be 4"
             in
             new_t, Proof.mk_assert tl, 0)
          lemma_list
      in
      let new_state_list =
        List.map (fun (t, tactic, _) -> Proof.apply_tactic t tactic) new_worklist
        |> Prover.ProofSet.of_list
      in
      loop_advanced
        (new_worklist |> Prover.WorkList.of_list)
        new_state_list
        (lemma_list @ old_lemma_list))
;; *)

let proof_auto std_lib program_a program_b goal =
  let std_lib = Parser.parse std_lib in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let std_lib = std_lib |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let env = std_lib @ program_a @ program_b in
  let init_t = Proof.create_t env () in
  let goal = Proof.parse_tactic init_t goal in
  let worklist = Prover.WorkList.of_list [ init_t, goal, 0 ] in
  match progress worklist Prover.ProofSet.empty [] with
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
