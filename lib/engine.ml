let proof_top std_lib program_a program_b =
  let std_lib = Parser.parse std_lib in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let std_lib = std_lib |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let env = std_lib @ program_a @ program_b in
  Proof.proof_top env
;;

let rec loop env worklist statelist =
  let stuck_list, proof = Prover.progress env worklist statelist in
  match proof with
  | Some _ -> [], proof
  | None ->
    let lemma_list = Finder.make_lemmas env stuck_list in
    if List.is_empty lemma_list
    then failwith "lemma does not exists"
    else (
      let new_worklist =
        List.map (fun (t, goal) -> t, Proof.mk_assert goal, 0) lemma_list
      in
      loop env new_worklist stuck_list)
;;

let proof_auto std_lib program_a program_b goal =
  let std_lib = Parser.parse std_lib in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let std_lib = std_lib |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let env = std_lib @ program_a @ program_b in
  let goal = Proof.parse_tactic Proof.empty_t goal env in
  match loop env [ Proof.empty_t, goal, 0 ] [] with
  | _, Some proof ->
    print_endline "Proof Success";
    print_endline "Proof";
    List.iter print_endline (List.map Proof.pp_tactic proof);
    print_endline "Qed"
  | _, None -> print_endline "Fail"
;;
