let proof_top std_lib program_a program_b =
  let std_lib = Parser.parse std_lib in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let std_lib = std_lib |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let _ = program_a |> Ir.pp_t |> print_endline in
  let env = std_lib @ program_a @ program_b in
  let goal = "assert forall (a:nat) (b:nat), natadd_ta1 a b = natadd_ta2 a b" in
  let goal = Proof.parse_tactic Proof.empty_t goal env in
  let result = Prover.progress env [ Proof.empty_t, goal, 0 ] [] in
  match result with
  | _, [] -> print_endline "Proof Success"
  | _, _ ->
    print_endline "Proof Failed";
    Proof.pp_t result |> print_endline
;;
