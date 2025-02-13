let proof_top std_lib program_a program_b =
  let std_lib = Parser.parse std_lib in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let std_lib = std_lib |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  Proof.proof_top (std_lib @ program_a @ program_b)
;;
