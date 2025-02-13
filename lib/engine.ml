let proof_top std_lib program_a program_b =
  let std_lib = Parser.parse std_lib in
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let std_lib = std_lib |> Ir.t_of_typedtree in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let _ = Ir.string_of_t program_a |> print_endline in
  let _ = Ir.string_of_t program_b |> print_endline in
  Proof.proof_top (std_lib @ program_a @ program_b)
;;
