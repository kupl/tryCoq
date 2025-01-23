let proof_start program_a program_b func_name =
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  Proof.mk_proof program_a program_b func_name
;;
