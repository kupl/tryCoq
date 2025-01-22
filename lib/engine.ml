let proof_start program_a program_b func_name =
  let program_a = Parser.parse program_a in
  let program_b = Parser.parse program_b in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  let _ = program_a |> Ir.pp_t |> print_endline in
  let _ = program_b |> Ir.pp_t |> print_endline in
  Proof.mk_theorem program_a program_b func_name
;;
