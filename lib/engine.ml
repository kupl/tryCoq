let proof_start program_a program_b func_name =
  let program_a, env = Parser.parse program_a Parser.init_env in
  let program_b, _ = Parser.parse program_b env in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  Proof.mk_proof program_a program_b func_name
;;

let proof_top program_a program_b =
  let program_a, env = Parser.parse program_a Parser.init_env in
  let program_b, env = Parser.parse program_b env in
  let program_a = program_a |> Ir.t_of_typedtree in
  let program_b = program_b |> Ir.t_of_typedtree in
  Proof.proof_top program_a program_b env
;;
