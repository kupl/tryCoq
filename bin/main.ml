let main =
  let program_a = "../dilemma-benchmark/dilemma-bench/dilemma/lambda/sol123.ml" in
  let program_b = "../dilemma-benchmark/dilemma-bench/dilemma/lambda/sol530.ml" in
  let function_name = "natadd" in
  let program_a = Dilemma.Utils.File.read_file_from_path program_a in
  let program_b = Dilemma.Utils.File.read_file_from_path program_b in
  let _ = Dilemma.Engine.proof_start program_a program_b function_name in
  ()
;;

(* ppx 어디갔어 민규야 *)

let () = main
