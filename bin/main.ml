let main =
  let program_a =
    "/home/mingyu_jo/dilemma-benchmark/dilemma-bench/dilemma/natadd/ta1.ml"
  in
  let program_b =
    "/home/mingyu_jo/dilemma-benchmark/dilemma-bench/dilemma/natadd/ta2.ml"
  in
  let function_name = "natadd" in
  let program_a = Dilemma.Utils.File.read_file_from_path program_a in
  let program_b = Dilemma.Utils.File.read_file_from_path program_b in
  let _ = Dilemma.Engine.proof_start program_a program_b function_name in
  ()
;;

let () = main
