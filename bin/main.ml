let main =
  let program_a = "../dilemma-benchmark/dilemma-bench/dilemma/natadd/ta1.ml" in
  let program_b = "../dilemma-benchmark/dilemma-bench/dilemma/natadd/sol4.ml" in
  let program_a = Dilemma.Utils.File.read_file_from_path program_a in
  let program_b = Dilemma.Utils.File.read_file_from_path program_b in
  let _ = Dilemma.Engine.proof_top program_a program_b in
  ()
;;

(* ppx 어디갔어 민규야 *)

let () = main
