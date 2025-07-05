let main =
  let definition = "prerequisites/definition.ml" in
  let axiom = "prerequisites/axiom" in
  let program_a = "../dilemma-benchmark/dilemma-bench/dilemma/lambda/ta1.ml" in
  let program_b = "../dilemma-benchmark/dilemma-bench/dilemma/lambda/sol530.ml" in
  let definition = Dilemma.Utils.File.read_file_from_path definition in
  let axiom = Dilemma.Utils.File.read_file_from_path axiom in
  let program_a = Dilemma.Utils.File.read_file_from_path program_a in
  let program_b = Dilemma.Utils.File.read_file_from_path program_b in
  let _ = print_endline "Choose the proof type :" in
  let _ = print_endline "1) Interactive Mode \t 2) Auto Mode" in
  let s = read_line () in
  if s = "1"
  then (
    let _ = Dilemma.Engine.proof_top definition axiom program_a program_b in
    ())
  else (
    let _ = print_string "Enter the goal : " in
    let goal = read_line () in
    let _ = Dilemma.Engine.proof_auto definition axiom program_a program_b goal in
    ())
;;

(* ppx 어디갔어 민규야 *)

let () = main
