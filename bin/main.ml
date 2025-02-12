let main =
  let std_lib = "primitive_type/std_lib.ml" in
  let program_a = "../dilemma-benchmark/dilemma-bench/dilemma/filter/ta1.ml" in
  let program_b = "../dilemma-benchmark/dilemma-bench/dilemma/filter/sol121.ml" in
  let std_lib = Dilemma.Utils.File.read_file_from_path std_lib in
  let program_a = Dilemma.Utils.File.read_file_from_path program_a in
  let program_b = Dilemma.Utils.File.read_file_from_path program_b in
  let _ = Dilemma.Engine.proof_top std_lib program_a program_b in
  ()
;;

(* ppx 어디갔어 민규야 *)

let () = main
