type t = Typedtree.structure

let parse src =
  let ocaml_ast = src |> Lexing.from_string |> Parse.implementation in
  let typed_tree, _, _, _, _ =
    let _ = Ocaml_common.Compmisc.init_path () in
    let env = Compmisc.initial_env () in
    Ocaml_common.Typemod.type_structure env ocaml_ast
  in
  typed_tree
;;
