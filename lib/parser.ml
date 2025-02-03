type t = Typedtree.structure

let init_env =
  let _ = Compmisc.init_path () in
  Compmisc.initial_env ()
;;

let parse src env =
  let ocaml_ast = src |> Lexing.from_string |> Parse.implementation in
  let typed_tree, _, _, _, new_env = Typemod.type_structure env ocaml_ast in
  typed_tree, new_env
;;

let parse_expr (env : Env.t) (src : string) : Typedtree.expression =
  let pexpr = src |> Lexing.from_string |> Parse.expression in
  let t_expr = Typecore.type_expression env pexpr in
  t_expr
;;
