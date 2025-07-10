type t = Typedtree.structure

let _ = Compmisc.init_path ()

let parse src =
  let env = Compmisc.initial_env () in
  let ocaml_ast = src |> Lexing.from_string |> Parse.implementation in
  let typed_tree, _, _, _, _ = Typemod.type_structure env ocaml_ast in
  typed_tree
;;

(* let parse_expr (env : Env.t) (src : string) : Typedtree.expression =
  let pexpr = src |> Lexing.from_string |> Parse.expression in
  let t_expr = Typecore.type_expression env pexpr in
  t_expr
;; *)
