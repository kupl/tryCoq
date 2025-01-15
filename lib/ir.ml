type t =
  | NonRec of name * expr
  | Rec of name * expr

and expr =
  | Match of expr * case list
  | LetIn of name * expr * expr
  | IfthenElse of expr * expr * expr
  | Call of t * expr list
  | Int of int
  | String of string
  | Bool of bool
  | List of expr list
  | Var of name

and case = Case of pattern * expr list
and pattern = Pattern of name * name list
and name = string

let ir_of_ocaml (typedtree : Parser.t) = ignore typedtree
