open Sexplib.Std

type t = typ_decl list * fun_decl list [@@deriving sexp]

and fun_decl =
  | NonRec of name * expr
  | Rec of name * expr
[@@deriving sexp]

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
[@@deriving sexp]

and case = Case of pattern * expr list [@@deriving sexp]
and pattern = Pattern of name * name list [@@deriving sexp]
and typ_decl = (const * name list) list [@@deriving sexp]
and const = Constructor of name [@@deriving sexp]
and name = string [@@deriving sexp]

let string_of_t t = t |> sexp_of_t |> Sexplib.Sexp.to_string
