open Sexplib.Std

type t = (fact list * goal) list [@@deriving sexp]
and fact = prop [@@deriving sexp]
and goal = prop [@@deriving sexp]

and prop =
  | Eq of expr * expr
  | Le of expr * expr
  | Lt of expr * expr
  | And of prop * prop
  | Or of prop * prop
  | Not of prop
  | Forall of string * prop
  | Imply of prop * prop
[@@deriving sexp]

and expr = Ir.expr [@@deriving sexp]

type theorem = tactic list * goal [@@deriving sexp]

and tactic =
  | ApplyInAt of string * string * int
  | Intro of string
  | RewriteInAt of string * string * int
  | Induction of string
  | Case of string
  | SimplInAt of string * string * int
[@@deriving sexp]

let apply_tactic tactic proof =
  ignore proof;
  match tactic with
  | ApplyInAt (fact, goal, i) -> ignore (fact, goal, i)
  | Intro name -> ignore name
  | RewriteInAt (fact, goal, i) -> ignore (fact, goal, i)
  | Induction name -> ignore name
  | Case name -> ignore name
  | SimplInAt (fact, goal, i) -> ignore (fact, goal, i)
;;

let string_of_t t = t |> sexp_of_t |> Sexplib.Sexp.to_string
let string_of_theorem t = t |> sexp_of_theorem |> Sexplib.Sexp.to_string
let string_of_tactic t = t |> sexp_of_tactic |> Sexplib.Sexp.to_string
let string_of_prop p = p |> sexp_of_prop |> Sexplib.Sexp.to_string
let string_of_expr e = e |> sexp_of_expr |> Sexplib.Sexp.to_string
