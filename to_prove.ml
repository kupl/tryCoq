let add = fun a b -> a + b
let dilemma_add = [@@dilemma.function]
let add = Dilemma.Function ("a", Dilemma.Function ("b", Dilemma.Add (Dilemma.Var "a", Dilemma.Var "b")))
(* let add = Dilemma.Function.t_of_ocaml add *)
let double = fun x -> x * 2

assert Dilemma.check
  (Dilemma.Forall (Dilemma.Nat, "x", 
      Dilemma.Eq (
        Dilemma.App (Dilemma.App (add, Dilemma.Var "x"), Dilemma.Var "x"),
        Dilemma.App (double, Dilemma.Var "x"))))

type t [@@deriving compare, equal, sexp]

type t
let compare: t -> t -> int
let equal: t -> t -> bool
let sexp_of_t: t -> Sexp.t
