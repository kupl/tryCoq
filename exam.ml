type lambda =
  | V of string
  | C of lambda * lambda
  | P of string * lambda

let rec f_sol lam vars =
  match lam with
  | V x -> List.mem x vars
  | C (e1, e2) -> f_sol e1 vars && f_sol e2 vars
  | P (x, e) -> f_sol e (x :: vars)
;;

let main_sol lam = f_sol lam []

let rec valify var covers =
  match covers with
  | V _ -> false
  | P (x, e) -> if x = var then true else valify var e
  | C _ -> false
;;

let rec f_std lam vars =
  match lam with
  | V x -> valify x vars
  | C (e1, e2) -> f_std e1 vars && f_std e2 vars
  | P (x, e) -> f_std e (P (x, vars))
;;

let main_std lam = f_std lam (V "")

(* forall (lst:idlist), main lst = matinNew lst *)
