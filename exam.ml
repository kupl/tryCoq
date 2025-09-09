type lambda =
  | V of string
  | P of string * lambda
  | C of lambda * lambda

let rec has_fv_ta lambda vars =
  match lambda with
  | V x -> List.mem x vars
  | P (x, e) -> has_fv_ta e (x :: vars)
  | C (e1, e2) -> has_fv_ta e1 vars && has_fv_ta e2 vars
;;

let rec has_fv_sub lambda vars =
  match lambda with
  | V x -> List.mem x vars
  | P (x, e) when List.mem x vars -> has_fv_sub e vars
  | P (x, e) -> has_fv_sub e (x :: vars)
  | C (e1, e2) -> has_fv_sub e1 vars && has_fv_sub e2 vars
;;

let check lambda = is_closed lambda []
