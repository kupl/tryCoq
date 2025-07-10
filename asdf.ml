type natural =
  | Z
  | S of natural

let rec natural_eq n1 n2 =
  match n1, n2 with
  | Z, Z -> true
  | S n1', S n2' -> natural_eq n1' n2'
  | Z, S _ -> false
  | S _, Z -> false
;;

let rec natural_add n1 n2 =
  match n1 with
  | Z -> n2
  | S n1' -> S (natural_add n1' n2)
;;

let rec natural_sub n1 n2 =
  match n2 with
  | Z -> n1
  | S n2' ->
    (match n1 with
     | Z -> Z
     | S n1' -> natural_sub n1' n2')
;;

let rec natural_mul n1 n2 =
  match n1 with
  | Z -> Z
  | S n1' -> natural_add n2 (natural_mul n1' n2)
;;

let rec less_than n1 n2 =
  match n1, n2 with
  | Z, _ -> true
  | _, Z -> false
  | S n1', S n2' -> less_than n1' n2'
;;

type 'a list =
  | Nil
  | Cons of 'a * 'a list

type bool =
  | true
  | false

type int =
  | Zero
  | Pos of natural
  | Neg of natural

type string =
  | EmptyString
  | Concat of int * string

let not b =
  match b with
  | true -> false
  | false -> true
;;

let bool_eq b1 b2 =
  match b1, b2 with
  | true, true -> true
  | false, false -> true
  | _, _ -> false
;;

let int_eq i1 i2 =
  match i1, i2 with
  | Zero, Zero -> true
  | Pos n1', Pos n2' -> natural_eq n1' n2'
  | Neg n1', Neg n2' -> natural_eq n1' n2'
  | Zero, Pos Z -> true
  | Zero, Neg Z -> true
  | Pos Z, Zero -> true
  | Neg Z, Zero -> true
  | _, _ -> false
;;
