type 'a list =
  | Nil
  | Cons of 'a * 'a list

type bool =
  | true
  | false

type natural =
  | Z
  | S of natural

type int =
  | Zero
  | Pos of natural
  | Neg of natural

type string = String of int list

let not b =
  match b with
  | true -> false
  | false -> true
;;

let rec ( && ) b1 b2 =
  match b1 with
  | true -> b2
  | false -> false
;;

let rec ( || ) b1 b2 =
  match b1 with
  | true -> true
  | false -> b2
;;

let rec add n1 n2 =
  match n1 with
  | Z -> n2
  | S n1' -> S (add n1' n2)
;;

let rec sub n1 n2 =
  match n2 with
  | Z -> n1
  | S n2' ->
    (match n1 with
     | Z -> Z
     | S n1' -> sub n1' n2')
;;

let rec mul n1 n2 =
  match n1 with
  | Z -> Z
  | S n1' -> add n2 (mul n1' n2)
;;

let rec less_than n1 n2 =
  match n1, n2 with
  | Z, _ -> true
  | _, Z -> false
  | S n1', S n2' -> less_than n1' n2'
;;

let ( + ) i1 i2 =
  match i1, i2 with
  | Zero, _ -> i2
  | _, Zero -> i1
  | Pos n1', Pos n2' -> Pos (add n1' n2')
  | Neg n1', Neg n2' -> Neg (add n1' n2')
  | Pos n1', Neg n2' ->
    (match less_than n1' n2' with
     | true -> Neg (sub n2' n1')
     | false -> Pos (sub n1' n2'))
  | Neg n1', Pos n2' ->
    (match less_than n1' n2' with
     | true -> Pos (sub n2' n1')
     | false -> Neg (sub n1' n2'))
;;

let ( - ) i1 i2 =
  match i1, i2 with
  | Zero, _ -> i2
  | _, Zero -> i1
  | Pos n1', Pos n2' ->
    (match less_than n1' n2' with
     | true -> Neg (sub n2' n1')
     | false -> Pos (sub n1' n2'))
  | Neg n1', Neg n2' ->
    (match less_than n1' n2' with
     | true -> Pos (sub n2' n1')
     | false -> Neg (sub n1' n2'))
  | Pos n1', Neg n2' -> Pos (add n1' n2')
  | Neg n1', Pos n2' -> Neg (add n1' n2')
;;

let rec ( @ ) l1 l2 =
  match l1 with
  | Nil -> l2
  | Cons (hd, tl) -> Cons (hd, tl @ l2)
;;

let rec mem x l =
  match l with
  | Nil -> false
  | Cons (hd, tl) ->
    (match hd = x with
     | true -> true
     | false -> mem x tl)
;;
