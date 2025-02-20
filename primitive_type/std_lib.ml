type 'a list =
  | Nil
  | Cons of 'a * 'a list

type ('a, 'b) tuple2 = Tuple2 of 'a * 'b

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

let ( + ) i1 i2 =
  match i1, i2 with
  | Zero, _ -> i2
  | _, Zero -> i1
  | Pos n1', Pos n2' -> Pos (natural_add n1' n2')
  | Neg n1', Neg n2' -> Neg (natural_add n1' n2')
  | Pos n1', Neg n2' ->
    (match less_than n1' n2' with
     | true -> Neg (natural_sub n2' n1')
     | false -> Pos (natural_sub n1' n2'))
  | Neg n1', Pos n2' ->
    (match less_than n1' n2' with
     | true -> Pos (natural_sub n2' n1')
     | false -> Neg (natural_sub n1' n2'))
;;

let ( - ) i1 i2 =
  match i1, i2 with
  | Zero, _ -> i2
  | _, Zero -> i1
  | Pos n1', Pos n2' ->
    (match less_than n1' n2' with
     | true -> Neg (natural_sub n2' n1')
     | false -> Pos (natural_sub n1' n2'))
  | Neg n1', Neg n2' ->
    (match less_than n1' n2' with
     | true -> Pos (natural_sub n2' n1')
     | false -> Neg (natural_sub n1' n2'))
  | Pos n1', Neg n2' -> Pos (natural_add n1' n2')
  | Neg n1', Pos n2' -> Neg (natural_add n1' n2')
;;

let ( < ) i1 i2 =
  match i1, i2 with
  | Zero, Pos _ -> true
  | Zero, _ -> false
  | Neg _, Zero -> true
  | _, Zero -> false
  | Pos n1', Pos n2' -> less_than n1' n2'
  | Neg n1', Neg n2' -> less_than n2' n1'
  | Pos n1', Neg n2' -> false
  | Neg n1', Pos n2' -> true
;;

let ( > ) i1 i2 = i2 < i1
let ( >= ) i1 i2 = not (i1 < i2)
let ( <= ) i1 i2 = not (i1 > i2)

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

let rec filter predicate list =
  match list with
  | Nil -> Nil
  | Cons (hd, tl) ->
    (match predicate hd with
     | true -> Cons (hd, filter predicate tl)
     | false -> filter predicate tl)
;;

let rec for_all predicate list =
  match list with
  | Nil -> true
  | Cons (hd, tl) ->
    (match predicate hd with
     | true -> for_all predicate tl
     | false -> false)
;;

let rec rev_aux acc list =
  match list with
  | Nil -> acc
  | Cons (hd, tl) -> rev_aux (Cons (hd, acc)) tl
;;

let rec rev list = rev_aux Nil list

let rec fold_left f acc list =
  match list with
  | Nil -> acc
  | Cons (hd, tl) -> fold_left f (f acc hd) tl
;;
