type unit = Unit

type 'a list =
  | Nil
  | Cons of 'a * 'a list

type natural =
  | Z
  | S of natural

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

type ('a, 'b) tuple2 = Tuple2 of 'a * 'b
type ('a, 'b, 'c) tuple3 = Tuple3 of 'a * 'b * 'c
type ('a, 'b, 'c, 'd) tuple4 = Tuple4 of 'a * 'b * 'c * 'd

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
  | _, Z -> false
  | Z, S _ -> true
  | S n1', S n2' -> less_than n1' n2'
;;

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

let rec list_eq l1 l2 =
  match l1, l2 with
  | Nil, Nil -> true
  | Cons (hd1, tl1), Cons (hd2, tl2) ->
    (match hd1 = hd2 with
     | true -> list_eq tl1 tl2
     | false -> false)
  | _, _ -> false
;;

let rec string_eq s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> true
     | _ -> false)
  | Concat (i1, s1') ->
    (match s2 with
     | EmptyString -> false
     | Concat (i2, s2') ->
       (match int_eq i1 i2 with
        | true -> string_eq s1' s2'
        | false -> false))
;;

let ( && ) b1 b2 =
  match b1 with
  | true -> b2
  | false -> false
;;

let ( || ) b1 b2 =
  match b1 with
  | true -> true
  | false -> b2
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
