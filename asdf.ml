#load "str.cma"

open Str
open Str

let parse_forall_vars str =
  (* (변수명 : 타입) 또는 (변수명:타입)을 인식하는 정규식 *)
  let var_regex = regexp "(\\([^:]+\\) *: *\\([^\\)]+\\))" in
  let rec extract acc pos =
    try
      ignore (search_forward var_regex str pos);
      let var = matched_group 1 str in
      let typ = matched_group 2 str in
      extract ((var, typ) :: acc) (match_end ())
    with
    | Not_found -> List.rev acc
  in
  extract [] 0
;;

(* 테스트 *)
let test_str = "forall (var1: int) (var2: int list) (var3: int -> bool) (var4:None)"
let result = parse_forall_vars test_str;;

(* 결과 출력 *)
List.iter (fun (v, t) -> Printf.printf "%s: %s\n" v t) result
