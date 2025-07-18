open Sexplib.Std

type t = decl list [@@deriving sexp]

and decl =
  | NonRec of name * name list * expr
  | Rec of name * name list * expr
  | TypeDecl of name * typ list * typ_decl
[@@deriving sexp]

and typ_decl = (constr * typ list) list [@@deriving sexp]
and constr = Constructor of name [@@deriving sexp]

and expr =
  { desc : expr_desc
  ; typ : typ
  }
[@@deriving sexp]

and expr_desc =
  | Match of expr list * case list
  | LetIn of (name * expr) list * expr
  | Call of name * expr list
  | Var of name
[@@deriving sexp]

and typ =
  | Talgebraic of name * typ list
  | Tany
  | Tarrow of typ list
[@@deriving sexp]

and case = Case of pattern * expr [@@deriving sexp]

and pattern =
  | Pat_Constr of name * pattern list
  | Pat_Var of name
  | Pat_Expr of expr
  | Pat_Tuple of pattern list
  | Pat_any
[@@deriving sexp]

and name = string [@@deriving sexp, eq, ord]

let counter = ref 0

let get_global_cnt () =
  counter := !counter + 1;
  !counter
;;

let get_fun_name decl =
  match decl with
  | Rec (name, _, _) | NonRec (name, _, _) -> name
  | _ -> failwith "t is no function"
;;

let get_mk_index t =
  List.fold_left
    (fun acc decl ->
       match decl with
       | NonRec (name, _, _) | Rec (name, _, _) ->
         if String.starts_with ~prefix:"mk_lhs" name then acc + 1 else acc
       | _ -> acc)
    0
    t
;;

let get_is_rec_list decl =
  match decl with
  | NonRec _ | Rec _ -> failwith "get_is_rec_list: input should be a type declaration"
  | TypeDecl (name, _, typ_decl) ->
    List.map
      (fun (_, typ_list) ->
         List.exists
           (fun typ ->
              match typ with
              | Talgebraic (typ_name, _) -> name = typ_name
              | _ -> false)
           typ_list)
      typ_decl
;;

let rec collect_var_in_pat pat =
  match pat with
  | Pat_Constr (_, patterns) -> List.map collect_var_in_pat patterns |> List.concat
  | Pat_Var name -> [ name ]
  | Pat_Tuple patterns -> List.map collect_var_in_pat patterns |> List.concat
  | _ -> []
;;

let rec collect_var_in_expr expr =
  match expr.desc with
  | Var name -> [ name ]
  | Call (_, args) -> List.map collect_var_in_expr args |> List.concat
  | Match (match_list, cases) ->
    let match_vars = List.map collect_var_in_expr match_list |> List.concat in
    let case_vars =
      List.map
        (fun (Case (pat, e)) ->
           let pat_vars = collect_var_in_pat pat in
           collect_var_in_expr e |> List.filter (fun var -> not (List.mem var pat_vars)))
        cases
      |> List.concat
    in
    match_vars @ case_vars
  | LetIn (bindings, body) ->
    let binding_vars =
      List.map (fun (_, e) -> collect_var_in_expr e) bindings |> List.concat
    in
    binding_vars @ collect_var_in_expr body
;;

let rec nth_tale n lst =
  if n = 0
  then lst
  else (
    match lst with
    | [] -> failwith "n is too big"
    | _ :: tl -> nth_tale (n - 1) tl)
;;

let rec expr_of_nat (n : int) : expr_desc =
  if n < 0
  then failwith "n should not be negative"
  else if n = 0
  then Call ("Z", [])
  else Call ("S", [ { desc = expr_of_nat (n - 1); typ = Talgebraic ("natural", []) } ])
;;

let expr_of_int (i : int) : expr_desc =
  if i = 0
  then Call ("Zero", [])
  else if i > 0
  then Call ("Pos", [ { desc = expr_of_nat i; typ = Talgebraic ("natural", []) } ])
  else Call ("Neg", [ { desc = expr_of_nat (-i); typ = Talgebraic ("natural", []) } ])
;;

let rec expr_of_pattern pattern =
  match pattern with
  | Pat_Constr (name, patterns) ->
    Call
      ( name
      , List.map (fun pattern -> { desc = expr_of_pattern pattern; typ = Tany }) patterns
      )
  | Pat_Var name -> Var name
  | _ -> failwith "Not implemented"
;;

let char_of_ascii i = Char.chr i
let ascii_of_char ch = Char.code ch

let expr_of_string string =
  let char_list =
    List.init (String.length string) (fun i -> String.get string i |> ascii_of_char)
  in
  let str =
    List.fold_right
      (fun c acc ->
         { desc =
             Call
               ( "Concat"
               , [ { desc = expr_of_int (c - 97); typ = Talgebraic ("int", []) }; acc ] )
         ; typ = Talgebraic ("string", [])
         })
      char_list
      { desc = Call ("EmptyString", []); typ = Talgebraic ("string", []) }
  in
  str.desc
;;

let rec oint_of_nat expr =
  match expr.desc with
  | Call ("Z", []) -> 0
  | Call ("S", [ n ]) -> 1 + oint_of_nat n
  | _ -> failwith "oint_of_nat: not a natural number expression"
;;

let oint_of_int expr =
  match expr.desc with
  | Call ("Zero", []) -> 0
  | Call ("Pos", [ n ]) -> oint_of_nat n
  | Call ("Neg", [ n ]) -> -oint_of_nat n
  | _ -> failwith "oint_of_int: not an integer expression"
;;

let rec pp_string expr =
  match expr.desc with
  | Call ("EmptyString", []) -> ""
  | Call ("Concat", [ ascii; tale ]) ->
    let ascii = oint_of_int ascii + 97 in
    (char_of_ascii ascii |> Char.escaped) ^ pp_string tale
  | _ -> failwith "pp_string: not a string expression"
;;

let string_of_t t = t |> sexp_of_t |> Sexplib.Sexp.to_string

let rec pp_decl decl =
  match decl with
  | NonRec (name, args, body) ->
    "let " ^ name ^ " " ^ String.concat " " args ^ " =\n" ^ pp_expr body
  | Rec (name, args, body) ->
    "let rec " ^ name ^ " " ^ String.concat " " args ^ " =\n" ^ pp_expr body
  | TypeDecl (name, args, typ_decl) ->
    let args = List.map (fun arg -> pp_typ arg) args in
    "type " ^ String.concat " " args ^ name ^ " = " ^ pp_typ_decl typ_decl

and pp_t t : string = (List.map pp_decl t |> String.concat "\n;;\n") ^ "\n;;"

and pp_expr expr =
  match expr.desc with
  | Match (match_list, cases) ->
    (match match_list with
     | [ e1 ] ->
       (match e1.typ, cases with
        | ( Talgebraic ("bool", [])
          , [ Case (Pat_Constr ("true", []), e2); Case (Pat_Constr ("false", []), e3) ] )
          -> "if " ^ pp_expr e1 ^ " then " ^ pp_expr e2 ^ " else " ^ pp_expr e3
        | _ ->
          "match ("
          ^ pp_expr e1
          ^ ") with\n| "
          ^ String.concat "\n| " (List.map pp_case cases))
     | _ ->
       "match ("
       ^ String.concat ", " (List.map pp_expr match_list)
       ^ ") with\n| "
       ^ String.concat "\n| " (List.map pp_case cases))
  | LetIn (bindings, body) ->
    "let "
    ^ String.concat
        " and "
        (List.map (fun (name, body) -> name ^ " = " ^ pp_expr body) bindings)
    ^ " in "
    ^ pp_expr body
  | Call (name, args) ->
    (match name with
     | "@" | "=" ->
       "("
       ^ pp_expr (List.hd args)
       ^ " "
       ^ name
       ^ " "
       ^ pp_expr (List.hd (List.tl args))
       ^ ")"
     | "Concat" | "EmptyString" -> "\"" ^ pp_string expr ^ "\""
     | "Cons" | "Nil" -> "(" ^ pp_list expr ^ ")"
     | "Pos" | "Zero" | "Neg" -> pp_int expr
     | "S" | "Z" -> pp_nat expr
     | _ ->
       (match args with
        | [] -> name
        | _ ->
          name
          ^ " "
          ^ String.concat " " (List.map (fun arg -> "(" ^ pp_expr arg ^ ")") args)))
  | Var name -> name

and pp_case case =
  match case with
  | Case (pattern, expr) -> pp_pattern pattern ^ " -> " ^ pp_expr expr

and pp_pattern pattern =
  match pattern with
  | Pat_Constr (name, patterns) ->
    name ^ " " ^ String.concat " " (List.map pp_pattern patterns)
  | Pat_Var name -> name
  | Pat_Expr expr -> pp_expr expr
  | Pat_Tuple patterns -> "(" ^ String.concat ", " (List.map pp_pattern patterns) ^ ")"
  | Pat_any -> "_"

and pp_typ_decl typ_decl =
  List.map
    (fun (const, args) ->
       match const with
       | Constructor name ->
         (match args with
          | [] -> name
          | _ -> name ^ " of " ^ String.concat " * " (List.map pp_typ args)))
    typ_decl
  |> String.concat " | "

and pp_typ typ =
  match typ with
  | Talgebraic (name, args) ->
    String.concat " " (List.map pp_typ args)
    ^ (if List.is_empty args then "" else " ")
    ^ name
  | Tany -> "any"
  | Tarrow l -> String.concat " -> " (List.map pp_typ l)

and pp_list expr =
  match expr.desc with
  | Call ("Nil", []) -> "Nil"
  | Call ("Cons", [ head; tail ]) ->
    let head_str = pp_expr head in
    let tail_str = pp_expr tail in
    head_str ^ "::" ^ tail_str
  | _ -> failwith "pp_list: not a list expression"

and pp_int expr =
  match expr.desc with
  | Call ("Zero", []) -> "0"
  | Call ("Pos", [ n ]) -> pp_expr n
  | Call ("Neg", [ n ]) -> "-" ^ pp_expr n
  | _ -> failwith "pp_int: not an integer expression"

and pp_nat expr =
  match expr.desc with
  | Call ("Z", []) -> "0"
  | Call ("S", [ n ]) ->
    if is_constant n then string_of_int (oint_of_nat n) else "S(" ^ pp_expr n ^ ")"
  | _ -> failwith "pp_nat: not a natural number expression"

and is_constant expr =
  match expr.desc with
  | Call ("Z", []) -> true
  | Call ("S", [ n ]) -> is_constant n
  | _ -> false
;;

let var_of_typ typ =
  match typ with
  | Talgebraic (name, args) ->
    String.concat "_" (List.map pp_typ args)
    ^ (if List.is_empty args then "" else "_")
    ^ name
  | Tany -> "any"
  | Tarrow l -> String.concat "2" (List.map pp_typ l)
;;

let rec parse_typ (s : string) : typ =
  let s = String.trim s in
  if String.contains s '-' && String.contains s '>'
  then (
    (* 가장 바깥쪽의 "->" 연산자를 기준으로 나눔 *)
    let parts = Str.split (Str.regexp " *-> *") s in
    Tarrow (List.map parse_typ parts))
  else if String.contains s '(' && String.contains s ')'
  then (
    (* 괄호가 있는 경우, 괄호 내부를 재귀적으로 파싱 *)
    let s = String.sub s 1 (String.length s - 2) in
    parse_typ s)
  else (
    (* 공백을 기준으로 왼쪽에서 오른쪽으로 타입 인자 적용 *)
    let parts = Str.split (Str.regexp " +") s in
    match parts with
    | [] -> failwith "Invalid type"
    | base :: args ->
      let acc = if String.get base 0 = '\'' then Tany else Talgebraic (base, []) in
      List.fold_left
        (fun acc arg ->
           if String.get arg 0 = '\''
           then (
             let _ = failwith "asdf " in
             Tany)
           else Talgebraic (arg, [ acc ]))
        acc
        args)
;;

let rec t_of_typedtree typ_tree : t =
  let items = typ_tree.Typedtree.str_items in
  let decls = List.map (fun item -> decl_of_item item) items |> List.flatten in
  decls

and typ_of_ctype ctype =
  match ctype.Typedtree.ctyp_desc with
  | Ttyp_any -> Tany
  | Ttyp_var _ -> Tany
  | Ttyp_constr (_, lident, lst) ->
    Talgebraic (Longident.last lident.txt, List.map typ_of_ctype lst)
  | Ttyp_tuple l ->
    failwith ("tuple" ^ string_of_int (List.length l) ^ " is not implemented")
  | _ -> failwith "Not implemented"

and decl_of_item item : decl list =
  match item.Typedtree.str_desc with
  | Typedtree.Tstr_type (_, typ_decls) ->
    let name_list = List.map (fun decl -> decl.Typedtree.typ_name.txt) typ_decls in
    let args_list =
      List.map
        (fun decl ->
           decl.Typedtree.typ_params |> List.map (fun ctyp -> ctyp |> fst |> typ_of_ctype))
        typ_decls
    in
    let constr_list =
      List.map
        (fun decl ->
           match decl.Typedtree.typ_kind with
           | Ttype_variant constructor_list ->
             List.map
               (fun constr_decl ->
                  let constr_name = constr_decl.Typedtree.cd_name.txt in
                  let args_list =
                    match constr_decl.Typedtree.cd_args with
                    | Cstr_tuple args_list -> List.map typ_of_ctype args_list
                    | _ -> failwith "Not implemented"
                  in
                  constr_name, args_list)
               constructor_list
           | _ -> failwith "Not implemented")
        typ_decls
    in
    let decl_list =
      List.map2 (fun (a, b) c -> a, b, c) (List.combine name_list args_list) constr_list
    in
    List.map
      (fun (name, args_list, constr_list) ->
         TypeDecl
           ( name
           , args_list
           , List.map
               (fun (constr_name, args_list) -> Constructor constr_name, args_list)
               constr_list ))
      decl_list
  | Typedtree.Tstr_value (rec_flag, bindings) ->
    let fun_decl =
      List.map
        (fun binding ->
           let fname =
             match binding.Typedtree.vb_pat.pat_desc with
             | Tpat_var (name, _, _) -> Ident.name name
             | Tpat_alias (_, name, _, _) -> Ident.name name
             | _ -> failwith "Not implemented"
           in
           let args = get_args binding.Typedtree.vb_expr.exp_desc in
           let fun_body = get_fun_body binding.Typedtree.vb_expr.exp_desc in
           fname, args, fun_body)
        bindings
    in
    (match rec_flag with
     | Asttypes.Nonrecursive ->
       List.map (fun (fname, args, body) -> NonRec (fname, args, body)) fun_decl
     | Asttypes.Recursive ->
       List.map (fun (fname, args, body) -> Rec (fname, args, body)) fun_decl)
  | _ -> failwith "Not implemented"

and get_args expr_desc =
  match expr_desc with
  | Texp_function (params, _) ->
    List.map (fun param -> Ident.name param.Typedtree.fp_param) params
  | _ -> failwith "Not implemented"

and get_fun_body expr_desc =
  match expr_desc with
  | Typedtree.Texp_function (_, body) ->
    (match body with
     | Tfunction_body expr -> get_expr expr
     | _ -> failwith "Not implemented")
  | _ -> failwith "Not implemented"

and get_expr expr =
  let typ = get_type expr in
  let desc =
    match expr.exp_desc with
    | Typedtree.Texp_match (e1, cases, _, _) ->
      let match_list =
        match e1.exp_desc with
        | Texp_tuple l -> List.map get_expr l
        | _ -> [ get_expr e1 ]
      in
      let cases' =
        List.map
          (fun case ->
             let pattern = get_pattern case.Typedtree.c_lhs in
             Case (pattern, case.Typedtree.c_rhs |> get_expr))
          cases
      in
      Match (match_list, cases')
    | Texp_ident (_, lident, _) ->
      let name = Longident.last lident.txt in
      Var name
    | Texp_construct (lidnet_loc, _, expr_list) ->
      let name = Longident.last lidnet_loc.txt in
      let name =
        match name with
        | "::" -> "Cons"
        | "[]" -> "Nil"
        | _ -> name
      in
      let expr_list' = List.map get_expr expr_list in
      Call (name, expr_list')
    | Texp_apply (func, args) ->
      let fname =
        match (get_expr func).desc with
        | Var name -> name
        | _ -> failwith "Not implemented"
      in
      let fname =
        match fname with
        | "=" ->
          let typ = args |> List.hd |> snd |> Option.get |> get_type in
          (match typ with
           | Talgebraic (typ_name, _) -> typ_name ^ "_eq"
           | Tany -> "any_eq"
           | Tarrow _ -> failwith "function '=' does not support arrow type")
        | _ -> fname
      in
      let args' =
        List.map
          (fun (_, expr) ->
             match expr with
             | Some expr -> get_expr expr
             | None -> failwith "Not implemented")
          args
      in
      Call (fname, args')
    | Texp_ifthenelse (cond, e1, e2_opt) ->
      (match e2_opt with
       | Some e2 ->
         let cond = get_expr cond in
         let e1 = get_expr e1 in
         let e2 = get_expr e2 in
         Match
           ( [ cond ]
           , [ Case (Pat_Constr ("true", []), e1); Case (Pat_Constr ("false", []), e2) ]
           )
       | None -> failwith "Not implemented")
    | Texp_tuple [ a; b ] ->
      let a' = get_expr a in
      let b' = get_expr b in
      Call ("tuple2", [ a'; b' ])
    | Texp_tuple _ -> failwith "more than tuple2 are not implemented"
    | Texp_constant constant ->
      (match constant with
       | Const_int i -> expr_of_int i
       | Const_char char -> expr_of_string (String.make 1 char)
       | Const_string (str, _, _) -> expr_of_string str
       | _ -> failwith "Not implemented")
    | Texp_let (_, bindings, body) ->
      LetIn
        ( List.map
            (fun binding ->
               let var_name =
                 match binding.Typedtree.vb_pat.pat_desc with
                 | Tpat_var (name, _, _) -> Ident.name name
                 | Tpat_alias (_, name, _, _) -> Ident.name name
                 | _ -> failwith "Not implemented"
               in
               let var_body = get_expr binding.Typedtree.vb_expr in
               var_name, var_body)
            bindings
        , get_expr body )
    | _ -> failwith "Not implemented"
  in
  { desc; typ }

and get_pattern : type k. k Typedtree.general_pattern -> pattern =
  fun pattern ->
  match pattern.pat_desc with
  | Tpat_value p -> (p :> Typedtree.pattern) |> get_pattern
  | Tpat_construct (lident_loc, _, args, _) ->
    let name = Longident.last lident_loc.txt in
    let name =
      match name with
      | "::" -> "Cons"
      | "[]" -> "Nil"
      | _ -> name
    in
    let args' = List.map (fun arg -> get_pattern arg) args in
    Pat_Constr (name, args')
  | Tpat_var (name, _, _) -> Pat_Var (Ident.name name)
  | Tpat_tuple patterns -> Pat_Tuple (List.map get_pattern patterns)
  | Tpat_any -> Pat_any
  | _ -> failwith "Not implemented"

and get_type (expr : Typedtree.expression) =
  let rec pr_type type_expr =
    match type_expr with
    | Types.Tvar (Some name) -> name |> parse_typ
    | Tvar None -> Tany
    | Tconstr (path, arg_typ, _) ->
      let name = path |> Path.name in
      Talgebraic (name, List.map (fun arg -> arg |> Types.get_desc |> pr_type) arg_typ)
    | Tarrow (_, e1, e2, _) ->
      (* let arg_num =
        match expr.exp_desc with
        | Texp_apply (_, args) -> List.length args
        | _ -> 0
      in *)
      let e2' = e2 |> Types.get_desc |> pr_type in
      let arg_typ = e1 |> Types.get_desc |> pr_type in
      let new_typ =
        match e2' with
        | Tarrow l -> Tarrow (arg_typ :: l)
        | _ -> Tarrow [ arg_typ; e2' ]
      in
      new_typ
    | Ttuple [ a; b ] ->
      let a' = a |> Types.get_desc |> pr_type in
      let b' = b |> Types.get_desc |> pr_type in
      Talgebraic ("tuple2", [ a'; b' ])
    | Ttuple _ -> failwith "more than tuple2 is not implemented yet"
    | _ -> failwith "Not implemented"
  in
  expr.exp_type |> Types.get_desc |> pr_type
;;

let find_decl name (decls : t) =
  List.find_opt
    (fun decl ->
       match decl with
       | NonRec (fname, _, _) -> fname = name
       | Rec (fname, _, _) -> fname = name
       | TypeDecl (tname, _, _) -> tname = name)
    decls
;;

let get_typ_decl decl =
  match decl with
  | TypeDecl (_, typ_list, typ_decl) -> typ_list, typ_decl
  | _ -> failwith "It is not a type declaration"
;;

let substitute_expr pred convert target expr_from expr_to i is_rewrite result =
  let rec substitute_further pred convert target expr_from expr_to cnt result =
    match target.desc with
    | Match (match_list, cases) ->
      let match_list, cnt, result =
        List.fold_left
          (fun (after_list, cnt, result) match_expr ->
             let new_expr, result, cnt =
               substitute_expr' pred convert match_expr expr_from expr_to cnt result
             in
             after_list @ [ new_expr ], cnt, result)
          ([], cnt, result)
          match_list
      in
      if
        List.for_all
          (fun case ->
             let (Case (pat, _)) = case in
             let pat_vars = collect_var_in_pat pat in
             List.is_empty pat_vars)
          cases
        || not is_rewrite
      then (
        let cases', cnt, result =
          List.fold_left
            (fun (cases, cnt, result) case ->
               let (Case (pattern, expr)) = case in
               let expr', result', cnt =
                 substitute_expr' pred convert expr expr_from expr_to cnt result
               in
               cases @ [ Case (pattern, expr') ], cnt, result')
            ([], cnt, result)
            cases
        in
        { desc = Match (match_list, cases'); typ = target.typ }, result, cnt)
      else { desc = Match (match_list, cases); typ = target.typ }, result, cnt
    | LetIn (bindings, body) ->
      let bindings', cnt, result =
        List.fold_left
          (fun (bindings, cnt, result) (name, body) ->
             let body', result', cnt =
               substitute_expr' pred convert body expr_from expr_to cnt result
             in
             bindings @ [ name, body' ], cnt, result')
          ([], cnt, result)
          bindings
      in
      let body', result, cnt =
        substitute_expr' pred convert body expr_from expr_to cnt result
      in
      { desc = LetIn (bindings', body'); typ = target.typ }, result, cnt
    | Call (name, args) ->
      let name =
        match name with
        | "any_eq" ->
          let typ = (List.hd args).typ in
          (match typ with
           | Talgebraic (name, _) -> name ^ "_eq"
           | _ -> name)
        | _ -> name
      in
      let args', cnt, result =
        List.fold_left
          (fun (args, cnt, result) arg ->
             let arg', result', cnt =
               substitute_expr' pred convert arg expr_from expr_to cnt result
             in
             args @ [ arg' ], cnt, result')
          ([], cnt, result)
          args
      in
      { desc = Call (name, args'); typ = target.typ }, result, cnt
    | Var _ -> target, result, cnt
  and substitute_expr' pred convert target expr_from expr_to cnt result =
    if i < cnt && i <> 0
    then target, result, cnt
    else if pred target expr_from
    then
      if cnt = i || i = 0
      then (
        let expr, result = convert target expr_from expr_to in
        expr, result, cnt + 1)
      else substitute_further pred convert target expr_from expr_to (cnt + 1) result
    else substitute_further pred convert target expr_from expr_to cnt result
  in
  let expr, result, cnt =
    substitute_expr' pred convert target expr_from expr_to 1 result
  in
  expr, result, cnt - 1
;;

let rec is_equal_expr e1 e2 =
  match e1.desc, e2.desc with
  | Var v1, Var v2 -> v1 = v2
  | Match (match_list1, cases1), Match (match_list2, cases2) ->
    List.for_all2 (fun e1 e2 -> is_equal_expr e1 e2) match_list1 match_list2
    && List.for_all2
         (fun (Case (p1, e1)) (Case (p2, e2)) ->
            is_equal_pattern p1 p2 && is_equal_expr e1 e2)
         cases1
         cases2
  | LetIn (bindings1, body1), LetIn (bindings2, body2) ->
    List.for_all2
      (fun (name1, body1) (name2, body2) -> name1 = name2 && is_equal_expr body1 body2)
      bindings1
      bindings2
    && is_equal_expr body1 body2
  | Call (name1, args1), Call (name2, args2) ->
    name1 = name2 && List.for_all2 (fun e1 e2 -> is_equal_expr e1 e2) args1 args2
  | _ -> false

and is_equal_expr_partrial_fun e1 e2 =
  match e1.desc, e2.desc with
  | Var v1, Var v2 -> v1 = v2
  | Match (match_list1, cases1), Match (match_list2, cases2) ->
    List.for_all2 (fun e1 e2 -> is_equal_expr_partrial_fun e1 e2) match_list1 match_list2
    && List.for_all2
         (fun (Case (p1, e1)) (Case (p2, e2)) ->
            is_equal_pattern p1 p2 && is_equal_expr_partrial_fun e1 e2)
         cases1
         cases2
  | LetIn (bindings1, body1), LetIn (bindings2, body2) ->
    List.for_all2
      (fun (name1, body1) (name2, body2) ->
         name1 = name2 && is_equal_expr_partrial_fun body1 body2)
      bindings1
      bindings2
    && is_equal_expr_partrial_fun body1 body2
  | Call (name1, args1), Call (name2, args2) ->
    name1 = name2
    && List.for_all2 (fun e1 e2 -> is_equal_expr_partrial_fun e1 e2) args1 args2
  | Var v1, Call (v2, _) | Call (v1, _), Var v2 -> v1 = v2
  | _ -> false

and is_equal_pattern p1 p2 =
  match p1, p2 with
  | Pat_Constr (name1, args1), Pat_Constr (name2, args2) ->
    name1 = name2 && List.for_all2 (fun p1 p2 -> is_equal_pattern p1 p2) args1 args2
  | Pat_Var v1, Pat_Var v2 -> v1 = v2
  | Pat_Expr e1, Pat_Expr e2 -> is_equal_expr e1 e2
  | Pat_Tuple l1, Pat_Tuple l2 ->
    List.for_all2 (fun p1 p2 -> is_equal_pattern p1 p2) l1 l2
  | Pat_any, Pat_any -> true
  | _ -> false
;;

let rec get_type_in_expr name expr =
  match expr.desc with
  | Var var -> if var = name then Some expr.typ else None
  | Call (fname, args) ->
    if fname = name
    then Some expr.typ
    else (
      let result =
        List.fold_left
          (fun acc arg ->
             match acc with
             | Some _ -> acc
             | None -> get_type_in_expr name arg)
          None
          args
      in
      result)
  | Match (match_list, cases) ->
    let acc =
      List.fold_left
        (fun acc e ->
           match acc with
           | Some _ -> acc
           | None -> get_type_in_expr name e)
        None
        match_list
    in
    List.fold_left
      (fun acc (Case (_, e)) ->
         match acc with
         | Some _ -> acc
         | None -> get_type_in_expr name e)
      acc
      cases
  | LetIn (let_list, e) ->
    let acc =
      List.fold_left
        (fun acc (_, e') ->
           match acc with
           | Some _ -> acc
           | None -> get_type_in_expr name e')
        None
        let_list
    in
    (match acc with
     | Some _ -> acc
     | None -> get_type_in_expr name e)
;;

module StringSet = Set.Make (String)

let get_free_vars expr =
  let rec extract_free_vars (expr : Parsetree.expression) (bound : StringSet.t)
    : StringSet.t
    =
    match expr.pexp_desc with
    | Parsetree.Pexp_ident { txt = Longident.Lident name; _ } ->
      if StringSet.mem name bound then StringSet.empty else StringSet.singleton name
    | Pexp_let (_, bindings, body) ->
      let bound_vars =
        List.fold_left
          (fun acc vb ->
             match vb.Parsetree.pvb_pat.ppat_desc with
             | Ppat_var { txt = var_name; _ } -> StringSet.add var_name acc
             | _ -> acc)
          bound
          bindings
      in
      let fv_body = extract_free_vars body bound_vars in
      let fv_bindings =
        List.fold_left
          (fun acc vb ->
             StringSet.union acc (extract_free_vars vb.Parsetree.pvb_expr bound))
          StringSet.empty
          bindings
      in
      StringSet.union fv_body fv_bindings
    | Pexp_apply (fname, args) ->
      let new_bound = extract_free_vars fname bound in
      List.fold_left
        (fun acc (_, e) -> StringSet.union acc (extract_free_vars e bound))
        new_bound
        args
    | Pexp_tuple exprs | Pexp_array exprs ->
      List.fold_left
        (fun acc e -> StringSet.union acc (extract_free_vars e bound))
        StringSet.empty
        exprs
    | Pexp_ifthenelse (e1, e2, Some e3) ->
      StringSet.union
        (extract_free_vars e1 bound)
        (StringSet.union (extract_free_vars e2 bound) (extract_free_vars e3 bound))
    | Pexp_ifthenelse (e1, e2, None) ->
      StringSet.union (extract_free_vars e1 bound) (extract_free_vars e2 bound)
    | Pexp_construct (_, Some e) -> extract_free_vars e bound
    | _ -> StringSet.empty
  in
  extract_free_vars expr StringSet.empty |> StringSet.elements
;;

let search_return_type name t =
  let decl = find_decl name t in
  match decl with
  | Some (NonRec (_, _, expr)) | Some (Rec (_, _, expr)) -> expr.typ
  | _ -> failwith ("This is not a function :" ^ name)
;;

let search_constr_type name t =
  let typ_decl =
    List.filter
      (fun decl ->
         match decl with
         | TypeDecl _ -> true
         | _ -> false)
      t
  in
  let is_in decl = List.exists (fun (Constructor constr, _) -> constr = name) decl in
  let decl =
    List.find
      (fun decl ->
         match decl with
         | TypeDecl (_, _, decl) -> is_in decl
         | _ -> failwith "not implemented")
      typ_decl
  in
  match decl with
  | TypeDecl (name, typ_list, _) -> Talgebraic (name, typ_list)
  | _ -> failwith "something wrong"
;;

let rec pattern_of_parsetree pat =
  match pat.Parsetree.ppat_desc with
  (* | Tpat_value p -> (p :> Typedtree.pattern) |> get_pattern *)
  | Ppat_construct (lident_loc, arg_opt) ->
    let name = Longident.last lident_loc.txt in
    let name =
      match name with
      | "::" -> "Cons"
      | "[]" -> "Nil"
      | _ -> name
    in
    let args =
      match arg_opt with
      | Some ([], patterns) ->
        (match patterns.Parsetree.ppat_desc with
         | Parsetree.Ppat_tuple args -> args
         | _ -> [ patterns ])
      | _ -> []
    in
    let args' = List.map (fun arg -> pattern_of_parsetree arg) args in
    Pat_Constr (name, args')
  | Ppat_var name -> Pat_Var name.Location.txt
  | Ppat_tuple patterns -> Pat_Tuple (List.map pattern_of_parsetree patterns)
  | Ppat_any -> Pat_any
  | _ -> failwith "Not implemented"
;;

let get_fun_arg_types binding name t =
  let decl = find_decl name t in
  match decl with
  | Some (NonRec (_, args, body)) | Some (Rec (_, args, body)) ->
    let arg_types = List.map (fun arg -> get_type_in_expr arg body |> Option.get) args in
    arg_types
  | _ ->
    (match List.assoc_opt name binding with
     | Some (Tarrow l) -> List.rev l |> List.tl |> List.rev
     | _ -> failwith ("This is not function name: " ^ name))
;;

let rec ir_of_parsetree parse_expr binding t =
  match parse_expr.Parsetree.pexp_desc with
  | Pexp_ident { txt = Longident.Lident name; _ } ->
    { desc = Var name; typ = List.assoc name binding }
  | Pexp_apply (func, args) ->
    (match func.pexp_desc with
     | Pexp_ident { txt = Longident.Lident name; _ } ->
       let typ =
         if List.mem_assoc name binding
         then (
           let arg_num = List.length args in
           let fun_type = List.assoc name binding in
           match fun_type with
           | Tarrow l ->
             let typ_list = nth_tale arg_num l in
             (match typ_list with
              | [ hd ] -> hd
              | _ -> Tarrow typ_list)
           | _ -> fun_type)
         else (
           try search_return_type name t with
           | _ -> failwith ("Function not found: " ^ name))
       in
       let args_types = get_fun_arg_types binding name t in
       let new_bind =
         List.fold_left2
           (fun acc (_, arg) typ ->
              match arg.Parsetree.pexp_desc with
              | Pexp_ident { txt = Longident.Lident arg_name; _ } ->
                (arg_name, typ) :: acc
              | _ -> acc)
           []
           args
           args_types
       in
       { desc =
           Call
             ( name
             , List.map (fun (_, arg) -> ir_of_parsetree arg (new_bind @ binding) t) args
             )
       ; typ
       }
     | _ -> failwith "Not implemented : Pexp_apply")
  | Pexp_construct ({ txt = Longident.Lident name; _ }, Some e) ->
    let name =
      match name with
      | "::" -> "Cons"
      | "[]" -> "Nil"
      | _ -> name
    in
    (match e.Parsetree.pexp_desc with
     | Pexp_tuple l ->
       { desc = Call (name, List.map (fun e -> ir_of_parsetree e binding t) l)
       ; typ = search_constr_type name t
       }
     | _ ->
       { desc = Call (name, [ ir_of_parsetree e binding t ])
       ; typ = search_constr_type name t
       })
  | Pexp_construct ({ txt = Longident.Lident name; _ }, None) ->
    (match name with
     | "[]" -> { desc = Call ("Nil", []); typ = Talgebraic ("list", [ Tany ]) }
     | _ -> { desc = Call (name, []); typ = search_constr_type name t })
  | Pexp_ifthenelse (cond, e1, e2_opt) ->
    let cond = ir_of_parsetree cond binding t in
    let e1 = ir_of_parsetree e1 binding t in
    let e2 =
      match e2_opt with
      | Some e2 -> ir_of_parsetree e2 binding t
      | None -> failwith "Not implemented : Pexp_ifthenelse"
    in
    { desc =
        Match
          ( [ cond ]
          , [ Case (Pat_Constr ("true", []), e1); Case (Pat_Constr ("false", []), e2) ] )
    ; typ = e1.typ
    }
  | Pexp_match (expr, case_list) ->
    let match_list =
      match expr.Parsetree.pexp_desc with
      | Pexp_tuple l -> List.map (fun e -> ir_of_parsetree e binding t) l
      | _ -> [ ir_of_parsetree expr binding t ]
    in
    let cases =
      List.map
        (fun case ->
           let pat = case.Parsetree.pc_lhs in
           let body = case.Parsetree.pc_rhs in
           let pattern = pattern_of_parsetree pat in
           let expr = ir_of_parsetree body binding t in
           Case (pattern, expr))
        case_list
    in
    let typ = List.hd cases |> fun (Case (_, e)) -> e.typ in
    { desc = Match (match_list, cases); typ }
  | Pexp_tuple _ -> failwith "tuple is not implemented"
  | _ -> failwith "Not implemented : Pexp_other"
;;

let rec substitute_typ typ binding =
  match typ with
  | Tany -> List.assoc Tany binding
  | Talgebraic (name, typ_list) ->
    Talgebraic (name, List.map (fun typ -> substitute_typ typ binding) typ_list)
  | _ -> typ
;;

let rec is_typ_contained typ1 typ2 =
  match typ1, typ2 with
  | _, Tany | Tany, _ -> true
  | Talgebraic (name1, lst1), Talgebraic (name2, lst2) ->
    name1 = name2 && List.for_all2 (fun t1 t2 -> is_typ_contained t1 t2) lst1 lst2
  | Tarrow l1, Tarrow l2 -> List.for_all2 (fun t1 t2 -> is_typ_contained t1 t2) l1 l2
  | _ -> false
;;

let absolute_neq e1 e2 =
  match e1.desc, e2.desc with
  | Call ("true", []), Call ("false", []) -> true
  | Call ("false", []), Call ("true", []) -> true
  | _ -> false
;;

let collect_constructor t =
  let typ_decl =
    List.filter
      (fun decl ->
         match decl with
         | TypeDecl _ -> true
         | _ -> false)
      t
  in
  List.fold_left
    (fun acc decl ->
       match decl with
       | TypeDecl (_, _, decl) ->
         List.fold_left (fun acc (Constructor constr, _) -> constr :: acc) acc decl
       | _ -> failwith "not implemented")
    []
    typ_decl
;;

let is_constructor name t =
  let constr_list = collect_constructor t in
  List.exists (fun constr -> constr = name) constr_list
;;

let rename_decl decl =
  match decl with
  | NonRec (name, args, body) ->
    let new_args =
      List.map
        (fun arg ->
           ( "arg_" ^ string_of_int (get_global_cnt ())
           , match get_type_in_expr arg body with
             | Some typ -> typ
             | _ -> failwith "not implemented" ))
        args
    in
    let new_body =
      List.fold_left2
        (fun body arg (new_arg, typ) ->
           let prop, _, _ =
             substitute_expr
               is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               body
               { desc = Var arg; typ }
               { desc = Var new_arg; typ }
               0
               false
               []
           in
           prop)
        body
        args
        new_args
    in
    NonRec (name, new_args |> List.map fst, new_body)
  | Rec (name, args, body) ->
    let new_args =
      List.map
        (fun arg ->
           ( "arg_" ^ string_of_int (get_global_cnt ())
           , match get_type_in_expr arg body with
             | Some typ -> typ
             | _ -> failwith "not implemented" ))
        args
    in
    let new_body =
      List.fold_left2
        (fun body arg (new_arg, typ) ->
           let prop, _, _ =
             substitute_expr
               is_equal_expr
               (fun _ _ expr_to -> expr_to, [])
               body
               { desc = Var arg; typ }
               { desc = Var new_arg; typ }
               0
               false
               []
           in
           prop)
        body
        args
        new_args
    in
    Rec (name, new_args |> List.map fst, new_body)
  | _ -> decl
;;

let rec is_contained expr_src expr_target =
  if is_equal_expr expr_src expr_target
  then true
  else (
    match expr_target.desc with
    | Match (match_list, cases) ->
      List.exists
        (fun e -> is_contained expr_src e)
        (match_list @ List.map (fun (Case (_, e)) -> e) cases)
    | LetIn (bindings, body) ->
      List.exists (fun (_, e) -> is_contained expr_src e) bindings
      || is_contained expr_src body
    | Call (_, args) -> List.exists (fun arg -> is_contained expr_src arg) args
    | _ -> false)
;;
