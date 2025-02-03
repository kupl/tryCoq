open Sexplib.Std

type t = decl list [@@deriving sexp]

and decl =
  | NonRec of name * name list * expr
  | Rec of name * name list * expr
  | TypeDecl of name * typ_decl
[@@deriving sexp]

and typ_decl = (constr * name list) list [@@deriving sexp]
and constr = Constructor of name [@@deriving sexp]

and expr =
  { desc : expr_desc
  ; typ : typ
  }
[@@deriving sexp]

and expr_desc =
  | Match of expr * case list
  | LetIn of (name * expr) list * expr
  | IfthenElse of expr * expr * expr
  | Call of name * expr list
  | Int of int
  | String of string
  | Bool of bool
  | List of expr list
  | Var of name
  | Tuple of expr list
[@@deriving sexp]

and typ =
  | Tint
  | Tstring
  | Tbool
  | Tlist of typ
  | Ttuple of typ list
  | Talgebraic of name
  | Tany
[@@deriving sexp]

and case = Case of pattern * expr [@@deriving sexp]

and pattern =
  | Pat_Constr of name * pattern list
  | Pat_Var of name
  | Pat_Expr of expr
  | Pat_Tuple of pattern list
  | Pat_any
[@@deriving sexp]

and name = string [@@deriving sexp]

let string_of_t t = t |> sexp_of_t |> Sexplib.Sexp.to_string

let rec pp_t t : string =
  (List.map
     (fun decl ->
        match decl with
        | NonRec (name, args, body) ->
          "let " ^ name ^ " " ^ String.concat " " args ^ " =\n" ^ pp_expr body
        | Rec (name, args, body) ->
          "let rec " ^ name ^ " " ^ String.concat " " args ^ " =\n" ^ pp_expr body
        | TypeDecl (name, typ_decl) -> "type " ^ name ^ " = " ^ pp_typ_decl typ_decl)
     t
   |> String.concat "\n;;\n")
  ^ "\n;;"

and pp_expr expr =
  match expr.desc with
  | Match (e1, cases) ->
    "match " ^ pp_expr e1 ^ " with\n| " ^ String.concat "\n| " (List.map pp_case cases)
  | LetIn (bindings, body) ->
    "let "
    ^ String.concat
        " and "
        (List.map (fun (name, body) -> name ^ " = " ^ pp_expr body) bindings)
    ^ " in "
    ^ pp_expr body
  | IfthenElse (cond, e1, e2) ->
    "if " ^ pp_expr cond ^ " then " ^ pp_expr e1 ^ " else " ^ pp_expr e2
  | Call (name, args) ->
    (match args with
     | [] -> name
     | _ -> name ^ " (" ^ String.concat " " (List.map pp_expr args) ^ ")")
  | Int i -> string_of_int i
  | String s -> "\"" ^ s ^ "\""
  | Bool b -> string_of_bool b
  | List l -> "[" ^ String.concat "; " (List.map pp_expr l) ^ "]"
  | Var name -> name
  | Tuple l -> "(" ^ String.concat ", " (List.map pp_expr l) ^ ")"

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
          | _ -> name ^ " of " ^ String.concat " * " args))
    typ_decl
  |> String.concat " | "

and pp_typ typ =
  match typ with
  | Tint -> "int"
  | Tstring -> "string"
  | Tbool -> "bool"
  | Tlist t -> pp_typ t ^ " list"
  | Ttuple l -> "(" ^ String.concat " * " (List.map pp_typ l) ^ ")"
  | Talgebraic name -> name
  | Tany -> "any"
;;

let typ_of_string s =
  match s with
  | "int" -> Tint
  | "string" -> Tstring
  | "bool" -> Tbool
  | _ -> Talgebraic s
;;

let rec t_of_typedtree typ_tree : t =
  let items = typ_tree.Typedtree.str_items in
  let decls = List.map (fun item -> decl_of_item item) items |> List.flatten in
  decls

and decl_of_item item : decl list =
  match item.Typedtree.str_desc with
  | Typedtree.Tstr_type (_, typ_decls) ->
    let name_list = List.map (fun decl -> decl.Typedtree.typ_name.txt) typ_decls in
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
                    | Cstr_tuple args_list ->
                      List.map
                        (fun args ->
                           match args.Typedtree.ctyp_desc with
                           | Ttyp_constr (_, lident, _) ->
                             let type_name = Longident.last lident.txt in
                             type_name
                           | _ -> failwith "Not implemented")
                        args_list
                    | _ -> failwith "Not implemented"
                  in
                  constr_name, args_list)
               constructor_list
           | _ -> failwith "Not implemented")
        typ_decls
    in
    let tuple_list = List.combine name_list constr_list in
    List.map
      (fun (name, constr_list) ->
         TypeDecl
           ( name
           , List.map
               (fun (constr_name, args_list) -> Constructor constr_name, args_list)
               constr_list ))
      tuple_list
  | Typedtree.Tstr_value (rec_flag, bindings) ->
    ignore rec_flag;
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
      let e1' = get_expr e1 in
      let cases' =
        List.map
          (fun case ->
             let pattern = get_pattern case.Typedtree.c_lhs in
             Case (pattern, case.Typedtree.c_rhs |> get_expr))
          cases
      in
      Match (e1', cases')
    | Texp_ident (_, lident, _) -> Var (Longident.last lident.txt)
    | Texp_construct (lidnet_loc, _, expr_list) ->
      let name = Longident.last lidnet_loc.txt in
      let expr_list' = List.map get_expr expr_list in
      Call (name, expr_list')
    | Texp_apply (func, args) ->
      let fname =
        match (get_expr func).desc with
        | Var name -> name
        | _ -> failwith "Not implemented"
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
       | Some e2 -> IfthenElse (get_expr cond, get_expr e1, get_expr e2)
       | None -> failwith "Not implemented")
    | Texp_tuple expr_list -> Tuple (List.map get_expr expr_list)
    | Texp_constant constant ->
      (match constant with
       | Const_int i -> Int i
       | Const_char char -> String (String.make 1 char)
       | Const_string (str, _, _) -> String str
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
    let args' = List.map (fun arg -> get_pattern arg) args in
    Pat_Constr (name, args')
  | Tpat_var (name, _, _) -> Pat_Var (Ident.name name)
  | Tpat_tuple patterns -> Pat_Tuple (List.map get_pattern patterns)
  | Tpat_any -> Pat_any
  | _ -> failwith "Not implemented"

and get_type (expr : Typedtree.expression) =
  let rec pr_type type_expr =
    match type_expr with
    | Types.Tvar (Some name) -> name
    | Tconstr (path, _, _) -> path |> Path.name
    | Tarrow (_, _, e2, _) -> e2 |> Types.get_desc |> pr_type
    | Tpoly (_, _) -> failwith "polymorphic type"
    | _ -> failwith "Not implemented"
  in
  let typ = expr.exp_type |> Types.get_desc |> pr_type in
  typ_of_string typ
;;

let find_decl name (decls : t) =
  List.find
    (fun decl ->
       match decl with
       | NonRec (fname, _, _) -> fname = name
       | Rec (fname, _, _) -> fname = name
       | TypeDecl (tname, _) -> tname = name)
    decls
;;

let get_typ_decl decl =
  match decl with
  | TypeDecl (_, typ_decl) -> typ_decl
  | _ -> failwith "It is not a type declaration"
;;

let substitute_expr pred convert target expr_from expr_to i result =
  let rec substitute_expr' pred convert target expr_from expr_to cnt result =
    if i < cnt && i <> 0
    then target, result, cnt
    else if pred target expr_from
    then
      if cnt = i || i = 0
      then (
        let expr, result = convert target expr_from expr_to in
        expr, result, cnt + 1)
      else expr_from, result, cnt + 1
    else (
      match target.desc with
      | Match (e1, cases) ->
        let e1', result, cnt =
          substitute_expr' pred convert e1 expr_from expr_to cnt result
        in
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
        { desc = Match (e1', cases'); typ = target.typ }, result, cnt
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
      | IfthenElse (cond, e1, e2) ->
        let cond', result, cnt =
          substitute_expr' pred convert cond expr_from expr_to cnt result
        in
        let e1', result, cnt =
          substitute_expr' pred convert e1 expr_from expr_to cnt result
        in
        let e2', result, cnt =
          substitute_expr' pred convert e2 expr_from expr_to cnt result
        in
        { desc = IfthenElse (cond', e1', e2'); typ = target.typ }, result, cnt
      | Call (name, args) ->
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
      | Int _ | String _ | Bool _ -> target, result, cnt
      | List l ->
        let l', cnt, result =
          List.fold_left
            (fun (l, cnt, result) expr ->
               let expr', result, cnt =
                 substitute_expr' pred convert expr expr_from expr_to cnt result
               in
               l @ [ expr' ], cnt, result)
            ([], cnt, result)
            l
        in
        { desc = List l'; typ = target.typ }, result, cnt
      | Var _ -> target, result, cnt
      | Tuple l ->
        let l', cnt, result =
          List.fold_left
            (fun (l, cnt, result) expr ->
               let expr', result, cnt =
                 substitute_expr' pred convert expr expr_from expr_to cnt result
               in
               l @ [ expr' ], cnt, result)
            ([], cnt, result)
            l
        in
        { desc = Tuple l'; typ = target.typ }, result, cnt)
  in
  let expr, result, cnt =
    substitute_expr' pred convert target expr_from expr_to 1 result
  in
  expr, result, cnt
;;

let rec is_equal_expr e1 e2 =
  match e1.desc, e2.desc with
  | Int i1, Int i2 -> i1 = i2
  | String s1, String s2 -> s1 = s2
  | Bool b1, Bool b2 -> b1 = b2
  | List l1, List l2 -> List.for_all2 (fun e1 e2 -> is_equal_expr e1 e2) l1 l2
  | Var v1, Var v2 -> v1 = v2
  | Tuple l1, Tuple l2 -> List.for_all2 (fun e1 e2 -> is_equal_expr e1 e2) l1 l2
  | Match (e1, cases1), Match (e2, cases2) ->
    is_equal_expr e1 e2
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
  | IfthenElse (cond1, e11, e12), IfthenElse (cond2, e21, e22) ->
    is_equal_expr cond1 cond2 && is_equal_expr e11 e21 && is_equal_expr e12 e22
  | Call (name1, args1), Call (name2, args2) ->
    name1 = name2 && List.for_all2 (fun e1 e2 -> is_equal_expr e1 e2) args1 args2
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
  | Call (_, args) ->
    List.fold_left
      (fun acc arg ->
         match acc with
         | Some _ -> acc
         | None -> get_type_in_expr name arg)
      None
      args
  | Match (e, cases) ->
    let acc = get_type_in_expr name e in
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
  | IfthenElse (e1, e2, e3) ->
    let acc = get_type_in_expr name e1 in
    (match acc with
     | Some _ -> acc
     | None ->
       let acc = get_type_in_expr name e2 in
       (match acc with
        | Some _ -> acc
        | None -> get_type_in_expr name e3))
  | List lst ->
    List.fold_left
      (fun acc e ->
         match acc with
         | Some _ -> acc
         | None -> get_type_in_expr name e)
      None
      lst
  | Tuple lst ->
    List.fold_left
      (fun acc e ->
         match acc with
         | Some _ -> acc
         | None -> get_type_in_expr name e)
      None
      lst
  | Int _ -> Some (typ_of_string "int")
  | Bool _ -> Some (typ_of_string "bool")
  | String _ -> Some (typ_of_string "string")
;;
