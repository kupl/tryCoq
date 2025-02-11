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

and name = string [@@deriving sexp]

let initial_env =
  [ Rec
      ( "@"
      , [ "l1"; "l2" ]
      , { desc =
            Match
              ( { desc = Var "l1"; typ = Tlist Tany }
              , [ Case (Pat_Constr ("[]", []), { desc = Var "l2"; typ = Tlist Tany })
                ; Case
                    ( Pat_Constr ("::", [ Pat_Tuple [ Pat_Var "hd"; Pat_Var "tl" ] ])
                    , { desc =
                          Call
                            ( "::"
                            , [ { desc =
                                    Tuple
                                      [ { desc = Var "hd"; typ = Tany }
                                      ; { desc =
                                            Call
                                              ( "@"
                                              , [ { desc = Var "tl"; typ = Tlist Tany }
                                                ; { desc = Var "l2"; typ = Tlist Tany }
                                                ] )
                                        ; typ = Tlist Tany
                                        }
                                      ]
                                ; typ = Ttuple [ Tany; Tlist Tany ]
                                }
                              ] )
                      ; typ = Tlist Tany
                      } )
                ] )
        ; typ = Tlist Tany
        } )
  ; NonRec
      ( "not"
      , [ "b" ]
      , { desc =
            IfthenElse
              ( { desc = Var "b"; typ = Tbool }
              , { desc = Bool false; typ = Tbool }
              , { desc = Bool true; typ = Tbool } )
        ; typ = Tbool
        } )
  ]
;;

let rec nth_tale n lst =
  if n = 0
  then lst
  else (
    match lst with
    | [] -> failwith "n is too big"
    | _ :: tl -> nth_tale (n - 1) tl)
;;

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
    (match name with
     | "::" ->
       let args = List.hd args in
       (match args.desc with
        | Tuple l ->
          "(" ^ pp_expr (List.hd l) ^ " :: " ^ pp_expr (List.hd (List.tl l)) ^ ")"
        | _ -> failwith "This is not list")
     | "@" ->
       "("
       ^ pp_expr (List.hd args)
       ^ " "
       ^ name
       ^ " "
       ^ pp_expr (List.hd (List.tl args))
       ^ ")"
     | _ ->
       (match args with
        | [] -> name
        | _ ->
          name
          ^ " "
          ^ String.concat " " (List.map (fun arg -> "(" ^ pp_expr arg ^ ")") args)))
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
  | Tarrow l -> String.concat " -> " (List.map pp_typ l)
;;

let rec parse_typ (s : string) : typ =
  let s = String.trim s in
  match s with
  | "int" -> Tint
  | "string" -> Tstring
  | "bool" -> Tbool
  | _ ->
    if Str.string_match (Str.regexp "\\(.*\\) list$") s 0
    then Tlist (parse_typ (String.trim (Str.matched_group 1 s)))
    else if String.contains s '*'
    then (
      let parts = List.map String.trim (Str.split (Str.regexp " *\\* *") s) in
      Ttuple (List.map parse_typ parts))
    else if String.contains s '-' && String.contains s '>'
    then (
      let parts = List.map String.trim (Str.split (Str.regexp " *-> *") s) in
      Tarrow (List.map parse_typ parts))
    else if Str.string_match (Str.regexp "[a-zA-Z_][a-zA-Z0-9_]*") s 0
    then Talgebraic s
    else Tany
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
    | Texp_ident (_, lident, _) ->
      let name = Longident.last lident.txt in
      Var name
    | Texp_construct (lidnet_loc, _, expr_list) ->
      let name = Longident.last lidnet_loc.txt in
      let expr_list' = List.map get_expr expr_list in
      if name = "::"
      then
        Call
          ( name
          , [ { desc = Tuple expr_list'
              ; typ = Ttuple (List.map (fun e -> e.typ) expr_list')
              }
            ] )
      else Call (name, expr_list')
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
    if name = "::"
    then Pat_Constr (name, [ Pat_Tuple args' ])
    else Pat_Constr (name, args')
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
      (match name with
       | "list" -> Tlist (List.hd arg_typ |> Types.get_desc |> pr_type)
       | _ -> parse_typ name)
    | Tarrow (_, e1, e2, _) ->
      let arg_num =
        match expr.exp_desc with
        | Texp_apply (_, args) -> List.length args
        | _ -> 0
      in
      let e2' = e2 |> Types.get_desc |> pr_type in
      let arg_typ = e1 |> Types.get_desc |> pr_type in
      (match arg_typ with
       | Tarrow l ->
         let l = nth_tale arg_num l in
         (match l with
          | [] -> e2'
          | _ -> Tarrow (l @ [ e2' ]))
       | _ ->
         (match arg_num with
          | 1 -> e2'
          | 0 -> Tarrow [ arg_typ; e2' ]
          | _ -> failwith "argument number not mathcing"))
    | Ttuple l -> Ttuple (List.map (fun e -> e |> Types.get_desc |> pr_type) l)
    | _ -> failwith "Not implemented"
  in
  expr.exp_type |> Types.get_desc |> pr_type
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
      else target, result, cnt + 1
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
  | Int _ -> Some Tint
  | Bool _ -> Some Tbool
  | String _ -> Some Tstring
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
  | NonRec (_, _, expr) | Rec (_, _, expr) -> expr.typ
  | _ -> failwith "This is not a function"
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
         | TypeDecl (_, decl) -> is_in decl
         | _ -> failwith "not implemented")
      typ_decl
  in
  match decl with
  | TypeDecl (name, _) -> parse_typ name
  | _ -> failwith "something wrong"
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
           | _ -> failwith "this is not function")
         else search_return_type name t
       in
       { desc = Call (name, List.map (fun (_, arg) -> ir_of_parsetree arg binding t) args)
       ; typ
       }
     | _ -> failwith "Not implemented")
  | Pexp_construct ({ txt = Longident.Lident name; _ }, Some e) ->
    (match name with
     | "::" -> { desc = Call ("::", [ ir_of_parsetree e binding t ]); typ = Tlist Tany }
     | _ ->
       { desc = Call (name, [ ir_of_parsetree e binding t ])
       ; typ = search_constr_type name t
       })
  | Pexp_construct ({ txt = Longident.Lident name; _ }, None) ->
    (match name with
     | "[]" -> { desc = Call ("[]", []); typ = Tlist Tany }
     | _ -> { desc = Call (name, []); typ = search_constr_type name t })
  | Pexp_ifthenelse (cond, e1, e2_opt) ->
    let cond = ir_of_parsetree cond binding t in
    let e1 = ir_of_parsetree e1 binding t in
    let e2 =
      match e2_opt with
      | Some e2 -> ir_of_parsetree e2 binding t
      | None -> failwith "Not implemented"
    in
    { desc = IfthenElse (cond, e1, e2); typ = e1.typ }
  | Pexp_tuple l ->
    let component = List.map (fun e -> ir_of_parsetree e binding t) l in
    { desc = Tuple component; typ = Ttuple (List.map (fun e -> e.typ) component) }
  | _ -> failwith "Not implemented"
;;

let rec is_typ_contained typ1 typ2 =
  match typ1, typ2 with
  | Tint, Tint | Tstring, Tstring | Tbool, Tbool | _, Tany | Tany, _ -> true
  | Tlist t1, Tlist t2 -> is_typ_contained t1 t2
  | Ttuple l1, Ttuple l2 -> List.for_all2 (fun t1 t2 -> is_typ_contained t1 t2) l1 l2
  | Talgebraic name1, Talgebraic name2 -> name1 = name2
  | Tarrow l1, Tarrow l2 -> List.for_all2 (fun t1 t2 -> is_typ_contained t1 t2) l1 l2
  | _ -> false
;;
