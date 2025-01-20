open Sexplib.Std

type t = decl list [@@deriving sexp]

and decl =
  | NonRec of name * name list * expr
  | Rec of name * name list * expr
  | TypeDecl of name * typ_decl
[@@deriving sexp]

and typ_decl = (const * name list) list [@@deriving sexp]
and const = Constructor of name [@@deriving sexp]

and expr =
  | Match of expr * case list
  | LetIn of name * expr * expr
  | IfthenElse of expr * expr * expr
  | Call of t * expr list
  | Int of int
  | String of string
  | Bool of bool
  | List of expr list
  | Var of name
[@@deriving sexp]

and case = Case of pattern * expr [@@deriving sexp]
and pattern = Pattern of name * name list [@@deriving sexp]
and name = string [@@deriving sexp]

let string_of_t t = t |> sexp_of_t |> Sexplib.Sexp.to_string

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
  match expr.exp_desc with
  | _ -> failwith "Not implemented"
;;
