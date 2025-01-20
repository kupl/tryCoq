open Sexplib.Std

type t = decl list [@@deriving sexp]

and decl =
  | NonRec of name * expr
  | Rec of name * expr
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

and case = Case of pattern * expr list [@@deriving sexp]
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
    ignore (rec_flag, bindings);
    [ NonRec ("", Int 0) ]
  | _ -> failwith "Not implemented"
;;
