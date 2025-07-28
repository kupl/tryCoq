type prop = Proof.prop
type env = Ir.t
type expr = Ir.expr
type typ = Ir.typ
type model = (string * expr) list

let pp_model (model : model) =
  model
  |> List.map (fun (name, expr) -> Printf.sprintf "%s: %s" name (Ir.pp_expr expr))
  |> String.concat ", "
;;

let rec generator =
  fun (binding : (typ * typ) list) (env : env) (typ : typ) : expr ->
  match typ with
  | Ir.Talgebraic ("string", []) ->
    let _ = Random.self_init () in
    let random_string = String.init 3 (fun _ -> Char.chr (Random.int 26 + 97)) in
    let random_string = Ir.expr_of_string random_string in
    Ir.{ desc = random_string; typ = Ir.Talgebraic ("string", []) }
  | Ir.Talgebraic (typ_name, args) ->
    let decl = Ir.find_decl typ_name env in
    (match decl with
     | Some decl ->
       let decl_args, typ_decl = Ir.get_typ_decl decl in
       let arg_binding = List.combine decl_args args in
       let binding = binding @ arg_binding in
       let is_rec_list = Ir.get_is_rec_list decl in
       let range = List.init (List.length is_rec_list) (fun i -> i) in
       let rec_typ_decl, non_rec_typ_decl =
         List.fold_left
           (fun (rec_list, non_rec_list) i ->
              let is_rec = List.nth is_rec_list i in
              let typ = List.nth typ_decl i in
              if is_rec
              then typ :: rec_list, non_rec_list
              else rec_list, typ :: non_rec_list)
           ([], [])
           range
       in
       let _ = Random.self_init () in
       let i = Random.int 10 in
       let typ =
         match i < 3 with
         | true when rec_typ_decl <> [] ->
           let i = Random.int (List.length rec_typ_decl) in
           List.nth rec_typ_decl i
         | _ ->
           let i = Random.int (List.length non_rec_typ_decl) in
           List.nth non_rec_typ_decl i
       in
       (match typ with
        | Ir.Constructor const_name, constr_arg ->
          let constr_arg = List.map (fun arg -> generator binding env arg) constr_arg in
          Ir.{ desc = Call (const_name, constr_arg); typ = Talgebraic (typ_name, args) })
     | None -> failwith ("type not found : " ^ typ_name))
  | Ir.Tany ->
    (match List.assoc_opt typ binding with
     | Some typ when typ <> Ir.Tany -> generator binding env typ
     | _ ->
       let _ = Random.self_init () in
       let random_int = Random.int 10 in
       let random_int = Ir.expr_of_int random_int in
       Ir.{ desc = random_int; typ = Ir.Talgebraic ("int", []) })
  | _ -> failwith "generator not implemented yet"
;;

let validate_prop prop =
  match prop with
  | Proof.Eq (expr1, expr2) -> Ir.is_equal_expr expr1 expr2
  | _ -> failwith "not implemented yet but equality"
;;

let validate =
  fun (env : env) (prop : prop) : bool ->
  let _ = Printf.printf "Lemma : %s\n" (Proof.pp_prop prop) in
  let _ = flush stdout in
  let vars, prop =
    match prop with
    | Proof.Forall (vars, prop) -> vars, prop
    | _ -> [], prop
  in
  let conds, prop =
    match prop with
    | Proof.Imply (conds, prop) -> conds, prop
    | _ -> [], prop
  in
  let vars_list =
    List.init 3 (fun _ ->
      let vars =
        List.map
          (fun (v, typ) ->
             match typ with
             | Proof.Type t -> v, generator [] env t
             | _ -> failwith "unexpected type in variable")
          vars
      in
      let _ = Printf.printf "Model : %s\n" (pp_model vars) in
      let _ = flush stdout in
      vars)
  in
  let _ = Printf.printf "Substituting variables...\n" in
  let _ = flush stdout in
  let conds_list =
    List.map
      (fun vars ->
         List.map
           (fun prop ->
              let new_cond =
                List.fold_left
                  (fun prop (name, concrete_value) ->
                     let new_prop, _, _ =
                       Proof.substitute_expr_in_prop
                         Ir.is_equal_expr
                         (fun _ _ expr_to -> expr_to, [])
                         prop
                         Ir.{ desc = Var name; typ = concrete_value.typ }
                         concrete_value
                         0
                         false
                     in
                     new_prop)
                  prop
                  vars
              in
              new_cond)
           conds)
      vars_list
  in
  let prop_list =
    List.map
      (fun vars ->
         List.fold_left
           (fun prop (name, concrete_value) ->
              let new_prop, _, _ =
                Proof.substitute_expr_in_prop
                  Ir.is_equal_expr
                  (fun _ _ expr_to -> expr_to, [])
                  prop
                  Ir.{ desc = Var name; typ = concrete_value.typ }
                  concrete_value
                  0
                  false
              in
              new_prop)
           prop
           vars)
      vars_list
  in
  let start = Sys.time () in
  let _ = Printf.printf "Simplifying conditions and property...\n" in
  let _ = flush stdout in
  let conds_list =
    List.map (fun conds -> List.map (Proof.simplify_prop env) conds) conds_list
  in
  let _ = Printf.printf "prop list:\n" in
  let _ = List.iter (fun prop -> Proof.pp_prop prop |> print_endline) prop_list in
  let prop_list = List.map (Proof.simplify_prop env) prop_list in
  let end_time = Sys.time () in
  let _ = Printf.printf "Simplifying took %f seconds\n" (end_time -. start) in
  let _ = flush stdout in
  let result =
    List.for_all2
      (fun conds prop ->
         List.exists (fun cond -> not (validate_prop cond)) conds || validate_prop prop)
      conds_list
      prop_list
  in
  let _ = Printf.printf "Result : %b\n" result in
  result
;;
