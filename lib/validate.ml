type prop = Proof.prop
type env = Ir.t
type expr = Ir.expr
type typ = Ir.typ

let rec generator =
  fun (env : env) (typ : typ) : expr ->
  match typ with
  | Ir.Talgebraic (name, args) ->
    let decl = Ir.find_decl name env in
    (match decl with
     | Some decl ->
       let _, typ_decl = Ir.get_typ_decl decl in
       let length = List.length typ_decl in
       let _ = Random.self_init () in
       let i = Random.int length in
       let typ = List.nth typ_decl i in
       (* have to assign high probability to terminal constructors *)
       (match typ with
        | Ir.Constructor name, constr_arg ->
          let constr_arg = List.map (fun arg -> generator env arg) constr_arg in
          Ir.{ desc = Call (name, constr_arg); typ = Talgebraic (name, args) })
     | None -> failwith "type not found")
  | Ir.Tany ->
    let _ = Random.self_init () in
    let random_int = Random.int 100 in
    let random_int = Ir.expr_of_int random_int in
    Ir.{ desc = random_int; typ = Ir.Talgebraic ("int", []) }
  | _ -> failwith "generator not implemented yet"
;;

let validate_prop prop =
  match prop with
  | Proof.Eq (expr1, expr2) -> Ir.is_equal_expr expr1 expr2
  | _ -> failwith "not implemented yet but equality"
;;

let validate =
  fun (env : env) (prop : prop) : bool ->
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
  let vars =
    List.map
      (fun (v, typ) ->
         match typ with
         | Proof.Type t -> v, generator env t
         | _ -> failwith "unexpected type in variable")
      vars
  in
  let _ = print_endline "vars" in
  let _ =
    List.iter (fun (name, expr) -> Printf.printf "%s: %s\n" name (Ir.pp_expr expr)) vars
  in
  let conds =
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
      conds
  in
  let prop =
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
  let conds = List.map (Proof.simplify_prop env) conds in
  let prop = Proof.simplify_prop env prop in
  List.exists (fun cond -> not (validate_prop cond)) conds || validate_prop prop
;;
