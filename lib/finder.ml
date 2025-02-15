type t = Proof.t
type env = Proof.env
type state = Proof.state
type lemma_stack = Proof.lemma_stack
type lemma = Proof.goal

let is_duplicated (env : env) (t : t) (lemma : lemma) : bool =
  ignore (env, t, lemma);
  failwith "TODO"
;;

let naive_generalize (env : env) (t : t) (goal : Proof.goal) : lemma =
  ignore (env, t, goal);
  failwith "TODO"
;;

let make_lemmas (env : env) (t : t list) : (t * lemma) list =
  ignore (env, t);
  failwith "TODO"
;;
