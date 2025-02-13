type env = Proof.env
type state = Proof.state
type lemma_stack = Proof.lemma_stack
type tactic = Proof.tactic

let rank_tactic env lemma_stack state tactic : int =
  ignore (env, lemma_stack, state, tactic);
  failwith "Not implemented"
;;

let is_valid env lemma_stack state tactic : bool =
  ignore (env, lemma_stack, state, tactic);
  failwith "Not implemented"
;;

let mk_candidates env lemma_stack state =
  ignore (env, lemma_stack, state);
  failwith "Not implemented"
;;

let get_decreasing_var env lemma_stack state =
  ignore (env, lemma_stack, state);
  failwith "Not implemented"
;;

let is_stuck env lemma_stack state =
  ignore (env, lemma_stack, state);
  failwith "Not implemented"
;;
