(** A tactic that executes immediately (during expression evaluation / constr-construction) and fails.  Ideally we can eventually give it a nicer error message.  COQBUG(3913) *)

Ltac constr_fail :=
  let __ := match goal with _ => fail 1 "Constr construction failed.  Please look at the message log (*coq*, or run your tactic again inside Fail or try) to see more details" end in
  ().

Ltac constr_fail_with msg_tac :=
  let __ := match goal with _ => msg_tac () end in
  constr_fail.
