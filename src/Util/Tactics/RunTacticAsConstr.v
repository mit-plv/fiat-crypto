Require Export Crypto.Util.FixCoqMistakes.

(** Runs a tactic during expression evaluation phase, returns the constr [I] *)
Ltac run_tactic tac :=
  let dummy := match goal with _ => tac () end in
  I.

(** Runs a tactic during expression evaluation phase, returning [true] on success and [false] on failure. *)
Ltac is_success_run_tactic tac :=
  match goal with
  | _ => let dummy := run_tactic tac in
         true
  | _ => false
  end.

(** Runs a tactic during expression evaluation phase; on success,
    returns [then_tac ()], otherwise returns [else_tac ()] *)
Ltac constr_tryif_then_else tac then_tac else_tac :=
  let success := is_success_run_tactic tac in
  lazymatch success with
  | true => then_tac ()
  | false => else_tac ()
  end.
