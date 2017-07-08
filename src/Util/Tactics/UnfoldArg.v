Require Import Crypto.Util.Tactics.ChangeInAll.

(** fully reduces the first argument to [t], wherever it appears *)
Ltac unfold_first_arg t :=
  repeat match goal with
         | [ H : context[t ?x] |- _ ] => progress change_with_compute_in_all x
         | [ |- context[t ?x] ] => progress change_with_compute_in_all x
         end.

(* use uconstr so we can have underscores *)
Tactic Notation "unfold_first_arg" uconstr(t) := unfold_first_arg t.
