Require Import Crypto.Util.Tactics.ChangeInAll.

(** fully reduces the first argument to [t], wherever it appears *)
Ltac unfold_first_arg t :=
  repeat match goal with
         | [ H : context[t ?x] |- _ ] => progress change_with_compute_in_all x
         | [ |- context[t ?x] ] => progress change_with_compute_in_all x
         end.

(** fully reduces the second argument to [t], wherever it appears *)
Ltac unfold_second_arg t :=
  repeat match goal with
         | [ H : context[t _ ?x] |- _ ] => progress change_with_compute_in_all x
         | [ |- context[t _ ?x] ] => progress change_with_compute_in_all x
         end.
