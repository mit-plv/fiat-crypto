Require Import Crypto.Util.Tactics.Test.
Require Import Crypto.Util.Tactics.Not.
Require Export Crypto.Util.FixCoqMistakes.

(** Do something with every hypothesis. *)
Ltac do_with_hyp' tac :=
  match goal with
    | [ H : _ |- _ ] => tac H
  end.

(** Do something with any hypothesis, as long as there is only one hypothesis that it works with *)
Ltac do_with_exactly_one_hyp tac :=
  match goal with
  | [ H : _ |- _ ]
    => test (tac H);
      not (idtac; match goal with
                  | [ H' : _ |- _ ] => tryif constr_eq H H' then fail else tac H'
                  end);
      tac H
  end.
