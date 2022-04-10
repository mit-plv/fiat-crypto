Require Export Crypto.Util.FixCoqMistakes.

(** [revert_until H] reverts all hypotheses coming after [H] *)
Ltac revert_until H :=
  lazymatch goal with
  | [ H' : _ |- _ ] => tryif constr_eq H' H
                      then idtac
                      else (revert H'; revert_until H)
  end.
