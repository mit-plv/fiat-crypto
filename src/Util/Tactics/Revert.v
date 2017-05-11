(** Like [Coq.Program.Tactics.revert_last], but only for non-dependent hypotheses *)
Ltac revert_last_nondep :=
  match goal with
  | [ H : _ |- _ ]
    => lazymatch goal with
       | [ H' : context[H] |- _ ] => fail
       | [ |- context[H] ] => fail
       | _ => idtac
       end;
       revert H
  end.

Ltac reverse_nondep := repeat revert_last_nondep.
