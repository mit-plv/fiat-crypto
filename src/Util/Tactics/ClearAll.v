Ltac clear_all :=
  repeat match goal with
         | [ H : _ |- _ ] => clear H
         end.
