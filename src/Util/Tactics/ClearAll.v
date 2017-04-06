Ltac clear_all :=
  clear;
  repeat match goal with
         | [ H : _ |- _ ] => clear H
         end.
