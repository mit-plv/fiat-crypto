Require Export Crypto.Util.FixCoqMistakes.
Ltac clearbody_all :=
  repeat match goal with
         | [ H := _ |- _ ] => clearbody H
         end.
