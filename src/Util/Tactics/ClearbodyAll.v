Require Export Crypto.Util.GlobalSettings.
Ltac clearbody_all :=
  repeat match goal with
         | [ H := _ |- _ ] => clearbody H
         end.
