Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.Z.Syntax.

Ltac invert_one_op e :=
  preinvert_one_type e;
  intros ? e;
  destruct e;
  try exact I.

Ltac invert_op_step :=
  match goal with
  | [ e : op _ (Tbase _) |- _ ] => invert_one_op e
  | [ e : op _ (Prod _ _) |- _ ] => invert_one_op e
  | [ e : op _ Unit |- _ ] => invert_one_op e
  end.

Ltac invert_op := repeat invert_op_step.
