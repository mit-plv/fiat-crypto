Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.Z.TypeInversion.
Require Import Crypto.Compilers.Z.Syntax.

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

Ltac invert_match_op_step :=
  match goal with
  | [ |- context[match ?e with OpConst _ _ => _ | _ => _ end] ]
    => invert_one_op e
  | [ H : context[match ?e with OpConst _ _ => _ | _ => _ end] |- _ ]
    => invert_one_op e
  end.

Ltac invert_match_op := repeat invert_match_op_step.
