Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.

Module Export Named.
  Ltac invert_one_expr e :=
    preinvert_one_type e;
    intros ? e;
    destruct e;
    try exact I.

  Ltac invert_expr_step :=
    match goal with
    | [ e : Named.exprf _ _ _ (Tbase _) |- _ ] => invert_one_expr e
    | [ e : Named.exprf _ _ _ (Prod _ _) |- _ ] => invert_one_expr e
    | [ e : Named.exprf _ _ _ Unit |- _ ] => invert_one_expr e
    | [ e : Named.expr _ _ _ (Arrow _ _) |- _ ] => invert_one_expr e
    end.

  Ltac invert_expr := repeat invert_expr_step.
End Named.
