Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Inline.

Definition InterpInlineConst {interp_base_type interp_op} {t} (e : Expr base_type op t) (Hwf : Wf e)
  : forall x, Interp interp_op (InlineConst e) x = Interp interp_op e x
  := @InterpInlineConst _ interp_base_type _ _ _ t e Hwf.

Hint Rewrite @InterpInlineConst using solve [ eassumption | eauto with wf ] : reflective_interp.
