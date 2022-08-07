Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.InlineInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Inline.

Definition InterpInlineConstAndOpp {interp_base_type interp_op} {t} (e : Expr t) (Hwf : Wf e)
  : forall x, Compilers.Syntax.Interp interp_op (InlineConstAndOpp e) x = Compilers.Syntax.Interp interp_op e x
  := @InterpInlineConst _ interp_base_type _ _ _ t e Hwf.

Definition InterpInlineConst {interp_base_type interp_op} {t} (e : Expr t) (Hwf : Wf e)
  : forall x, Compilers.Syntax.Interp interp_op (InlineConst e) x = Compilers.Syntax.Interp interp_op e x
  := @InterpInlineConst _ interp_base_type _ _ _ t e Hwf.

#[global]
Hint Rewrite @InterpInlineConstAndOpp @InterpInlineConst using solve_wf_side_condition : reflective_interp.
