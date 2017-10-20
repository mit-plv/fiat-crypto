Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.InlineConstAndOpInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.InlineConstAndOp.

Definition InterpInlineConstAndOp {t} (e : Expr t) (Hwf : Wf e)
  : forall x, Interp (InlineConstAndOp e) x = Interp e x
  := @InterpInlineConstAndOp _ _ _ _ _ t e Hwf Syntax.Util.make_const_correct.

Hint Rewrite @InterpInlineConstAndOp using solve_wf_side_condition : reflective_interp.
