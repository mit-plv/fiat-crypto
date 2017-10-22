Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.InlineConstAndOpInterp.
Require Import Crypto.Compilers.ZExtended.Syntax.
Require Import Crypto.Compilers.ZExtended.InlineConstAndOp.

Definition InterpInlineConstAndOp {t} (e : Expr t) (Hwf : Wf e)
  : forall x, Interp (InlineConstAndOp e) x = Interp e x.
Proof.
  refine (@InterpInlineConstAndOp _ _ _ _ _ t e Hwf _).
  clear; abstract (intros []; intros; reflexivity).
Defined.

Hint Rewrite @InterpInlineConstAndOp using solve_wf_side_condition : reflective_interp.
