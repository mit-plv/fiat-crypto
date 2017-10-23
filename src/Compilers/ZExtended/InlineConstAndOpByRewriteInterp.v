Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.InlineConstAndOpByRewriteInterp.
Require Import Crypto.Compilers.ZExtended.Syntax.
Require Import Crypto.Compilers.ZExtended.InlineConstAndOpByRewrite.

Module Export Rewrite.
  Lemma InterpInlineConstAndOp {t} (e : Expr t)
  : forall x, Interp (InlineConstAndOp e) x = Interp e x.
  Proof.
    refine (@InterpInlineConstAndOp _ _ _ _ _ t e _).
    clear; abstract (intros []; intros; reflexivity).
  Defined.

  Hint Rewrite @InterpInlineConstAndOp : reflective_interp.
End Rewrite.
