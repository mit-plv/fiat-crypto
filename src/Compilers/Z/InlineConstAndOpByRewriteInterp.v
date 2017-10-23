Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.InlineConstAndOpByRewriteInterp.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.InlineConstAndOpByRewrite.

Module Export Rewrite.
  Definition InterpInlineConstAndOp {t} (e : Expr t)
  : forall x, Interp (InlineConstAndOp e) x = Interp e x
    := @InterpInlineConstAndOp _ _ _ _ _ t e Syntax.Util.make_const_correct.

  Hint Rewrite @InterpInlineConstAndOp : reflective_interp.
End Rewrite.
