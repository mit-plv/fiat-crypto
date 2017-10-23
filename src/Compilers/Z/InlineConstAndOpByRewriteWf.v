Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.InlineConstAndOpByRewriteWf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.InlineConstAndOpByRewrite.

Module Export Rewrite.
  Definition Wf_InlineConstAndOp {t} (e : Expr t) (Hwf : Wf e)
  : Wf (InlineConstAndOp e)
    := @Wf_InlineConstAndOp _ _ _ _ _ t e Hwf.

  Hint Resolve Wf_InlineConstAndOp : wf.
End Rewrite.
