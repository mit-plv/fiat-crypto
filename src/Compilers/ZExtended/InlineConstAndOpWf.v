Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.InlineConstAndOpWf.
Require Import Crypto.Compilers.ZExtended.Syntax.
Require Import Crypto.Compilers.ZExtended.InlineConstAndOp.

Definition Wf_InlineConstAndOp {t} (e : Expr t) (Hwf : Wf e)
  : Wf (InlineConstAndOp e)
  := @Wf_InlineConstAndOp _ _ _ _ _ t e Hwf.

Hint Resolve Wf_InlineConstAndOp : wf.
