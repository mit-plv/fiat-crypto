Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.InlineWf.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Inline.

Definition Wf_InlineConst {t} (e : Expr base_type op t) (Hwf : Wf e)
  : Wf (InlineConst e)
  := @Wf_InlineConst _ _ _ t e Hwf.

Hint Resolve Wf_InlineConst : wf.
