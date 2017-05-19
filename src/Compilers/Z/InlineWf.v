Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.InlineWf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Inline.

Definition Wf_InlineConstAndOpp {t} (e : Expr base_type op t) (Hwf : Wf e)
  : Wf (InlineConstAndOpp e)
  := @Wf_InlineConst _ _ _ t e Hwf.

Definition Wf_InlineConst {t} (e : Expr base_type op t) (Hwf : Wf e)
  : Wf (InlineConst e)
  := @Wf_InlineConst _ _ _ t e Hwf.

Hint Resolve Wf_InlineConstAndOpp Wf_InlineConst : wf.
