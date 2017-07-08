Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  Lemma zselect_correct cond zero_case nonzero_case :
    Z.zselect cond zero_case nonzero_case =
    if dec (cond = 0) then zero_case else nonzero_case.
  Proof.
    cbv [Z.zselect]; break_match;
      try reflexivity; try discriminate.
    rewrite <-Z.eqb_neq in *; congruence.
  Qed.
End Z.
