Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Local Open Scope Z_scope.

Module Z.
  Hint Rewrite Z.log2_pow2 Z.pow_1_r using solve [auto using Z.log2_nonneg with zarith] : push_Zpow.

  Lemma cc_m_eq : forall s x, 2 < s -> Z.cc_m s x = x / (s / 2).
  Proof.
    intros; cbv [Z.cc_m].
    assert (1 <= Z.log2 s) by (rewrite <-Z.log2_2; auto using Z.log2_le_mono with lia).
    break_match; [ | reflexivity ].
    match goal with H : _ = s |- _ => rewrite <-H end.
    autorewrite with Zshift_to_pow push_Zpow.
    reflexivity.
  Qed.

  Lemma cc_m_small : forall s x, 2 < s -> s mod 2 = 0 -> 0 <= x < s -> 0 <= Z.cc_m s x < 2.
  Proof.
    intros. rewrite cc_m_eq by auto.
    repeat match goal with
           | _ => split
           | _ => apply Z.div_lt_upper_bound
           | _ => solve [Z.zero_bounds]
           end.
    Z.div_mod_to_quot_rem_in_goal; lia.
  Qed.
End Z.