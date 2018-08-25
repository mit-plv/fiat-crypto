Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Simple.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Local Open Scope Z_scope.

Module Z.
  Hint Rewrite Z.log2_pow2 Z.pow_1_r using solve [auto using Z.log2_nonneg with zarith] : push_Zpow.

  Lemma cc_m_eq_full : forall s x, Z.cc_m s x = if (s =? 1) then x * 2 else x / (s / 2).
  Proof.
    intros; cbv [Z.cc_m].
    destruct (Decidable.dec (2 < s)).
    { assert (1 <= Z.log2 s) by (rewrite <-Z.log2_2; auto using Z.log2_le_mono with lia).
      break_match; Z.ltb_to_lt; try lia; [].
      match goal with H : _ = s |- _ => rewrite <-H end.
      autorewrite with Zshift_to_pow push_Zpow.
      reflexivity. }
    { assert (s < 0 \/ s = 0 \/ s = 1 \/ s = 2) by lia.
      destruct_head'_or; (subst s || destruct s); try reflexivity; try (cbn; autorewrite with zsimplify_const; lia).
      change (Z.log2 1 - 1) with (-1).
      rewrite (Z.shiftr_opp_r _ 1), Z.shiftl_mul_pow2 by lia.
      reflexivity. }
  Qed.

  Lemma cc_m_eq : forall s x, 2 < s -> Z.cc_m s x = x / (s / 2).
  Proof. intros; rewrite cc_m_eq_full; break_match; Z.ltb_to_lt; lia. Qed.

  Lemma cc_m_small : forall s x, s mod 2 = 0 -> 0 <= x < s -> 0 <= Z.cc_m s x < 2.
  Proof.
    intros. rewrite cc_m_eq_full.
    repeat match goal with
           | _ => break_innermost_match_step
           | _ => progress Z.ltb_to_lt
           | _ => split
           | _ => apply Z.div_lt_upper_bound
           | _ => solve [Z.zero_bounds]
           end.
    Z.div_mod_to_quot_rem_in_goal; lia.
  Qed.
End Z.
