Require Import Coq.Classes.Morphisms.
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

  Lemma cc_m_Proper_le_r_gen s
    : (0 <= s /\ Proper (Z.le ==> Z.le) (Definitions.Z.cc_m s))
      \/ (s < 0 /\ Proper (Basics.flip Z.le ==> Z.le) (Definitions.Z.cc_m s)).
  Proof.
    cbv [Basics.flip].
    destruct (Z_lt_le_dec s 0); [ right | left ]; (split; [ assumption | ]).
    all: intros x0 x1 H; rewrite !cc_m_eq_full; break_innermost_match; Z.ltb_to_lt; [ nia | ].
    all: Z.div_mod_to_quot_rem; nia.
  Qed.
  Hint Resolve cc_m_Proper_le_r_gen : zarith.

  Lemma cc_m_Proper_le_r s
    : Proper (Z.le ==> Z.le) (Definitions.Z.cc_m s)
      \/ Proper (Basics.flip Z.le ==> Z.le) (Definitions.Z.cc_m s).
  Proof. pose proof (cc_m_Proper_le_r_gen s); tauto. Qed.
  Hint Resolve cc_m_Proper_le_r : zarith.

  Lemma cc_m_Proper_le_r_pos s
    : Proper (Z.le ==> Z.le) (Definitions.Z.cc_m (Z.pos s)).
  Proof. pose proof (cc_m_Proper_le_r_gen (Z.pos s)); intuition lia. Qed.
  Hint Resolve cc_m_Proper_le_r_pos : zarith.

  Lemma cc_m_Proper_le_r_neg s
    : Proper (Basics.flip Z.le ==> Z.le) (Definitions.Z.cc_m (Z.neg s)).
  Proof. pose proof (cc_m_Proper_le_r_gen (Z.neg s)); intuition lia. Qed.
  Hint Resolve cc_m_Proper_le_r_neg : zarith.

  Lemma cc_m_Proper_le_r_0
    : Proper (Z.le ==> Z.le) (Definitions.Z.cc_m 0).
  Proof. pose proof (cc_m_Proper_le_r_gen 0); intuition lia. Qed.
  Hint Resolve cc_m_Proper_le_r_0 : zarith.
End Z.
