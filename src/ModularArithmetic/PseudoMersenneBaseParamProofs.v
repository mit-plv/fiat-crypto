Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import VerdiTactics.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.Pow2Base Crypto.ModularArithmetic.Pow2BaseProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section PseudoMersenneBaseParamProofs.
  Context `{prm : PseudoMersenneBaseParams}.

  Lemma limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w.
  Proof.
    intros.
    apply Z.lt_le_incl.
    auto using limb_widths_pos.
  Qed. Hint Resolve limb_widths_nonneg.

  Lemma k_nonneg : 0 <= k.
  Proof.
    apply sum_firstn_limb_widths_nonneg; auto.
  Qed. Hint Resolve k_nonneg.

  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma base_length : length base = length limb_widths.
  Proof.
    auto using base_from_limb_widths_length.
  Qed.

  Lemma base_matches_modulus: forall i j,
    (i   <  length base)%nat ->
    (j   <  length base)%nat ->
    (i+j >= length base)%nat->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat).
  Proof.
    intros.
    rewrite (Z.mul_comm r).
    subst r.
    assert (i + j - length base < length base)%nat by omega.
    rewrite Z.mul_div_eq by (apply Z.gt_lt_iff; apply Z.mul_pos_pos;
      [ | subst b; rewrite nth_default_base; try assumption ];
      zero_bounds; auto using sum_firstn_limb_widths_nonneg, limb_widths_nonneg).
    rewrite (Zminus_0_l_reverse (b i * b j)) at 1.
    f_equal.
    subst b.
    repeat rewrite nth_default_base by auto.
    do 2 rewrite <- Z.pow_add_r by auto using sum_firstn_limb_widths_nonneg.
    symmetry.
    apply Z.mod_same_pow.
    split.
    + apply Z.add_nonneg_nonneg; auto using sum_firstn_limb_widths_nonneg.
    + rewrite base_length in * by auto.
      apply limb_widths_match_modulus; auto.
  Qed.

   Lemma base_positive : forall b : Z, In b base -> b > 0.
   Proof.
     intros b In_b_base.
     apply In_nth_error_value in In_b_base.
     destruct In_b_base as [i nth_err_b].
     apply nth_error_subst in nth_err_b; [ | auto ].
     rewrite nth_err_b.
     apply Z.gt_lt_iff.
     apply Z.pow_pos_nonneg; omega || auto using sum_firstn_limb_widths_nonneg.
   Qed.

   Lemma b0_1 : forall x : Z, nth_default x base 0 = 1.
   Proof.
     case_eq limb_widths; intros; [pose proof limb_widths_nonnil; congruence | reflexivity].
   Qed.

   Lemma base_good : forall i j : nat,
                (i + j < length base)%nat ->
                let b := nth_default 0 base in
                let r := b i * b j / b (i + j)%nat in
                b i * b j = r * b (i + j)%nat.
   Proof.
     intros; subst b r.
     repeat rewrite nth_default_base by (omega || auto).
     rewrite (Z.mul_comm _ (2 ^ (sum_firstn limb_widths (i+j)))).
     rewrite Z.mul_div_eq by (apply Z.gt_lt_iff; zero_bounds;
       auto using sum_firstn_limb_widths_nonneg).
     rewrite <- Z.pow_add_r by auto using sum_firstn_limb_widths_nonneg.
     rewrite Z.mod_same_pow; try ring.
     split; [ auto using sum_firstn_limb_widths_nonneg | ].
     apply limb_widths_good.
     rewrite <- base_length; assumption.
   Qed.

  Global Instance bv : BaseSystem.BaseVector base := {
    base_positive := base_positive;
    b0_1 := b0_1;
    base_good := base_good
  }.

End PseudoMersenneBaseParamProofs.
