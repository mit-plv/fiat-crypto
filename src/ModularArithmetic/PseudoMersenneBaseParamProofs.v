Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import VerdiTactics.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section PseudoMersenneBaseParamProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).

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

  Lemma two_k_nonzero : 2^k <> 0.
  Proof.
    pose proof (Z.pow_eq_0 2 k k_nonneg).
    intuition.
  Qed.

  Lemma base_matches_modulus: forall i j,
    (i   <  length limb_widths)%nat ->
    (j   <  length limb_widths)%nat ->
    (i+j >= length limb_widths)%nat->
    let b := nth_default 0 base in
    let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
              b i * b j = r * (2^k * b (i+j-length base)%nat).
  Proof.
    intros.
    rewrite (Z.mul_comm r).
    subst r.
    assert (i + j - length limb_widths < length limb_widths)%nat by omega.
    rewrite Z.mul_div_eq by (apply Z.gt_lt_iff; apply Z.mul_pos_pos;
      subst b; rewrite ?nth_default_base; zero_bounds; rewrite ?base_from_limb_widths_length;
      auto using sum_firstn_limb_widths_nonneg, limb_widths_nonneg).
    rewrite (Zminus_0_l_reverse (b i * b j)) at 1.
    f_equal.
    subst b.
    repeat rewrite nth_default_base by (rewrite ?base_from_limb_widths_length; auto).
    do 2 rewrite <- Z.pow_add_r by auto using sum_firstn_limb_widths_nonneg.
    symmetry.
    apply Z.mod_same_pow.
    split.
    + apply Z.add_nonneg_nonneg; auto using sum_firstn_limb_widths_nonneg.
    + rewrite base_from_limb_widths_length; auto using limb_widths_nonneg, limb_widths_match_modulus.
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
     rewrite <-base_from_limb_widths_length; auto using limb_widths_nonneg.
   Qed.

  Lemma base_length : length base = length limb_widths.
  Proof.
    auto using base_from_limb_widths_length.
  Qed.

  Global Instance bv : BaseSystem.BaseVector base := {
    base_positive := base_positive limb_widths_nonneg;
    b0_1 := fun x => b0_1 x limb_widths_nonnil;
    base_good := base_good
  }.

End PseudoMersenneBaseParamProofs.
