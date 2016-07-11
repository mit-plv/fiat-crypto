Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import VerdiTactics.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section ExtendedBaseVector.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (Pow2Base.base_from_limb_widths limb_widths).

  (* This section defines a new BaseVector that has double the length of the BaseVector
  * used to construct [params]. The coefficients of the new vector are as follows:
  *
  * ext_base[i] = if (i < length base) then base[i] else 2^k * base[i]
  *
  * The purpose of this construction is that it allows us to multiply numbers expressed
  * using [base], obtaining a number expressed using [ext_base]. (Numbers are "expressed" as
  * vectors of digits; the value of a digit vector is obtained by doing a dot product with
  * the base vector.) So if x, y are digit vectors:
  *
  * (x \dot base) * (y \dot base) = (z \dot ext_base)
  *
  * Then we can separate z into its first and second halves:
  *
  * (z \dot ext_base) = (z1 \dot base) + (2 ^ k) * (z2 \dot base)
  *
  * Now, if we want to reduce the product modulo 2 ^ k - c:
  *
  * (z \dot ext_base) mod (2^k-c)= (z1 \dot base) + (2 ^ k) * (z2 \dot base) mod (2^k-c)
  * (z \dot ext_base) mod (2^k-c)= (z1 \dot base) + c * (z2 \dot base) mod (2^k-c)
  *
  * This sum may be short enough to express using base; if not, we can reduce again.
  *)
  Definition ext_base := base ++ (map (Z.mul (2^k)) base).

  Lemma ext_base_positive : forall b, In b ext_base -> b > 0.
  Proof.
    unfold ext_base. intros b In_b_base.
    rewrite in_app_iff in In_b_base.
    destruct In_b_base as [In_b_base | In_b_extbase].
    + eapply BaseSystem.base_positive.
      eapply In_b_base.
    + eapply in_map_iff in In_b_extbase.
      destruct In_b_extbase as [b' [b'_2k_b  In_b'_base]].
      subst.
      specialize (BaseSystem.base_positive b' In_b'_base); intro base_pos.
      replace 0 with (2 ^ k * 0) by ring.
      apply (Zmult_gt_compat_l b' 0 (2 ^ k)); [| apply base_pos; intuition].
      rewrite Z.gt_lt_iff.
      apply Z.pow_pos_nonneg; intuition.
      pose proof k_nonneg; omega.
  Qed.

  Lemma base_length_nonzero : (0 < length base)%nat.
  Proof.
    assert (nth_default 0 base 0 = 1) by (apply BaseSystem.b0_1).
    unfold nth_default in H.
    case_eq (nth_error base 0); intros;
      try (rewrite H0 in H; omega).
    apply (nth_error_value_length _ 0 base z); auto.
  Qed.

  Lemma b0_1 : forall x, nth_default x ext_base 0 = 1.
  Proof.
    intros. unfold ext_base.
    rewrite nth_default_app.
    assert (0 < length base)%nat by (apply base_length_nonzero).
    destruct (lt_dec 0 (length base)); try apply BaseSystem.b0_1; try omega.
  Qed.

  Lemma two_k_nonzero : 2^k <> 0.
  Proof.
    pose proof (Z.pow_eq_0 2 k k_nonneg).
    intuition.
  Qed.

  Lemma map_nth_default_base_high : forall n, (n < (length base))%nat ->
    nth_default 0 (map (Z.mul (2 ^ k)) base) n =
    (2 ^ k) * (nth_default 0 base n).
  Proof.
    intros.
    erewrite map_nth_default; auto.
  Qed.

  Lemma base_good_over_boundary : forall
    (i : nat)
    (l : (i < length base)%nat)
    (j' : nat)
    (Hj': (i + j' < length base)%nat)
    ,
    2 ^ k * (nth_default 0 base i * nth_default 0 base j') =
    2 ^ k * (nth_default 0 base i * nth_default 0 base j') /
    (2 ^ k * nth_default 0 base (i + j')) *
    (2 ^ k * nth_default 0 base (i + j'))
  .
  Proof.
    intros.
    remember (nth_default 0 base) as b.
    rewrite Zdiv_mult_cancel_l by (exact two_k_nonzero).
    replace (b i * b j' / b (i + j')%nat * (2 ^ k * b (i + j')%nat))
     with  ((2 ^ k * (b (i + j')%nat * (b i * b j' / b (i + j')%nat)))) by ring.
    rewrite Z.mul_cancel_l by (exact two_k_nonzero).
    replace (b (i + j')%nat * (b i * b j' / b (i + j')%nat))
     with ((b i * b j' / b (i + j')%nat) * b (i + j')%nat) by ring.
    subst b.
    apply (BaseSystem.base_good i j'); omega.
  Qed.

  Lemma ext_base_good :
    forall i j, (i+j < length ext_base)%nat ->
    let b := nth_default 0 ext_base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    intros.
    subst b. subst r.
    unfold ext_base in *.
    rewrite app_length in H; rewrite map_length in H.
    repeat rewrite nth_default_app.
    destruct (lt_dec i (length base));
      destruct (lt_dec j (length base));
      destruct (lt_dec (i + j) (length base));
      try omega.
    { (* i < length base, j < length base, i + j < length base *)
      apply BaseSystem.base_good; auto.
    } { (* i < length base, j < length base, i + j >= length base *)
      rewrite (map_nth_default _ _ _ _ 0) by omega.
      apply base_matches_modulus; omega.
    } { (* i < length base, j >= length base, i + j >= length base *)
      do 2 rewrite map_nth_default_base_high by omega.
      remember (j - length base)%nat as j'.
      replace (i + j - length base)%nat with (i + j')%nat by omega.
      replace (nth_default 0 base i * (2 ^ k * nth_default 0 base j'))
         with (2 ^ k * (nth_default 0 base i * nth_default 0 base j'))
         by ring.
      eapply base_good_over_boundary; eauto; omega.
    } { (* i >= length base, j < length base, i + j >= length base *)
      do 2 rewrite map_nth_default_base_high by omega.
      remember (i - length base)%nat as i'.
      replace (i + j - length base)%nat with (j + i')%nat by omega.
      replace (2 ^ k * nth_default 0 base i' * nth_default 0 base j)
         with (2 ^ k * (nth_default 0 base j * nth_default 0 base i'))
         by ring.
      eapply base_good_over_boundary; eauto; omega.
    }
  Qed.

  Instance ExtBaseVector : BaseSystem.BaseVector ext_base := {
    base_positive := ext_base_positive;
    b0_1 := b0_1;
    base_good := ext_base_good
  }.

  Lemma extended_base_length:
      length ext_base = (length base + length base)%nat.
  Proof.
    unfold ext_base; rewrite app_length; rewrite map_length; auto.
  Qed.
End ExtendedBaseVector.
