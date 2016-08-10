Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.BaseSystemProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section ExtendedBaseVector.
  Context (limb_widths : list Z)
          (limb_widths_nonnegative : forall x, In x limb_widths -> 0 <= x).
  Local Notation k := (sum_firstn limb_widths (length limb_widths)).
  Local Notation base := (base_from_limb_widths limb_widths).

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
  Definition ext_limb_widths := limb_widths ++ limb_widths.
  Definition ext_base := base_from_limb_widths ext_limb_widths.
  Lemma ext_base_alt : ext_base = base ++ (map (Z.mul (2^k)) base).
  Proof.
    unfold ext_base, ext_limb_widths.
    rewrite base_from_limb_widths_app by auto.
    rewrite two_p_equiv.
    reflexivity.
  Qed.

  Lemma ext_base_positive : forall b, In b ext_base -> b > 0.
  Proof.
    apply base_positive; unfold ext_limb_widths.
    intros ? H. apply in_app_or in H; destruct H; auto.
  Qed.

  Lemma b0_1 : forall x, nth_default x base 0 = 1 -> nth_default x ext_base 0 = 1.
  Proof.
    intros. rewrite ext_base_alt, nth_default_app.
    destruct base; assumption.
  Qed.

  Lemma map_nth_default_base_high : forall n, (n < (length base))%nat ->
    nth_default 0 (map (Z.mul (2 ^ k)) base) n =
    (2 ^ k) * (nth_default 0 base n).
  Proof.
    intros.
    erewrite map_nth_default; auto.
  Qed.

  Lemma ext_limb_widths_nonneg
        (limb_widths_nonneg : forall w : Z, In w limb_widths -> 0 <= w)
    : forall w : Z, In w ext_limb_widths -> 0 <= w.
  Proof.
    unfold ext_limb_widths; setoid_rewrite in_app_iff.
    intros ? [?|?]; auto.
  Qed.

  Section base_good.
    Context (two_k_nonzero : 2^k <> 0)
            (base_good : forall i j, (i+j < length base)%nat ->
                                     let b := nth_default 0 base in
                                     let r := (b i * b j) / b (i+j)%nat in
                                     b i * b j = r * b (i+j)%nat)
            (limb_widths_match_modulus : forall i j,
                (i < length limb_widths)%nat ->
                (j < length limb_widths)%nat ->
                (i + j >= length limb_widths)%nat ->
                let w_sum := sum_firstn limb_widths in
                k + w_sum (i + j - length limb_widths)%nat <= w_sum i + w_sum j).

    Lemma base_good_over_boundary
      : forall (i : nat)
               (l : (i < length base)%nat)
               (j' : nat)
               (Hj': (i + j' < length base)%nat),
        2 ^ k * (nth_default 0 base i * nth_default 0 base j') =
        (2 ^ k * (nth_default 0 base i * nth_default 0 base j'))
          / (2 ^ k * nth_default 0 base (i + j')) *
        (2 ^ k * nth_default 0 base (i + j')).
    Proof.
      clear limb_widths_match_modulus.
      intros.
      remember (nth_default 0 base) as b.
      rewrite Zdiv_mult_cancel_l by (exact two_k_nonzero).
      replace (b i * b j' / b (i + j')%nat * (2 ^ k * b (i + j')%nat))
      with  ((2 ^ k * (b (i + j')%nat * (b i * b j' / b (i + j')%nat)))) by ring.
      rewrite Z.mul_cancel_l by (exact two_k_nonzero).
      replace (b (i + j')%nat * (b i * b j' / b (i + j')%nat))
      with ((b i * b j' / b (i + j')%nat) * b (i + j')%nat) by ring.
      subst b.
      apply (base_good i j'); omega.
    Qed.

    Lemma ext_base_good :
      forall i j, (i+j < length ext_base)%nat ->
                  let b := nth_default 0 ext_base in
                  let r := (b i * b j) / b (i+j)%nat in
                  b i * b j = r * b (i+j)%nat.
    Proof.
      intros.
      subst b. subst r.
      rewrite ext_base_alt in *.
      rewrite app_length in H; rewrite map_length in H.
      repeat rewrite nth_default_app.
      repeat break_if; try omega.
      { (* i < length base, j < length base, i + j < length base *)
        auto using BaseSystem.base_good.
      } { (* i < length base, j < length base, i + j >= length base *)
        rewrite (map_nth_default _ _ _ _ 0) by omega.
        apply base_matches_modulus; auto using limb_widths_nonnegative, limb_widths_match_modulus;
        distr_length.
        assumption.
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
  End base_good.

  Lemma extended_base_length:
      length ext_base = (length base + length base)%nat.
  Proof.
    clear limb_widths_nonnegative.
    unfold ext_base, ext_limb_widths; autorewrite with distr_length; reflexivity.
  Qed.

  Lemma firstn_us_base_ext_base : forall (us : BaseSystem.digits),
      (length us <= length base)%nat
      -> firstn (length us) base = firstn (length us) ext_base.
  Proof.
    rewrite ext_base_alt; intros.
    rewrite firstn_app_inleft; auto; omega.
  Qed.

  Lemma decode_short : forall (us : BaseSystem.digits),
    (length us <= length base)%nat ->
    BaseSystem.decode base us = BaseSystem.decode ext_base us.
  Proof. auto using decode_short_initial, firstn_us_base_ext_base. Qed.

  Section BaseVector.
    Context {bv : BaseSystem.BaseVector base}
            (limb_widths_match_modulus : forall i j,
                (i < length limb_widths)%nat ->
                (j < length limb_widths)%nat ->
                (i + j >= length limb_widths)%nat ->
                let w_sum := sum_firstn limb_widths in
                k + w_sum (i + j - length limb_widths)%nat <= w_sum i + w_sum j).

    Instance ExtBaseVector : BaseSystem.BaseVector ext_base :=
      { base_positive := ext_base_positive;
        b0_1 x := b0_1 x (BaseSystem.b0_1 _);
        base_good := ext_base_good (two_sum_firstn_limb_widths_nonzero limb_widths_nonnegative _) BaseSystem.base_good limb_widths_match_modulus }.
  End BaseVector.
End ExtendedBaseVector.

Hint Rewrite @extended_base_length : distr_length.
