Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Lnot.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  Lemma ones_spec : forall n m, 0 <= n -> 0 <= m -> Z.testbit (Z.ones n) m = if Z_lt_dec m n then true else false.
  Proof.
    intros.
    break_match.
    + apply Z.ones_spec_low. omega.
    + apply Z.ones_spec_high. omega.
  Qed.
  Hint Rewrite ones_spec using zutil_arith : Ztestbit.

  Lemma ones_spec_full : forall n m, Z.testbit (Z.ones n) m
                                     = if Z_lt_dec m 0
                                       then false
                                       else if Z_lt_dec n 0
                                            then true
                                            else if Z_lt_dec m n then true else false.
  Proof.
    intros n m.
    repeat (break_match || autorewrite with Ztestbit); try reflexivity; try omega.
    unfold Z.ones.
    rewrite <- Z.shiftr_opp_r, Z.shiftr_eq_0 by (simpl; omega); simpl.
    destruct m; simpl in *; try reflexivity.
    exfalso; auto using Zlt_neg_0.
  Qed.
  Hint Rewrite ones_spec_full : Ztestbit_full.

  Lemma testbit_pow2_mod : forall a n i, 0 <= n ->
  Z.testbit (Z.pow2_mod a n) i = if Z_lt_dec i n then Z.testbit a i else false.
  Proof.
    cbv [Z.pow2_mod]; intros a n i H; destruct (Z_le_dec 0 i);
      repeat match goal with
          | |- _ => rewrite Z.testbit_neg_r by omega
          | |- _ => break_innermost_match_step
          | |- _ => omega
          | |- _ => reflexivity
          | |- _ => progress autorewrite with Ztestbit
          end.
  Qed.
  Hint Rewrite testbit_pow2_mod using zutil_arith : Ztestbit.

  Lemma testbit_pow2_mod_full : forall a n i,
      Z.testbit (Z.pow2_mod a n) i = if Z_lt_dec n 0
                                     then if Z_lt_dec i 0 then false else Z.testbit a i
                                     else if Z_lt_dec i n then Z.testbit a i else false.
  Proof.
    intros a n i; destruct (Z_lt_dec n 0); [ | apply testbit_pow2_mod; omega ].
    unfold Z.pow2_mod.
    autorewrite with Ztestbit_full;
      repeat break_match;
      autorewrite with Ztestbit;
      reflexivity.
  Qed.
  Hint Rewrite testbit_pow2_mod_full : Ztestbit_full.

  Lemma bits_above_pow2 a n : 0 <= a < 2^n -> Z.testbit a n = false.
  Proof.
    intros.
    destruct (Z_zerop a); subst; autorewrite with Ztestbit; trivial.
    apply Z.bits_above_log2; auto with zarith concl_log2.
  Qed.
  Hint Rewrite bits_above_pow2 using zutil_arith : Ztestbit.

  Lemma testbit_low : forall n x i, (0 <= i < n) ->
    Z.testbit x i = Z.testbit (Z.land x (Z.ones n)) i.
  Proof.
    intros.
    rewrite Z.land_ones by omega.
    symmetry.
    apply Z.mod_pow2_bits_low.
    omega.
  Qed.

  Lemma testbit_add_shiftl_low : forall i, (0 <= i) -> forall a b n, (i < n) ->
    Z.testbit (a + Z.shiftl b n) i = Z.testbit a i.
  Proof.
    intros i H a b n H0.
    erewrite Z.testbit_low; eauto.
    rewrite Z.land_ones, Z.shiftl_mul_pow2 by omega.
    rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 n); omega).
    auto using Z.mod_pow2_bits_low.
  Qed.
  Hint Rewrite testbit_add_shiftl_low using zutil_arith : Ztestbit.

  Lemma testbit_sub_pow2 n i x (i_range:0 <= i < n) (x_range:0 < x < 2 ^ n) :
    Z.testbit (2 ^ n - x) i = negb (Z.testbit (x - 1)  i).
  Proof.
    rewrite <-Z.lnot_spec, Z.lnot_sub1 by omega.
    rewrite <-(Z.mod_pow2_bits_low (-x) _ _ (proj2 i_range)).
    f_equal.
    rewrite Z.mod_opp_l_nz; autorewrite with zsimplify; omega.
  Qed.

  Lemma testbit_false_bound : forall a x, 0 <= x ->
    (forall n, ~ (n < x) -> Z.testbit a n = false) ->
    a < 2 ^ x.
  Proof.
    intros a x H H0.
    assert (H1 : a = Z.pow2_mod a x). {
     apply Z.bits_inj'; intros.
     rewrite Z.testbit_pow2_mod by omega; break_match; auto.
    }
    rewrite H1.
    cbv [Z.pow2_mod]; rewrite Z.land_ones by auto.
    try apply Z.mod_pos_bound; Z.zero_bounds.
  Qed.

  Lemma testbit_neg_eq_if x n :
    0 <= n ->
    - (2 ^ n) <= x  < 2 ^ n ->
    Z.b2z (if x <? 0 then true else Z.testbit x n) = - (x / 2 ^ n) mod 2.
  Proof.
    intros. break_match; Z.ltb_to_lt.
    { autorewrite with zsimplify. reflexivity. }
    { autorewrite with zsimplify.
      rewrite Z.bits_above_pow2 by omega.
      reflexivity. }
  Qed.
End Z.
