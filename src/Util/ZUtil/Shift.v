Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Ones.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Pow2Mod.
Require Import Crypto.Util.ZUtil.Le.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.LandLorShiftBounds.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Local Open Scope Z_scope.

Module Z.
  Lemma shiftr_add_shiftl_high : forall n m a b, 0 <= n <= m -> 0 <= a < 2 ^ n ->
    Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr b (m - n).
  Proof.
    intros n m a b H H0.
    rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    replace (2 ^ m) with (2 ^ n * 2 ^ (m - n)) by
      (rewrite <-Z.pow_add_r by lia; f_equal; ring).
    rewrite <-Z.div_div, Z.div_add, (Z.div_small a) ; try solve
      [assumption || apply Z.pow_nonzero || apply Z.pow_pos_nonneg; lia].
    f_equal; ring.
  Qed.
  Hint Rewrite Z.shiftr_add_shiftl_high using zutil_arith : pull_Zshift.
  Hint Rewrite <- Z.shiftr_add_shiftl_high using zutil_arith : push_Zshift.

  Lemma shiftr_add_shiftl_low : forall n m a b, 0 <= m <= n -> 0 <= a < 2 ^ n ->
                                           Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr a m + Z.shiftr b (m - n).
  Proof.
    intros n m a b H H0.
    rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2, Z.shiftr_mul_pow2 by lia.
    replace (2 ^ n) with (2 ^ (n - m) * 2 ^ m) by
        (rewrite <-Z.pow_add_r by lia; f_equal; ring).
    rewrite Z.mul_assoc, Z.div_add by (apply Z.pow_nonzero; lia).
    repeat f_equal; ring.
  Qed.
  Hint Rewrite Z.shiftr_add_shiftl_low using zutil_arith : pull_Zshift.
  Hint Rewrite <- Z.shiftr_add_shiftl_low using zutil_arith : push_Zshift.

  Lemma testbit_add_shiftl_high : forall i, (0 <= i) -> forall a b n, (0 <= n <= i) ->
                                                          0 <= a < 2 ^ n ->
                                                          Z.testbit (a + Z.shiftl b n) i = Z.testbit b (i - n).
  Proof.
    intros i ?.
    apply natlike_ind with (x := i); [ intros a b n | intros x H0 H1 a b n | ]; intros; try assumption;
      (destruct (Z.eq_dec 0 n); [ subst; rewrite Z.pow_0_r in *;
                                  replace a with 0 by lia; f_equal; ring | ]); try lia.
    rewrite <-Z.add_1_r at 1. rewrite <-Z.shiftr_spec by assumption.
    replace (Z.succ x - n) with (x - (n - 1)) by ring.
    rewrite shiftr_add_shiftl_low, <-Z.shiftl_opp_r with (a := b) by lia.
    rewrite <-H1 with (a := Z.shiftr a 1); try lia; [ repeat f_equal; ring | ].
    rewrite Z.shiftr_div_pow2 by lia.
    split; apply Z.div_pos || apply Z.div_lt_upper_bound;
      try solve [rewrite ?Z.pow_1_r; lia].
    rewrite <-Z.pow_add_r by lia.
    replace (1 + (n - 1)) with n by ring; lia.
  Qed.
  Hint Rewrite testbit_add_shiftl_high using zutil_arith : Ztestbit.

  Lemma testbit_add_shiftl i a b n
        (Ha : 0 <= a < 2^n)
        (Hb : 0 <= n)
        (Hn : 0 <= i) :
    Z.testbit (a + Z.shiftl b n) i = if (i <? n)
                                then Z.testbit a i
                                else Z.testbit b (i - n).
  Proof. destruct (Z.ltb_spec i n); autorewrite with Ztestbit; reflexivity. Qed.
  
  Lemma shiftr_succ : forall n x,
    Z.shiftr n (Z.succ x) = Z.shiftr (Z.shiftr n x) 1.
  Proof.
    intros.
    rewrite Z.shiftr_shiftr by lia.
    reflexivity.
  Qed.
  Hint Rewrite Z.shiftr_succ using zutil_arith : push_Zshift.
  Hint Rewrite <- Z.shiftr_succ using zutil_arith : pull_Zshift.

  Lemma shiftr_1_r_le : forall a b, a <= b ->
    Z.shiftr a 1 <= Z.shiftr b 1.
  Proof.
    intros.
    rewrite !Z.shiftr_div_pow2, Z.pow_1_r by lia.
    apply Z.div_le_mono; lia.
  Qed.
  Hint Resolve shiftr_1_r_le : zarith.

  Lemma shiftr_le : forall a b i : Z, 0 <= i -> a <= b -> a >> i <= b >> i.
  Proof.
    intros a b i ?; revert a b. apply natlike_ind with (x := i); intros; auto.
    rewrite !shiftr_succ, shiftr_1_r_le; eauto. reflexivity.
  Qed.
  Hint Resolve shiftr_le : zarith.

  Lemma shiftr_ones' : forall a n, 0 <= a < 2 ^ n -> forall i, (0 <= i) ->
    Z.shiftr a i <= Z.ones (n - i) \/ n <= i.
  Proof.
    intros a n H.
    apply natlike_ind.
    + unfold Z.ones.
      rewrite Z.shiftr_0_r, Z.shiftl_1_l, Z.sub_0_r.
      lia.
    + intros x H0 H1.
      destruct (Z_lt_le_dec x n); try lia.
      intuition auto with zarith lia.
      left.
      rewrite shiftr_succ.
      replace (n - Z.succ x) with (Z.pred (n - x)) by lia.
      rewrite Z.ones_pred by lia.
      apply Z.shiftr_1_r_le.
      assumption.
  Qed.

  Lemma shiftr_ones : forall a n i, 0 <= a < 2 ^ n -> (0 <= i) -> (i <= n) ->
    Z.shiftr a i <= Z.ones (n - i) .
  Proof.
    intros a n i G G0 G1.
    destruct (Z_le_lt_eq_dec i n G1).
    + destruct (Z.shiftr_ones' a n G i G0); lia.
    + subst; rewrite Z.sub_diag.
      destruct (Z.eq_dec a 0).
      - subst; rewrite Z.shiftr_0_l; reflexivity.
      - rewrite Z.shiftr_eq_0; try lia; try reflexivity.
        apply Z.log2_lt_pow2; lia.
  Qed.
  Hint Resolve shiftr_ones : zarith.

  Lemma shiftr_upper_bound : forall a n, 0 <= n -> 0 <= a <= 2 ^ n -> Z.shiftr a n <= 1.
  Proof.
    intros a ? ? [a_nonneg a_upper_bound].
    apply Z_le_lt_eq_dec in a_upper_bound.
    destruct a_upper_bound.
    + destruct (Z.eq_dec 0 a).
      - subst; rewrite Z.shiftr_0_l; lia.
      - rewrite Z.shiftr_eq_0; auto; try lia.
        apply Z.log2_lt_pow2; auto; lia.
    + subst.
      rewrite Z.shiftr_div_pow2 by assumption.
      assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
      rewrite Z.div_same;  lia.
  Qed.
  Hint Resolve shiftr_upper_bound : zarith.

  Lemma lor_shiftl : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor a (Z.shiftl b n) = a + (Z.shiftl b n).
  Proof.
    intros a b n H H0.
    apply Z.bits_inj'; intros t ?.
    rewrite Z.lor_spec, Z.shiftl_spec by assumption.
    destruct (Z_lt_dec t n).
    + rewrite Z.testbit_add_shiftl_low by lia.
      rewrite Z.testbit_neg_r with (n := t - n) by lia.
      apply Bool.orb_false_r.
    + rewrite testbit_add_shiftl_high by lia.
      replace (Z.testbit a t) with false; [ apply Bool.orb_false_l | ].
      symmetry.
      apply Z.testbit_false; try lia.
      rewrite Z.div_small; try reflexivity.
      split; try eapply Z.lt_le_trans with (m := 2 ^ n); try lia.
      apply Z.pow_le_mono_r; lia.
  Qed.
  Hint Rewrite <- Z.lor_shiftl using zutil_arith : convert_to_Ztestbit.

  Lemma lor_shiftl' : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor (Z.shiftl b n) a = (Z.shiftl b n) + a.
  Proof.
    intros; rewrite Z.lor_comm, Z.add_comm; apply lor_shiftl; assumption.
  Qed.
  Hint Rewrite <- Z.lor_shiftl' using zutil_arith : convert_to_Ztestbit.

  Lemma shiftl_spec_full a n m
    : Z.testbit (a << n) m = if Z_lt_dec m n
                             then false
                             else if Z_le_dec 0 m
                                  then Z.testbit a (m - n)
                                  else false.
  Proof.
    repeat break_match; auto using Z.shiftl_spec_low, Z.shiftl_spec, Z.testbit_neg_r with lia.
  Qed.
  Hint Rewrite shiftl_spec_full : Ztestbit_full.

  Lemma shiftr_spec_full a n m
    : Z.testbit (a >> n) m = if Z_lt_dec m (-n)
                             then false
                             else if Z_le_dec 0 m
                                  then Z.testbit a (m + n)
                                  else false.
  Proof.
    rewrite <- Z.shiftl_opp_r, shiftl_spec_full, Z.sub_opp_r; reflexivity.
  Qed.
  Hint Rewrite shiftr_spec_full : Ztestbit_full.

  Lemma testbit_add_shiftl_full i (Hi : 0 <= i) a b n (Ha : 0 <= a < 2^n)
    : Z.testbit (a + b << n) i
      = if (i <? n) then Z.testbit a i else Z.testbit b (i - n).
  Proof.
    assert (0 < 2^n) by lia.
    assert (0 <= n) by eauto 2 with zarith.
    pose proof (Zlt_cases i n); break_match; autorewrite with Ztestbit; reflexivity.
  Qed.
  Hint Rewrite testbit_add_shiftl_full using zutil_arith : Ztestbit.

  Lemma land_add_land : forall n m a b, (m <= n)%nat ->
    Z.land ((Z.land a (Z.ones (Z.of_nat n))) + (Z.shiftl b (Z.of_nat n))) (Z.ones (Z.of_nat m)) = Z.land a (Z.ones (Z.of_nat m)).
  Proof.
    intros n m a b H.
    rewrite !Z.land_ones by apply Nat2Z.is_nonneg.
    rewrite Z.shiftl_mul_pow2 by apply Nat2Z.is_nonneg.
    replace (b * 2 ^ Z.of_nat n) with
      ((b * 2 ^ Z.of_nat (n - m)) * 2 ^ Z.of_nat m) by
      (rewrite (le_plus_minus m n) at 2; try assumption;
       rewrite Nat2Z.inj_add, Z.pow_add_r by apply Nat2Z.is_nonneg; ring).
    rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat m)); lia).
    symmetry. apply Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; lia).
    rewrite (le_plus_minus m n) by assumption.
    rewrite Nat2Z.inj_add, Z.pow_add_r by apply Nat2Z.is_nonneg.
    apply Z.divide_factor_l.
  Qed.

  Lemma shiftl_add x y z : 0 <= z -> (x + y) << z = (x << z) + (y << z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftl_add using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftl_add using zutil_arith : pull_Zshift.

  Lemma shiftr_add x y z : z <= 0 -> (x + y) >> z = (x >> z) + (y >> z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftr_add using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftr_add using zutil_arith : pull_Zshift.

  Lemma shiftl_sub x y z : 0 <= z -> (x - y) << z = (x << z) - (y << z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftl_sub using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftl_sub using zutil_arith : pull_Zshift.

  Lemma shiftr_sub x y z : z <= 0 -> (x - y) >> z = (x >> z) - (y >> z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftr_sub using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftr_sub using zutil_arith : pull_Zshift.

  Lemma compare_add_shiftl : forall x1 y1 x2 y2 n, 0 <= n ->
    Z.pow2_mod x1 n = x1 -> Z.pow2_mod x2 n = x2  ->
    x1 + (y1 << n) ?= x2 + (y2 << n) =
      if Z.eq_dec y1 y2
      then x1 ?= x2
      else y1 ?= y2.
  Proof.
  repeat match goal with
           | |- _ => progress intros
           | |- _ => progress subst y1
           | |- _ => rewrite Z.shiftl_mul_pow2 by lia
           | |- _ => rewrite Z.add_compare_mono_r
           | |- _ => rewrite <-Z.mul_sub_distr_r
           | |- _ => break_innermost_match_step
           | H : Z.pow2_mod _ _ = _ |- _ => rewrite Z.pow2_mod_id_iff in H by lia
           | H : ?a <> ?b |- _ = (?a ?= ?b) =>
             case_eq (a ?= b); rewrite ?Z.compare_eq_iff, ?Z.compare_gt_iff, ?Z.compare_lt_iff
           | |- _ + (_ * _) > _ + (_ * _) => cbv [Z.gt]
           | |- _ + (_ * ?x) < _ + (_ * ?x) =>
             apply Z.lt_sub_lt_add; apply Z.lt_le_trans with (m := 1 * x); [lia|]
           | |- _ => apply Z.mul_le_mono_nonneg_r; lia
           | |- _ => reflexivity
           | |- _ => congruence
           end.
  Qed.

  (* (* not compatible with x mod 0 = x *)
  Lemma shiftl_opp_l a n
    : Z.shiftl (-a) n = - Z.shiftl a n - (if Z_zerop (a mod 2 ^ (- n)) then 0 else 1).
  Proof.
    destruct (Z_dec 0 n) as [ [?|?] | ? ];
      subst;
      rewrite ?Z.pow_neg_r by lia;
      autorewrite with zsimplify_const;
      [ | | simpl; lia ].
    { rewrite !Z.shiftl_mul_pow2 by lia.
      nia. }
    { rewrite !Z.shiftl_div_pow2 by lia.
      rewrite Z.div_opp_l_complete by auto with zarith.
      reflexivity. }
  Qed.
  Hint Rewrite shiftl_opp_l : push_Zshift.
  Hint Rewrite <- shiftl_opp_l : pull_Zshift.

  Lemma shiftr_opp_l a n
    : Z.shiftr (-a) n = - Z.shiftr a n - (if Z_zerop (a mod 2 ^ n) then 0 else 1).
  Proof.
    unfold Z.shiftr; rewrite shiftl_opp_l at 1; rewrite Z.opp_involutive.
    reflexivity.
  Qed.
  Hint Rewrite shiftr_opp_l : push_Zshift.
  Hint Rewrite <- shiftr_opp_l : pull_Zshift. *)

  Lemma shl_shr_lt x y n m (Hx : 0 <= x < 2^n) (Hy : 0 <= y < 2^n) (Hm : 0 <= m <= n)
    : 0 <= (x >> (n - m)) + ((y << m) mod 2^n) < 2^n.
  Proof.
    cut (0 <= (x >> (n - m)) + ((y << m) mod 2^n) <= 2^n - 1); [ lia | ].
    assert (0 <= x <= 2^n - 1) by lia.
    assert (0 <= y <= 2^n - 1) by lia.
    assert (0 < 2 ^ (n - m)) by auto with zarith.
    assert (0 <= y mod 2 ^ (n - m) < 2^(n-m)) by auto with zarith.
    assert (0 <= y mod 2 ^ (n - m) <= 2 ^ (n - m) - 1) by lia.
    assert (0 <= (y mod 2 ^ (n - m)) * 2^m <= (2^(n-m) - 1)*2^m) by auto with zarith.
    assert (0 <= x / 2^(n-m) < 2^n / 2^(n-m)).
    { split; Z.zero_bounds.
      apply Z.div_lt_upper_bound; autorewrite with pull_Zpow zsimplify; nia. }
    autorewrite with Zshift_to_pow.
    split; Z.zero_bounds.
    replace (2^n) with (2^(n-m) * 2^m) by (autorewrite with pull_Zpow; f_equal; lia).
    rewrite Zmult_mod_distr_r.
    autorewrite with pull_Zpow zsimplify push_Zmul in * |- .
    nia.
  Qed.

  Lemma add_shift_mod x y n m
        (Hx : 0 <= x < 2^n) (Hy : 0 <= y)
        (Hn : 0 <= n) (Hm : 0 < m)
    : (x + y << n) mod (m * 2^n) = x + (y mod m) << n.
  Proof.
    pose proof (Z.mod_bound_pos y m).
    specialize_by lia.
    assert (0 < 2^n) by auto with zarith.
    autorewrite with Zshift_to_pow.
    rewrite Zplus_mod, !Zmult_mod_distr_r.
    rewrite Zplus_mod, !Zmod_mod, <- Zplus_mod.
    rewrite !(Zmod_eq (_ + _)) by nia.
    etransitivity; [ | apply Z.add_0_r ].
    rewrite <- !Z.add_opp_r, <- !Z.add_assoc.
    repeat apply f_equal.
    ring_simplify.
    cut (((x + y mod m * 2 ^ n) / (m * 2 ^ n)) = 0); [ nia | ].
    apply Z.div_small; split; nia.
  Qed.

  Lemma add_mul_mod x y n m
        (Hx : 0 <= x < 2^n) (Hy : 0 <= y)
        (Hn : 0 <= n) (Hm : 0 < m)
    : (x + y * 2^n) mod (m * 2^n) = x + (y mod m) * 2^n.
  Proof.
    generalize (add_shift_mod x y n m).
    autorewrite with Zshift_to_pow; auto.
  Qed.

  Lemma lt_pow_2_shiftr : forall a n, 0 <= a < 2 ^ n -> a >> n = 0.
  Proof.
    intros a n H.
    destruct (Z_le_dec 0 n).
    + rewrite Z.shiftr_div_pow2 by assumption.
      auto using Z.div_small.
    + assert (2 ^ n = 0) by (apply Z.pow_neg_r; lia).
      lia.
  Qed.

  Hint Rewrite Z.pow2_bits_eqb using zutil_arith : Ztestbit.
  Lemma pow_2_shiftr : forall n, 0 <= n -> (2 ^ n) >> n = 1.
  Proof.
    intros; apply Z.bits_inj'; intros.
    replace 1 with (2 ^ 0) by ring.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress rewrite ?Z.eqb_eq, ?Z.eqb_neq in *
           | |- _ => progress autorewrite with Ztestbit
           | |- context[Z.eqb ?a ?b] => case_eq (Z.eqb a b)
           | |- _ => reflexivity || lia
           end.
  Qed.

  Lemma lt_mul_2_pow_2_shiftr : forall a n, 0 <= a < 2 * 2 ^ n ->
                                            a >> n = if Z_lt_dec a (2 ^ n) then 0 else 1.
  Proof.
    intros a n H; break_match; [ apply lt_pow_2_shiftr; lia | ].
    destruct (Z_le_dec 0 n).
    + replace (2 * 2 ^ n) with (2 ^ (n + 1)) in *
        by (rewrite Z.pow_add_r; try lia; ring).
      pose proof (Z.shiftr_ones a (n + 1) n H).
      pose proof (Z.shiftr_le (2 ^ n) a n).
      specialize_by lia.
      replace (n + 1 - n) with 1 in * by ring.
      replace (Z.ones 1) with 1 in * by reflexivity.
      rewrite pow_2_shiftr in * by lia.
      lia.
    + assert (2 ^ n = 0) by (apply Z.pow_neg_r; lia).
      lia.
  Qed.

  Lemma shiftr_nonneg_le : forall a n, 0 <= a -> 0 <= n -> a >> n <= a.
  Proof.
    intros.
    repeat match goal with
           | [ H : _ <= _ |- _ ]
             => rewrite Z.lt_eq_cases in H
           | [ H : _ \/ _ |- _ ] => destruct H
           | _ => progress subst
           | _ => progress autorewrite with zsimplify Zshift_to_pow
           | _ => solve [ auto with zarith lia ]
           end.
  Qed.
  Hint Resolve shiftr_nonneg_le : zarith.

  Lemma lor_shift_land_ones x n
    : 0 <= n -> x = Z.lor ((x >> n) << n) (Z.land x (Z.ones n)).
  Proof.
    intro Hn.
    apply Z.bits_inj; intro n'.
    autorewrite with Ztestbit Ztestbit_full.
    break_innermost_match; Z.ltb_to_lt;
      repeat rewrite ?Bool.andb_false_l, ?Bool.andb_false_r, ?Bool.orb_false_l, ?Bool.orb_false_r, ?Bool.andb_true_l, ?Bool.andb_true_r, ?Z.sub_add, ?Bool.orb_diag;
      autorewrite with Ztestbit;
      try lia; reflexivity.
  Qed.

  Lemma add_shift_land_ones x n
    : 0 <= n -> x = ((x >> n) << n) + (Z.land x (Z.ones n)).
  Proof.
    pose proof (Z.ones_lt_pow2 n n).
    pose proof (Z.ones_nonneg n).
    intro Hn; etransitivity; [ eapply lor_shift_land_ones; eassumption | ].
    apply lor_shiftl'; [ assumption | ].
    rewrite Z.land_nonneg, Z.lt_le_pred.
    split.
    { right; now apply Z.ones_nonneg. }
    { rewrite Z.land_comm; etransitivity; [ apply Z.land_le | ]; lia. }
  Qed.
End Z.
