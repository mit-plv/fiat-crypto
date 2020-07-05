Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Testbit.
Local Open Scope bool_scope. Local Open Scope Z_scope.

Module Z.
  Lemma land_same_r : forall a b, (a &' b) &' b = a &' b.
  Proof.
    intros a b; apply Z.bits_inj'; intros n H.
    rewrite !Z.land_spec.
    case_eq (Z.testbit b n); intros;
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
  Qed.

  Lemma land_m1'_l a : Z.land (-1) a = a.
  Proof. apply Z.land_m1_l. Qed.
  Hint Rewrite Z.land_m1_l land_m1'_l : zsimplify_const zsimplify zsimplify_fast.

  Lemma land_m1'_r a : Z.land a (-1) = a.
  Proof. apply Z.land_m1_r. Qed.
  Hint Rewrite Z.land_m1_r land_m1'_r : zsimplify_const zsimplify zsimplify_fast.

  Lemma sub_1_lt_le x y : (x - 1 < y) <-> (x <= y).
  Proof. lia. Qed.

  Lemma land_mod a b :
    0 <= b ->
    a &' b = (a mod (2 ^ (Z.log2 b + 1))) &' b.
  Proof.
    pose proof (Z.log2_nonneg b).
    intros. rewrite <-Z.land_ones by lia.
    rewrite <-Z.land_assoc, (Z.land_comm (Z.ones _)).
    rewrite Z.land_ones_low; auto with zarith.
  Qed.

  Lemma land_add_high a b c d :
    Z.log2 d < c ->
    0 <= d ->
    (a + b * 2 ^ c) &' d = a &' d.
  Proof.
    pose proof (Z.log2_nonneg d).
    intros. rewrite land_mod by lia.
    rewrite Z.add_mod, Z.mul_mod by (apply Z.pow_nonzero; lia).
    match goal with
    | |- context [?a ^ ?b mod ?a ^ ?c] =>
      replace b with ((b - c) + c) by lia;
        rewrite (Z.pow_add_r a (b - c) c) by lia;
        rewrite Z.mod_mul by (apply Z.pow_nonzero; lia)
    end.
    rewrite Z.mul_0_r, Z.mod_0_l, Z.add_0_r, Z.mod_mod
      by (apply Z.pow_nonzero; lia).
    rewrite <-Z.land_ones, <-Z.land_assoc, (Z.land_comm (Z.ones _))
      by auto with zarith.
    rewrite Z.land_ones_low; auto with zarith.
  Qed.

  Lemma land_pow2 x n :
    0 <= n ->
    Z.land x (2^n-1) = x mod 2^n.
  Proof.
    intros. rewrite Z.sub_1_r, <- Z.ones_equiv.
    apply Z.land_ones; auto with zarith.
  Qed.
  
  Lemma land_pow2_testbit a b :
  a &' 2^b = if Z.testbit a b then 2^b else 0.
  Proof.
    apply Z.bits_inj_iff; red; intros; rewrite Z.land_spec.
    destruct (Z.testbit a b) eqn:E.
    - destruct (Z.eqb_spec b n); subst.
      + now rewrite E, andb_true_l.
      + now rewrite Z.pow2_bits_false, andb_false_r.
    - rewrite Z.testbit_0_l; destruct (Z.eqb_spec b n); subst.
      + now rewrite E, andb_false_l.
      + now rewrite Z.pow2_bits_false, andb_false_r. Qed.

  Lemma land_pow2_small a b
        (Ha : 0 <= a < 2^b) :
    a &' 2^b = 0.
  Proof. now rewrite land_pow2_testbit, Testbit.Z.bits_above_pow2. Qed.

  Lemma land_pow2_small_neg a b
        (Ha : - 2^b <= a < 0)
        (Hb : 0 < b) :
    a &' 2^b = 2^b.
  Proof. now rewrite land_pow2_testbit, Testbit.Z.testbit_small_neg. Qed.

  Lemma land_div2 a b (Ha : 0 <= a < 2^(b + 1))  :
    a / 2 &' 2^b = 0.
  Proof.
    destruct (Z.ltb_spec b 0).
    - now rewrite Pow.Z.base_pow_neg, Z.land_0_r.
    - rewrite land_pow2_testbit, Z.div2_bits, Testbit.Z.bits_above_pow2; 
      try (replace (Z.succ b) with (b + 1); nia). Qed.
End Z.
