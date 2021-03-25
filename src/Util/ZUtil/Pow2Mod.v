Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.Ztestbit.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Module Z.
  Lemma pow2_mod_spec : forall a b, (0 <= b) -> Z.pow2_mod a b = a mod (2 ^ b).
  Proof.
    intros.
    unfold Z.pow2_mod.
    rewrite Z.land_ones; auto.
  Qed.
  Hint Rewrite <- Z.pow2_mod_spec using zutil_arith : convert_to_Ztestbit.

  Lemma pow2_mod_0_r : forall a, Z.pow2_mod a 0 = 0.
  Proof.
    intros; rewrite Z.pow2_mod_spec, Z.mod_1_r; reflexivity.
  Qed.

  Lemma pow2_mod_0_l : forall n, 0 <= n -> Z.pow2_mod 0 n = 0.
  Proof.
    intros; rewrite Z.pow2_mod_spec, Z.mod_0_l; try reflexivity; try apply Z.pow_nonzero; lia.
  Qed.

  Lemma pow2_mod_split : forall a n m, 0 <= n -> 0 <= m ->
                                       Z.pow2_mod a (n + m) = Z.lor (Z.pow2_mod a n) ((Z.pow2_mod (a >> n) m) << n).
  Proof.
    intros; cbv [Z.pow2_mod].
    apply Z.bits_inj'; intros.
    repeat progress (try break_match; autorewrite with Ztestbit zsimplify; try reflexivity).
    try match goal with H : ?a < ?b |- context[Z.testbit _ (?a - ?b)] =>
      rewrite !Z.testbit_neg_r with (n := a - b) by lia end.
    autorewrite with Ztestbit; reflexivity.
  Qed.

  Lemma pow2_mod_pow2_mod : forall a n m, 0 <= n -> 0 <= m ->
                                          Z.pow2_mod (Z.pow2_mod a n) m = Z.pow2_mod a (Z.min n m).
  Proof.
    intros; cbv [Z.pow2_mod].
    apply Z.bits_inj'; intros.
    apply Z.min_case_strong; intros; repeat progress (try break_match; autorewrite with Ztestbit zsimplify; try reflexivity).
  Qed.

  Lemma pow2_mod_pos_bound a b : 0 < b -> 0 <= Z.pow2_mod a b < 2^b.
  Proof.
    intros; rewrite Z.pow2_mod_spec by lia.
    auto with zarith.
  Qed.
  Hint Resolve pow2_mod_pos_bound : zarith.

  Lemma pow2_mod_id_iff : forall a n, 0 <= n ->
                                      (Z.pow2_mod a n = a <-> 0 <= a < 2 ^ n).
  Proof.
    intros a n H.
    rewrite Z.pow2_mod_spec by assumption.
    assert (0 < 2 ^ n) by Z.zero_bounds.
    rewrite Z.mod_small_iff by lia.
    split; intros; intuition lia.
  Qed.
End Z.
