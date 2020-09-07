Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Notations.

Require Import Crypto.Util.ZUtil.Tactics.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.

Require Import Crypto.Util.Decidable.

Import Notations.

Local Open Scope Z_scope.

Module Z.
  Local Ltac destruct_ltb a b :=
    let E := fresh in
    destruct (a <? b) eqn:E; [rewrite Z.ltb_lt in E|rewrite Z.ltb_ge in E].
  Local Ltac destruct_leb a b :=
    let E := fresh in
    destruct (a <=? b) eqn:E; [rewrite Z.leb_le in E|rewrite Z.leb_gt in E].
  Local Ltac destruct_eqb a b :=
    let E := fresh in
    destruct (a =? b) eqn:E; [rewrite Z.eqb_eq in E|rewrite Z.eqb_neq in E].

  Lemma twos_complement_neg_equiv m a
    (Hm : 0 < m) :
    Z.twos_complement m a <? 0 = negb (a mod 2 ^ m <? 2 ^ (m - 1)).
  Proof.
    assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
    assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
    unfold Z.twos_complement. Z.ltb_to_lt; break_match; try discriminate; lia. Qed.

  Lemma twos_complement_cond_equiv m a
        (Hm : 0 < m) :
    (a mod 2 ^ m) <? 2 ^ (m - 1) = negb (Z.testbit a (m - 1)).
  Proof.
    pose proof Z.mod_pos_bound a (2 ^ m) ltac:(apply Z.pow_pos_nonneg;lia).
    destruct_ltb (a mod 2 ^ m) (2 ^ (m - 1)).
    rewrite <- (Z.mod_pow2_bits_low _ m) by lia.
    destruct (dec (a mod 2 ^ m = 0)) as [amod0|]; rewrite ?amod0, ?Z.bits_0, ?Z.bits_above_log2; try reflexivity.
    apply Z.mod_pos_bound; lia. apply Z.log2_lt_pow2; lia.
    rewrite <- (Z.mod_pow2_bits_low _ m),  Z.testbit_large by lia; reflexivity. Qed.

  Lemma twos_complement_spec m a b
    (Hm : 0 < m) :
    Z.twos_complement m a = b <-> a mod 2 ^ m = b mod 2 ^ m /\ - 2 ^ (m - 1) <= b < 2 ^ (m - 1).
  Proof.
    unfold Z.twos_complement.
    assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
    assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
    assert (2 ^ (m - 1) <= 2 ^ m) by (apply Z.pow_le_mono_r; lia).
    assert (2 * 2 ^ (m - 1) = 2 ^ m) by (rewrite Z.pow_mul_base by lia; apply f_equal2; lia).
    split; destruct_ltb (a mod 2 ^ m) (2 ^ (m - 1)); intros H4; subst; try split;
      repeat (pull_Zmod; push_Zmod; rewrite ?Z.mod_0_l, ?Z.sub_0_r); try lia.
    - destruct H4. rewrite H4 in *. rewrite Z.mod_small. lia.
      destruct (dec (b < 0)); [|lia]. pose proof Z.mod_neg_small b (2 ^ m) ltac:(nia).
      rewrite Z.mod_small in H6; lia.
    - destruct H4. rewrite H4 in *. rewrite Z.mod_neg_small. lia.
      destruct (dec (0 <= b)); [|lia]. rewrite Z.mod_small in H3; lia. Qed.

  Lemma twos_complement_testbit_spec_full m a i
        (Hm : 0 < m) :
    Z.testbit (Z.twos_complement m a) i = if (i <? m) then Z.testbit a i else Z.testbit a (m - 1).
  Proof. unfold Z.twos_complement.
         unfold Z.sub at 2.
         rewrite <- Z.lor_add by Z.solve_using_testbit.
         rewrite Z.twos_complement_cond_equiv by assumption.
         destruct (Z.testbit a (m - 1)); Z.solve_testbit. Qed.

  Hint Rewrite twos_complement_testbit_spec_full : testbit_pos_rewrite.
  Hint Rewrite twos_complement_testbit_spec_full : testbit_rewrite.

  Lemma twos_complement_one m (Hm : 1 < m) :
    Z.twos_complement m 1 = 1.
  Proof. Z.solve_using_testbit. Qed.

  Lemma twos_complement_zero m (Hm : 0 < m):
    Z.twos_complement m 0 = 0.
  Proof. Z.solve_using_testbit. Qed.

  Lemma twos_complement_mod a m (Hm : 0 < m) :
    Z.twos_complement m (a mod 2 ^ m) = Z.twos_complement m a.
  Proof. unfold Z.twos_complement; rewrite Z.mod_mod; try apply Z.pow_nonzero; lia. Qed.

  Lemma twos_complement_mod' a m (Hm : 0 < m) :
    Z.twos_complement m a mod 2 ^ m = a mod 2 ^ m.
  Proof. unfold Z.twos_complement.
         destruct_ltb (a mod 2 ^ m) (2 ^ (m - 1)); repeat (pull_Zmod; push_Zmod; rewrite Z.mod_0_l, Z.sub_0_r);
           try apply Z.mod_mod; apply Z.pow_nonzero; lia. Qed.

  Lemma twos_complement_odd m a (Hm : 0 < m) : Z.odd (Z.twos_complement m a) = Z.odd a.
  Proof. rewrite <- !Z.bit0_odd; Z.solve_testbit. Qed.

  Lemma twos_complement_mod2 m a (Hm : 0 < m) : Z.twos_complement m a mod 2 = a mod 2.
  Proof. rewrite Zmod_odd, twos_complement_odd, <- Zmod_odd by lia. reflexivity. Qed.

  Lemma twos_complement_bounds a m (Hm : 0 < m) :
    - 2 ^ (m - 1) <= Z.twos_complement m a < 2 ^ (m - 1).
  Proof.
    unfold Z.twos_complement.
    assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
    assert (2 ^ m = 2 * 2 ^ (m - 1)) by (rewrite Z.pow_mul_base by lia; apply f_equal2; lia).
    pose proof (Z.mod_pos_bound a (2 ^ m) H); destruct_ltb (a mod 2 ^ m) (2 ^ (m - 1)); lia. Qed.

  Hint Resolve twos_complement_bounds : zarith.

  Lemma twos_complement_add_full a b m
      (Hm : 0 < m)
      (Hsum : - 2 ^ (m - 1) <= Z.twos_complement m a + Z.twos_complement m b < 2 ^ (m - 1)) :
    Z.twos_complement m (a + b) = Z.twos_complement m a + Z.twos_complement m b.
  Proof.
    apply twos_complement_spec; try split; try lia; unfold Z.twos_complement.
    destruct_ltb (a mod 2 ^ m) (2 ^ (m - 1));
      destruct_ltb (b mod 2 ^ m) (2 ^ (m - 1)); repeat (push_Zmod; pull_Zmod; rewrite ?Z.sub_0_r); reflexivity. Qed.

  Lemma twos_complement_add_weak a b m
        (Hm : 0 < m)
        (Ha : - 2 ^ (m - 2) <= Z.twos_complement m a < 2 ^ (m - 2))
        (Hb : - 2 ^ (m - 2) <= Z.twos_complement m b < 2 ^ (m - 2)) :
    Z.twos_complement m (a + b) = Z.twos_complement m a + Z.twos_complement m b.
  Proof. destruct (dec (m = 1)); [subst; rewrite Z.pow_neg_r in *; lia|].
         assert (2 * 2 ^ (m - 2) = 2 ^ (m - 1)) by (rewrite Z.pow_mul_base by lia; apply f_equal2; lia).
         rewrite twos_complement_add_full; lia. Qed.

  Lemma twos_complement_mul_full m a b
        (Hm : 0 < m)
        (Hprod : - 2 ^ (m - 1) <= Z.twos_complement m a * Z.twos_complement m b < 2 ^ (m - 1)) :
    Z.twos_complement m (a * b) = Z.twos_complement m a * Z.twos_complement m b.
  Proof.
    apply twos_complement_spec; try split; try lia; unfold Z.twos_complement.
    destruct_ltb (a mod 2 ^ m) (2 ^ (m - 1));
      destruct_ltb (b mod 2 ^ m) (2 ^ (m - 1)); repeat (push_Zmod; pull_Zmod; rewrite ?Z.sub_0_r); reflexivity. Qed.
End Z.
