Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.TwosComplement.

Require Import Crypto.Util.ZUtil.Tactics.SolveRange.

Import Notations.

Local Open Scope Z_scope.

Module Z.
  Lemma sign_bit_0_land_pow2 a m :
    Z.sign_bit m a = 0 -> a &' 2 ^ (m - 1) = 0.
  Proof.
    intros H; apply Z.shiftr_eq_0_iff in H; destruct H as [? |[? ?] ]; subst.
    - rewrite Z.land_0_l; reflexivity.
    - rewrite Z.land_pow2_testbit, Z.bits_above_log2; lia. Qed.

  Lemma sign_bit_testbit a m
        (Hm : 0 < m)
        (H : 0 <= a < 2 ^ m) :
    Z.sign_bit m a = Z.b2z (Z.testbit a (m - 1)).
  Proof.
    rewrite Z.testbit_spec', Z.mod_small, <- Z.shiftr_div_pow2 by Z.solve_range.
    reflexivity. Qed.

  Lemma sign_bit_equiv a m
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m) :
    Z.sign_bit m a = Z.b2z (negb (a <? 2 ^ (m - 1))).
  Proof. rewrite <- (Z.mod_small _ _ Ha) at 2.
         rewrite Z.twos_complement_cond_equiv, sign_bit_testbit, negb_involutive; lia. Qed.

  Lemma sign_bit_1_land_pow2 a m
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m) :
    Z.sign_bit m a <> 0 -> a &' 2 ^ (m - 1) = 2 ^ (m - 1).
  Proof.
    intros H. rewrite Z.land_pow2_testbit, Z.testbit_b2z, <- sign_bit_testbit by assumption.
    apply Z.eqb_neq in H; rewrite H; reflexivity. Qed.

  Lemma sign_bit_0_testbit a m
        (Hm : 0 < m) :
    Z.sign_bit m a = 0 -> Z.testbit a (m - 1) = false.
  Proof.
    assert (Hnz : 2 ^ (m - 1) <> 0) by (apply Z.pow_nonzero; lia).
    intro H; apply sign_bit_0_land_pow2 in H. rewrite Z.land_pow2_testbit in H;
                                                destruct (Z.testbit a (m - 1));
                                                [contradiction|reflexivity]. Qed.

  Lemma sign_bit_1_testbit a m
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m) :
    Z.sign_bit m a <> 0 -> Z.testbit a (m - 1) = true.
  Proof.
    rewrite Z.testbit_b2z, <- sign_bit_testbit by lia; intro H.
    apply Z.eqb_neq in H; rewrite H; reflexivity. Qed.
End Z.
