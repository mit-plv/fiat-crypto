Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ListUtil.
Local Open Scope Z_scope.

Module Z.
  Lemma base_pow_neg b n : n < 0 -> b^n = 0.
  Proof.
    destruct n; intro H; try reflexivity; compute in H; congruence.
  Qed.
  Hint Rewrite base_pow_neg using zutil_arith : zsimplify.

  Lemma nonneg_pow_pos a b : 0 < a -> 0 < a^b -> 0 <= b.
  Proof.
    destruct (Z_lt_le_dec b 0); intros; auto.
    erewrite Z.pow_neg_r in * by eassumption.
    lia.
  Qed.
  Hint Resolve nonneg_pow_pos (fun n => nonneg_pow_pos 2 n Z.lt_0_2) : zarith.
  Lemma nonneg_pow_pos_helper a b dummy : 0 < a -> 0 <= dummy < a^b -> 0 <= b.
  Proof. eauto with zarith lia. Qed.
  Hint Resolve nonneg_pow_pos_helper (fun n dummy => nonneg_pow_pos_helper 2 n dummy Z.lt_0_2) : zarith.

  Lemma div_pow2succ : forall n x, (0 <= x) ->
    n / 2 ^ Z.succ x = Z.div2 (n / 2 ^ x).
  Proof.
    intros.
    rewrite Z.pow_succ_r, Z.mul_comm by auto.
    rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
    rewrite Zdiv2_div.
    reflexivity.
  Qed.

  Definition pow_sub_r'
    := fun a b c y H0 H1 => @Logic.eq_trans _ _ _ y (@Z.pow_sub_r a b c H0 H1).
  Definition pow_sub_r'_sym
    := fun a b c y p H0 H1 => Logic.eq_sym (@Logic.eq_trans _ y _ _ (Logic.eq_sym p) (@Z.pow_sub_r a b c H0 H1)).
  Hint Resolve pow_sub_r' pow_sub_r'_sym Z.eq_le_incl : zarith.
  Hint Resolve (fun b => f_equal (fun e => b ^ e)) (fun e => f_equal (fun b => b ^ e)) : zarith.

  Lemma two_p_two_eq_four : 2^(2) = 4.
  Proof. reflexivity. Qed.
  Hint Rewrite <- two_p_two_eq_four : push_Zpow.

  Lemma pow_pos_le a b : 0 < a -> 0 < b -> a <= a ^ b.
  Proof.
    intros; transitivity (a ^ 1).
    { rewrite Z.pow_1_r; reflexivity. }
    { apply Z.pow_le_mono; auto with zarith. }
  Qed.
  Hint Resolve pow_pos_le : zarith.

  Lemma pow_pos_lt a b : 1 < a -> 1 < b -> a < a ^ b.
  Proof.
    intros; eapply Z.le_lt_trans with (m:=a ^ 1).
    { rewrite Z.pow_1_r; reflexivity. }
    { apply Z.pow_lt_mono_r; auto with zarith. }
  Qed.
  Hint Resolve pow_pos_lt : zarith.

  Lemma pow_div_base a b : a <> 0 -> 0 < b -> a ^ b / a = a ^ (b - 1).
  Proof. intros; rewrite Z.pow_sub_r, Z.pow_1_r; lia. Qed.
  Hint Rewrite pow_div_base using zutil_arith : pull_Zpow.

  Lemma pow_mul_base a b : 0 <= b -> a * a ^ b = a ^ (b + 1).
  Proof. intros; rewrite <-Z.pow_succ_r, <-Z.add_1_r by lia; reflexivity. Qed.
  Hint Rewrite pow_mul_base using zutil_arith : pull_Zpow.
End Z.
