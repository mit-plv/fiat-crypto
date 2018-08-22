Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
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
    omega.
  Qed.
  Hint Resolve nonneg_pow_pos (fun n => nonneg_pow_pos 2 n Z.lt_0_2) : zarith.
  Lemma nonneg_pow_pos_helper a b dummy : 0 < a -> 0 <= dummy < a^b -> 0 <= b.
  Proof. eauto with zarith omega. Qed.
  Hint Resolve nonneg_pow_pos_helper (fun n dummy => nonneg_pow_pos_helper 2 n dummy Z.lt_0_2) : zarith.

  Lemma div_pow2succ : forall n x, (0 <= x) ->
    n / 2 ^ Z.succ x = Z.div2 (n / 2 ^ x).
  Proof.
    intros.
    rewrite Z.pow_succ_r, Z.mul_comm by auto.
    rewrite <- Z.div_div by (try apply Z.pow_nonzero; omega).
    rewrite Zdiv2_div.
    reflexivity.
  Qed.
End Z.
