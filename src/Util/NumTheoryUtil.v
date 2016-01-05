Require Import Zpower Znumtheory ZArith.ZArith ZArith.Zdiv.
Require Import Omega NPeano Arith.
Require Import Crypto.Util.NatUtil Crypto.Util.ZUtil.
Local Open Scope Z.

Lemma euler_criterion : forall (a x p : Z) (prime_p : prime p),
  (x * 2 + 1 = p)%Z -> (a ^ x mod p = 1)%Z ->
    exists b : Z, (0 <= b < p /\ b * b mod p = a)%Z.
Admitted.

Lemma divide2_1mod4 : forall x, x mod 4 = 1 -> 0 <= x -> (2 | x / 2).
Proof.
  intros.
  assert (Z.to_nat x mod 4 = 1)%nat. {
    replace 1%Z with (Z.of_nat 1) in H by auto.
    replace (x mod 4)%Z with (Z.of_nat (Z.to_nat x mod 4)) in H
      by (rewrite mod_Zmod by omega; rewrite Z2Nat.id; auto).
    apply Nat2Z.inj in H; auto.
  }
  remember (Z.to_nat x / 4)%nat as c.
  pose proof (divide2_1mod4_nat c (Z.to_nat x) Heqc H1).
  destruct H2.
  replace 2%nat with (Z.to_nat 2) in H2 by auto.
  apply inj_eq in H2.
  rewrite div_Zdiv in H2 by (replace (Z.to_nat 2) with 2%nat by auto; omega).
  rewrite Nat2Z.inj_mul in H2.
  do 2 rewrite Z2Nat.id in H2 by (auto || omega).
  rewrite Z.mul_comm in H2.
  symmetry in H2.
  apply Zdivide_intro in H2; auto.
Qed.

Lemma minus1_even_pow : forall x y, (2 | y) -> (1 < x) -> (0 <= y) -> ((x - 1) ^ y mod x = 1).
Proof.
  intros.
  apply Zdivide_Zdiv_eq in H; try omega.
  rewrite H.
  rewrite Z.pow_mul_r by omega.
  assert ((x - 1)^2 mod x = 1). {
    replace ((x - 1)^2) with (x ^ 2 - 2 * x + 1)
      by (do 2 rewrite Z.pow_2_r; rewrite Z.mul_sub_distr_l; do 2 rewrite Z.mul_sub_distr_r; omega).
    rewrite Zplus_mod.
    rewrite Z.pow_2_r.
    rewrite <- Z.mul_sub_distr_r.
    rewrite Z_mod_mult.
    do 2 rewrite Zmod_1_l by auto; auto.
  }
  rewrite <- (Z2Nat.id (y / 2)) by omega.
  induction (Z.to_nat (y / 2)); try apply Zmod_1_l; auto.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by apply Zle_0_nat.
  rewrite Zmult_mod.
  rewrite IHn.
  rewrite H2.
  simpl.
  apply Zmod_1_l; auto.
Qed.

Lemma minus1_square_1mod4 : forall (p : Z) (prime_p : prime p),
  (p mod 4 = 1)%Z -> exists b : Z, (0 <= b < p /\ b * b mod p = p - 1)%Z.
Proof.
  intros.
  assert (4 <> 0)%Z by omega.
  pose proof (Z.div_mod p 4 H0).
  pose proof (prime_ge_2 p (prime_p)).
  assert (2 | p / 2)%Z by (apply divide2_1mod4; (auto || omega)).
  apply (euler_criterion (p - 1) (p / 2) p prime_p);
    [ | apply minus1_even_pow; (omega || auto); apply Z_div_pos; omega].
  rewrite <- H.
  rewrite H1 at 3.
  f_equal.
  replace 4%Z with (2 * 2)%Z by auto.
  rewrite <- Z.div_div by omega.
  rewrite <- Zdivide_Zdiv_eq_2 by (auto || omega).
  replace (2 * 2 * (p / 2) / 2)%Z with (2 * (2 * (p / 2)) / 2)%Z
    by (f_equal; apply Z.mul_assoc).
  rewrite ZUtil.Z_div_mul' by omega.
  rewrite Z.mul_comm.
  auto.
Qed.

