Require Import Zpower Znumtheory ZArith.ZArith ZArith.Zdiv.
Require Import Omega NPeano Arith.
Require Import Crypto.Util.NatUtil.
Require Import Bedrock.Word.
Local Open Scope Z.

Lemma gt_lt_symmetry: forall n m, n > m <-> m < n.
Proof.
  intros; split; omega.
Qed.

Lemma positive_is_nonzero : forall x, x > 0 -> x <> 0.
Proof.
  intros; omega.
Qed.
Hint Resolve positive_is_nonzero.

Lemma div_positive_gt_0 : forall a b, a > 0 -> b > 0 -> a mod b = 0 ->
  a / b > 0.
Proof.
  intros; rewrite gt_lt_symmetry.
  apply Z.div_str_pos.
  split; intuition.
  apply Z.divide_pos_le; try (apply Zmod_divide); omega.
Qed.

Lemma elim_mod : forall a b m, a = b -> a mod m = b mod m.
Proof.
  intros; subst; auto.
Qed.
Hint Resolve elim_mod.

Lemma mod_mult_plus: forall a b c, (b <> 0) -> (a * b + c) mod b = c mod b.
Proof.
  intros.
  rewrite Zplus_mod.
  rewrite Z.mod_mul; auto; simpl.
  rewrite Zmod_mod; auto.
Qed.

Lemma pos_pow_nat_pos : forall x n, 
  Z.pos x ^ Z.of_nat n > 0.
  do 2 (intros; induction n; subst; simpl in *; auto with zarith).
  rewrite <- Pos.add_1_r, Zpower_pos_is_exp.
  apply Zmult_gt_0_compat; auto; reflexivity.
Qed.

Lemma Z_div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  intros. rewrite Z.mul_comm. apply Z.div_mul; auto.
Qed.

Lemma Zgt0_neq0 : forall x, x > 0 -> x <> 0.
  intuition.
Qed.

Lemma Zpow_pow2 : forall n, (pow2 n)%nat = Z.to_nat (2 ^ (Z.of_nat n)).
Proof.
  induction n; intros; auto.
  simpl pow2.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by apply Zle_0_nat.
  rewrite untimes2.
  rewrite Z2Nat.inj_mul by (try apply Z.pow_nonneg; omega).
  rewrite <- IHn.
  auto.
Qed.
