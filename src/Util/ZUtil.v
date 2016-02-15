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

Lemma mod_exp_0 : forall a x m, x > 0 -> m > 1 -> a mod m = 0 ->
  a ^ x mod m = 0.
Proof.
  intros.
  replace x with (Z.of_nat (Z.to_nat x)) in * by (apply Z2Nat.id; omega).
  induction (Z.to_nat x). {
    simpl in *; omega.
  } {
    rewrite Nat2Z.inj_succ in *.
    rewrite Z.pow_succ_r by omega.
    rewrite Z.mul_mod by omega.
    case_eq n; intros. {
      subst. simpl.
      rewrite Zmod_1_l by omega.
      rewrite H1.
      apply Zmod_0_l.
    } {
      subst.
      rewrite IHn by (rewrite Nat2Z.inj_succ in *; omega).
      rewrite H1.
      auto.
    }
  }
Qed.

Lemma mod_pow : forall (a m b : Z), (0 <= b) -> (m <> 0) ->
    a ^ b mod m = (a mod m) ^ b mod m.
Proof.
  intros; rewrite <- (Z2Nat.id b) by auto.
  induction (Z.to_nat b); auto.
  rewrite Nat2Z.inj_succ.
  do 2 rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
  rewrite Z.mul_mod by auto.
  rewrite (Z.mul_mod (a mod m) ((a mod m) ^ Z.of_nat n) m) by auto.
  rewrite <- IHn by auto.
  rewrite Z.mod_mod by auto.
  reflexivity.
Qed.

Ltac Zdivide_exists_mul := let k := fresh "k" in
match goal with
| [ H : (?a | ?b) |- _ ] => apply Z.mod_divide in H; try apply Zmod_divides in H; destruct H as [k H]
| [ |- (?a | ?b) ] => apply Z.mod_divide; try apply Zmod_divides
end; (omega || auto).

Lemma divide_mul_div: forall a b c (a_nonzero : a <> 0) (c_nonzero : c <> 0),
  (a | b * (a / c)) -> (c | a) -> (c | b).
Proof.
  intros ? ? ? ? ? divide_a divide_c_a; do 2 Zdivide_exists_mul.
  rewrite divide_c_a in divide_a.
  rewrite Z_div_mul' in divide_a by auto.
  replace (b * k) with (k * b) in divide_a by ring.
  replace (c * k * k0) with (k * (k0 * c)) in divide_a by ring.
  rewrite Z.mul_cancel_l in divide_a by (intuition; rewrite H in divide_c_a; ring_simplify in divide_a; intuition).
  eapply Zdivide_intro; eauto.
Qed.

Lemma divide2_even_iff : forall n, (2 | n) <-> Z.even n = true.
Proof.
  intro; split. {
    intro divide2_n.
    Zdivide_exists_mul; [ | pose proof (Z.mod_pos_bound n 2); omega].
    rewrite divide2_n.
    apply Z.even_mul.
  } {
    intro n_even.
    pose proof (Zmod_even n).
    rewrite n_even in H.
    apply Zmod_divide; omega || auto.
  }
Qed.

Lemma prime_odd_or_2 : forall p (prime_p : prime p), p = 2 \/ Z.odd p = true.
Proof.
  intros.
  apply Decidable.imp_not_l; try apply Z.eq_decidable.
  intros p_neq2.
  pose proof (Zmod_odd p) as mod_odd.
  destruct (Sumbool.sumbool_of_bool (Z.odd p)) as [? | p_not_odd]; auto.
  rewrite p_not_odd in mod_odd.
  apply Zmod_divides in mod_odd; try omega.
  destruct mod_odd as [c c_id].
  rewrite Z.mul_comm in c_id.
  apply Zdivide_intro in c_id.
  apply prime_divisors in c_id; auto.
  destruct c_id; [omega | destruct H; [omega | destruct H; auto]].
  pose proof (prime_ge_2 p prime_p); omega.
Qed.

Lemma mul_div_eq : (forall a m, m > 0 -> m * (a / m) = (a - a mod m))%Z.
Proof.
  intros.
  rewrite (Z_div_mod_eq a m) at 2 by auto.
  ring.
Qed.

Ltac prime_bound := match goal with
| [ H : prime ?p |- _ ] => pose proof (prime_ge_2 p H); try omega
end.

Lemma Zlt_minus_lt_0 : forall n m, m < n -> 0 < n - m.
Proof.
  intros; omega.
Qed.

(* prove that known nonnegative numbers are nonnegative *)
Ltac zero_bounds' :=
  repeat match goal with
  | [ |- 0 <= _ + _] => apply Z.add_nonneg_nonneg
  | [ |- 0 <= _ - _] => apply Zle_minus_le_0
  | [ |- 0 <= _ * _] => apply Z.mul_nonneg_nonneg
  | [ |- 0 <= _ / _] => apply Z.div_pos
  | [ |- 0 < _ + _] => apply Z.add_pos_nonneg
  (* TODO : this apply is not good: it can make a true goal false. Actually,
  * we would want this tactic to explore two branches:
  * - apply Z.add_pos_nonneg and continue
  * - apply Z.add_nonneg_pos and continue
  * Keep whichever one solves all subgoals. If neither does, don't apply. *)

  | [ |- 0 < _ - _] => apply Zlt_minus_lt_0
  | [ |- 0 < _ * _] => apply Z.lt_0_mul; left; split
  | [ |- 0 < _ / _] => apply Z.div_str_pos
  end; try omega; try prime_bound; auto.

Ltac zero_bounds := try omega; try prime_bound; zero_bounds'.
