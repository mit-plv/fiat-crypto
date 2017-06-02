
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(************************************************************************

    Definition of the Euler Totient function

*************************************************************************)
Require Import ZArith.
Require Export Znumtheory.
Require Import Tactic.
Require Export ZSum.

Open Scope Z_scope.

Definition phi n := Zsum 1 (n - 1) (fun x => if rel_prime_dec x n then 1 else 0).

Theorem phi_def_with_0:
  forall n, 1< n -> phi n = Zsum 0 (n - 1) (fun x => if rel_prime_dec x n then 1 else 0).
intros n H; rewrite Zsum_S_left; auto with zarith.
case (rel_prime_dec 0 n); intros H2.
contradict H2; apply not_rel_prime_0; auto.
rewrite Zplus_0_l; auto.
Qed.

Theorem phi_pos: forall n, 1 < n -> 0 < phi n.
intros n H; unfold phi.
case (Zle_lt_or_eq 2 n); auto with zarith; intros H1; subst.
rewrite Zsum_S_left; simpl; auto with zarith.
case (rel_prime_dec 1 n); intros H2.
apply Zlt_le_trans with (1 + 0); auto with zarith.
apply Zplus_le_compat_l.
pattern 0 at 1; replace 0 with  ((1 + (n - 1) - 2) * 0); auto with zarith.
rewrite <- Zsum_c; auto with zarith.
apply Zsum_le; auto with zarith.
intros x H3;  case (rel_prime_dec x n); auto with zarith.
case H2; apply rel_prime_1; auto with zarith.
rewrite Zsum_nn.
case (rel_prime_dec (2 - 1) 2); auto with zarith.
intros H1; contradict H1; apply rel_prime_1; auto with zarith.
Qed.

Theorem phi_le_n_minus_1: forall n, 1 < n -> phi n <= n - 1.
intros n H; replace (n-1) with ((1 +  (n - 1) - 1) * 1); auto with zarith.
rewrite <- Zsum_c; auto with zarith.
unfold phi; apply Zsum_le; auto with zarith.
intros x H1; case (rel_prime_dec x n); auto with zarith.
Qed.

Theorem prime_phi_n_minus_1: forall n, prime n -> phi n = n - 1.
intros n H; replace (n-1) with ((1 +  (n - 1) - 1) * 1); auto with zarith.
assert (Hu: 1 <= n - 1).
assert (2 <= n); auto with zarith.
apply prime_ge_2; auto.
rewrite <- Zsum_c; auto with zarith; unfold phi; apply Zsum_ext; auto.
intros x  (H2, H3); case H; clear H; intros H H1.
generalize (H1 x); case (rel_prime_dec x n); auto with zarith.
intros H6 H7; contradict H6; apply H7; split; auto with zarith.
Qed.

Theorem phi_n_minus_1_prime: forall n, 1 < n -> phi n = n - 1 -> prime n.
intros n H H1; case (prime_dec n); auto; intros H2.
assert (H3: phi n < n - 1); auto with zarith.
replace (n-1) with ((1 +  (n - 1) - 1) * 1); auto with zarith.
assert (Hu: 1 <= n - 1); auto with zarith.
rewrite <- Zsum_c; auto with zarith; unfold phi; apply Zsum_lt; auto.
intros x _; case (rel_prime_dec x n); auto with zarith.
case not_prime_divide with n; auto.
intros x (H3, H4); exists x; repeat split; auto with zarith.
case (rel_prime_dec x n); auto with zarith.
intros H5; absurd (x = 1 \/ x = -1); auto with zarith.
case (Zis_gcd_unique  x n x 1); auto.
apply Zis_gcd_intro; auto; exists 1; auto with zarith.
contradict H3; rewrite H1; auto with zarith.
Qed.

Theorem phi_divide_prime: forall n, 1 < n -> (n - 1 | phi n) -> prime n.
intros n H1 H2; apply  phi_n_minus_1_prime; auto.
apply Zle_antisym.
apply phi_le_n_minus_1; auto.
apply Zdivide_le; auto; auto with zarith.
apply phi_pos; auto.
Qed.
