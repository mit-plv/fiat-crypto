Require Import Coq.Numbers.Natural.Peano.NPeano Coq.omega.Omega.

Local Open Scope nat_scope.

Lemma div_minus : forall a b, b <> 0 -> (a + b) / b = a / b + 1.
Proof.
  intros.
  assert (b = 1 * b) by omega.
  rewrite H0 at 1.
  rewrite <- Nat.div_add by auto.
  reflexivity.
Qed.

Lemma divide2_1mod4_nat : forall c x, c = x / 4 -> x mod 4 = 1 -> exists y, 2 * y = (x / 2).
Proof.
  assert (4 <> 0) as ne40 by omega.
  induction c; intros; pose proof (div_mod x 4 ne40); rewrite <- H in H1. {
    rewrite H0 in H1.
    simpl in H1.
    rewrite H1.
    exists 0; auto.
  } {
    rewrite mult_succ_r in H1.
    assert (4 <= x) as le4x by (apply Nat.div_str_pos_iff; omega).
    rewrite <- Nat.add_1_r in H.
    replace x with ((x - 4) + 4) in H by omega.
    rewrite div_minus in H by auto.
    apply Nat.add_cancel_r in H.
    replace x with ((x - 4) + (1 * 4)) in H0 by omega.
    rewrite Nat.mod_add in H0 by auto.
    pose proof (IHc _ H H0).
    destruct H2.
    exists (x0 + 1).
    rewrite <- (Nat.sub_add 4 x) in H1 at 1 by auto.
    replace (4 * c + 4 + x mod 4) with (4 * c + x mod 4 + 4) in H1 by omega.
    apply Nat.add_cancel_r in H1.
    replace (2 * (x0 + 1)) with (2 * x0 + 2)
      by (rewrite Nat.mul_add_distr_l; auto).
    rewrite H2.
    rewrite <- Nat.div_add by omega.
    f_equal.
    simpl.
    apply Nat.sub_add; auto.
  }
Qed.

Lemma Nat2N_inj_lt : forall n m, (N.of_nat n < N.of_nat m)%N <-> n < m.
Proof.
  split; intros. {
    rewrite nat_compare_lt.
    rewrite Nnat.Nat2N.inj_compare.
    rewrite N.compare_lt_iff; auto.
  } {
    rewrite <- N.compare_lt_iff.
    rewrite <- Nnat.Nat2N.inj_compare.
    rewrite <- nat_compare_lt; auto.
  }
Qed.

Lemma lt_min_l : forall x a b, (x < min a b)%nat -> (x < a)%nat.
Proof.
  intros ? ? ? lt_min.
  apply Nat.min_glb_lt_iff in lt_min.
  destruct lt_min; assumption.
Qed.

(* useful for hints *)
Lemma eq_le_incl_rev : forall a b, a = b -> b <= a.
Proof.
  intros; omega.
Qed.

Lemma beq_nat_eq_nat_dec {R} (x y : nat) (a b : R)
  : (if EqNat.beq_nat x y then a else b) = (if eq_nat_dec x y then a else b).
Proof.
  destruct (eq_nat_dec x y) as [H|H];
    [ rewrite (proj2 (@beq_nat_true_iff _ _) H); reflexivity
    | rewrite (proj2 (@beq_nat_false_iff _ _) H); reflexivity ].
Qed.

