Require Coq.Logic.Eqdep_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.omega.Omega.
Require Import Coq.micromega.Psatz.
Import Nat.

Create HintDb natsimplify discriminated.

Hint Resolve mod_bound_pos : arith.
Hint Resolve (fun x y p q => proj1 (@Nat.mod_bound_pos x y p q)) (fun x y p q => proj2 (@Nat.mod_bound_pos x y p q)) : arith.

Hint Rewrite @mod_small @mod_mod @mod_1_l @mod_1_r succ_pred using omega : natsimplify.

Local Open Scope nat_scope.

Lemma min_def {x y} : min x y = x - (x - y).
Proof. apply Min.min_case_strong; omega. Qed.
Lemma max_def {x y} : max x y = x + (y - x).
Proof. apply Max.max_case_strong; omega. Qed.
Ltac coq_omega := omega.
Ltac handle_min_max_for_omega_gen min max :=
  repeat match goal with
         | [ H : context[min _ _] |- _ ] => rewrite !min_def in H || setoid_rewrite min_def in H
         | [ H : context[max _ _] |- _ ] => rewrite !max_def in H || setoid_rewrite max_def in H
         | [ |- context[min _ _] ] => rewrite !min_def || setoid_rewrite min_def
         | [ |- context[max _ _] ] => rewrite !max_def || setoid_rewrite max_def
         end.
Ltac handle_min_max_for_omega_case_gen min max :=
  repeat match goal with
         | [ H : context[min _ _] |- _ ] => revert H
         | [ H : context[max _ _] |- _ ] => revert H
         | [ |- context[min _ _] ] => apply Min.min_case_strong
         | [ |- context[max _ _] ] => apply Max.max_case_strong
         end;
  intros.
Ltac handle_min_max_for_omega := handle_min_max_for_omega_gen min max.
Ltac handle_min_max_for_omega_case := handle_min_max_for_omega_case_gen min max.
(* In 8.4, Nat.min is a definition, so we need to unfold it *)
Ltac handle_min_max_for_omega_compat_84 :=
  let min := (eval cbv [min] in min) in
  let max := (eval cbv [max] in max) in
  handle_min_max_for_omega_gen min max.
Ltac handle_min_max_for_omega_case_compat_84 :=
  let min := (eval cbv [min] in min) in
  let max := (eval cbv [max] in max) in
  handle_min_max_for_omega_case_gen min max.
Ltac omega_with_min_max :=
  handle_min_max_for_omega;
  try handle_min_max_for_omega_compat_84;
  omega.
Ltac omega_with_min_max_case :=
  handle_min_max_for_omega_case;
  try handle_min_max_for_omega_case_compat_84;
  omega.
Tactic Notation "omega" := coq_omega.
Tactic Notation "omega" "*" := omega_with_min_max_case.
Tactic Notation "omega" "**" := omega_with_min_max.

Lemma div_minus : forall a b, b <> 0 -> (a + b) / b = a / b + 1.
Proof.
  intros.
  assert (b = 1 * b) by omega.
  rewrite H0 at 1.
  rewrite <- Nat.div_add by auto.
  reflexivity.
Qed.

Lemma div_add_l' : forall a b c, a <> 0 -> (a * b + c) / a = b + c / a.
Proof.
  intros; rewrite Nat.mul_comm; auto using div_add_l.
Qed.

Lemma mod_add_l : forall a b c, b <> 0 -> (a * b + c) mod b = c mod b.
Proof.
  intros; rewrite Nat.add_comm; auto using mod_add.
Qed.

Lemma mod_add_l' : forall a b c, b <> 0 -> (b * a + c) mod b = c mod b.
Proof.
  intros; rewrite Nat.mul_comm; auto using mod_add_l.
Qed.

Lemma mod_div_eq0 : forall a b, b <> 0 -> a mod b / b = 0.
Proof.
  intros; apply Nat.div_small, mod_bound_pos; omega.
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

Lemma pow_nonzero a k : a <> 0 -> a ^ k <> 0.
Proof.
  intro; induction k; simpl; nia.
Qed.

Hint Resolve pow_nonzero : arith.

Lemma S_pred_nonzero : forall a, (a > 0 -> S (pred a) = a)%nat.
Proof.
  destruct a; simpl; omega.
Qed.

Hint Rewrite S_pred_nonzero using omega : natsimplify.

Lemma mod_same_eq a b : a <> 0 -> a = b -> b mod a = 0.
Proof. intros; subst; apply mod_same; assumption. Qed.

Hint Rewrite @mod_same_eq using omega : natsimplify.
Hint Resolve mod_same_eq : arith.

Lemma mod_mod_eq a b c : a <> 0 -> b = c mod a -> b mod a = b.
Proof. intros; subst; autorewrite with natsimplify; reflexivity. Qed.

Hint Rewrite @mod_mod_eq using (reflexivity || omega) : natsimplify.

Local Arguments minus !_ !_.

Lemma S_mod_full a b : a <> 0 -> (S b) mod a = if eq_nat_dec (S (b mod a)) a
                                               then 0
                                               else S (b mod a).
Proof.
  change (S b) with (1+b); intros.
  pose proof (mod_bound_pos b a).
  rewrite add_mod by assumption.
  destruct (eq_nat_dec (S (b mod a)) a) as [H'|H'];
    destruct a as [|[|a]]; autorewrite with natsimplify in *;
      try congruence; try reflexivity.
Qed.

Hint Rewrite S_mod_full using omega : natsimplify.

Lemma S_mod a b : a <> 0 -> S (b mod a) <> a -> (S b) mod a = S (b mod a).
Proof.
  intros; rewrite S_mod_full by assumption.
  edestruct eq_nat_dec; omega.
Qed.

Hint Rewrite S_mod using (omega || autorewrite with natsimplify; omega) : natsimplify.

Lemma eq_nat_dec_refl x : eq_nat_dec x x = left (Logic.eq_refl x).
Proof.
  edestruct eq_nat_dec; try congruence.
  apply f_equal, Eqdep_dec.UIP_dec, eq_nat_dec.
Qed.

Hint Rewrite eq_nat_dec_refl : natsimplify.

(** Helper to get around the lack of function extensionality *)
Definition eq_nat_dec_right_val n m (pf0 : n <> m) : { pf | eq_nat_dec n m = right pf }.
Proof.
  revert dependent n; induction m; destruct n as [|n]; simpl;
    intro pf0;
    [ (exists pf0; exfalso; abstract congruence)
    | eexists; reflexivity
    | eexists; reflexivity
    | ].
  { specialize (IHm n (fun e => pf0 (f_equal_nat nat S n m e))).
    destruct IHm as [? IHm].
    eexists; rewrite IHm; reflexivity. }
Qed.

Lemma eq_nat_dec_S_n n : eq_nat_dec (S n) n = right (proj1_sig (@eq_nat_dec_right_val _ _ (@neq_succ_diag_l n))).
Proof.
  edestruct eq_nat_dec_right_val; assumption.
Qed.

Hint Rewrite eq_nat_dec_S_n : natsimplify.

Lemma eq_nat_dec_n_S n : eq_nat_dec n (S n) = right (proj1_sig (@eq_nat_dec_right_val _ _ (n_Sn n))).
Proof.
  edestruct eq_nat_dec_right_val; assumption.
Qed.

Hint Rewrite eq_nat_dec_n_S : natsimplify.
