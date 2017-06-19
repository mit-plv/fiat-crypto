Require Coq.Logic.Eqdep_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Import Nat.

Scheme Equality for nat.

Create HintDb natsimplify discriminated.

Hint Resolve mod_bound_pos plus_le_compat : arith.
Hint Resolve (fun x y p q => proj1 (@Nat.mod_bound_pos x y p q)) (fun x y p q => proj2 (@Nat.mod_bound_pos x y p q)) : arith.

Hint Rewrite @mod_small @mod_mod @mod_1_l @mod_1_r succ_pred using omega : natsimplify.

Hint Rewrite sub_diag add_0_l add_0_r sub_0_r sub_succ : natsimplify.

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

Lemma nat_eq_dec_S x y
  : match nat_eq_dec (S x) (S y), nat_eq_dec x y with
    | left pfS, left pf => pfS = f_equal S pf
    | right _, right _ => True
    | _, _ => False
    end.
Proof.
  unfold nat_eq_dec; simpl.
  match goal with
  | [ |- match match ?e with _ => _ end with _ => _ end ]
    => destruct e
  end; simpl; try exact I.
  reflexivity.
Defined.

Lemma UIP_nat_transparent x y (p1 p2 : x = y :> nat) : p1 = p2.
Proof.
  transitivity (match nat_eq_dec x y, nat_eq_dec y y with
                | left pf1, left pf2 => eq_trans pf1 (eq_sym pf2)
                | _, _ => p1
                end);
    [ revert p2 | revert p1 ];
    subst y; intro p;
      destruct (nat_eq_dec x x) as [q|q]; case q; reflexivity.
Defined.

Lemma nat_beq_false_iff x y : nat_beq x y = false <-> x <> y.
Proof.
  split; intro H; repeat intro; subst.
  { erewrite internal_nat_dec_lb in H by reflexivity; congruence. }
  { destruct (nat_beq x y) eqn:H'; [ | reflexivity ].
    apply internal_nat_dec_bl in H'; subst; congruence. }
Qed.

Ltac nat_beq_to_eq :=
  repeat match goal with
         | [ H : nat_beq _ _ = true |- _ ] => apply internal_nat_dec_bl in H
         | [ H : is_true (nat_beq _ _) = true |- _ ] => apply internal_nat_dec_bl in H
         | [ |- nat_beq _ _ = true ] => apply internal_nat_dec_lb
         | [ |- is_true (nat_beq _ _) ] => apply internal_nat_dec_lb
         | [ H : nat_beq _ _ = false |- _ ] => apply nat_beq_false_iff in H
         | [ |- nat_beq _ _ = false ] => apply nat_beq_false_iff
         end.

Lemma div_minus : forall a b, b <> 0 -> (a + b) / b = a / b + 1.
Proof.
  intros a b H.
  assert (H0 : b = 1 * b) by omega.
  rewrite H0 at 1.
  rewrite <- Nat.div_add by auto.
  reflexivity.
Qed.

Lemma pred_mod : forall m, (0 < m)%nat -> ((pred m) mod m)%nat = pred m.
Proof.
  intros m H; apply Nat.mod_small.
  destruct m; try omega; rewrite Nat.pred_succ; auto.
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
  induction c; intros x H H0; pose proof (div_mod x 4 ne40) as H1; rewrite <- H in H1. {
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
    pose proof (IHc _ H H0) as H2.
    destruct H2 as [x0 H2].
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
  revert dependent n; induction m as [|m IHm]; destruct n as [|n]; simpl;
    intro pf0;
    [ (exists pf0; exfalso; abstract congruence)
    | eexists; reflexivity
    | eexists; reflexivity
    | ].
  { specialize (IHm n).
    destruct IHm as [? IHm]; [ omega | ].
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

Hint Rewrite Max.max_0_l Max.max_0_r Max.max_idempotent Min.min_0_l Min.min_0_r Min.min_idempotent : natsimplify.

(** Helper to get around the lack of function extensionality *)
Definition le_dec_right_val n m (pf0 : ~n <= m) : { pf | le_dec n m = right pf }.
Proof.
  destruct (le_dec n m) eqn:Heq; [ | eexists; reflexivity ].
  exfalso; clear Heq; apply pf0; assumption.
Qed.

(** Helper to get around the lack of function extensionality *)
Definition lt_dec_right_val n m (pf0 : ~n < m) : { pf | lt_dec n m = right pf }
  := @le_dec_right_val _ _ pf0.

Lemma lt_dec_irrefl n : lt_dec n n = right (proj1_sig (@lt_dec_right_val _ _ (lt_irrefl n))).
Proof. edestruct lt_dec_right_val; assumption. Qed.
Hint Rewrite lt_dec_irrefl : natsimplify.

Lemma not_lt_n_pred_n n : ~n < pred n.
Proof. destruct n; simpl; omega. Qed.

Lemma lt_dec_n_pred_n n : lt_dec n (pred n) = right (proj1_sig (@lt_dec_right_val _ _ (not_lt_n_pred_n n))).
Proof. edestruct lt_dec_right_val; assumption. Qed.
Hint Rewrite lt_dec_n_pred_n : natsimplify.

Lemma le_dec_refl n : le_dec n n = left (le_refl n).
Proof.
  edestruct le_dec; try omega.
  apply f_equal, le_unique.
Qed.
Hint Rewrite le_dec_refl : natsimplify.

Lemma le_dec_pred_l n : le_dec (pred n) n = left (le_pred_l n).
Proof.
  edestruct le_dec; [ | destruct n; simpl in *; omega ].
  apply f_equal, le_unique.
Qed.
Hint Rewrite le_dec_pred_l : natsimplify.

Lemma le_pred_plus_same n : n <= pred (n + n).
Proof. destruct n; simpl; omega. Qed.

Lemma le_dec_pred_plus_same n : le_dec n (pred (n + n)) = left (le_pred_plus_same n).
Proof.
  edestruct le_dec; [ | destruct n; simpl in *; omega ].
  apply f_equal, le_unique.
Qed.
Hint Rewrite le_dec_pred_plus_same : natsimplify.

Lemma minus_S_diag x : (S x - x = 1)%nat.
Proof. omega. Qed.
Hint Rewrite minus_S_diag : natsimplify.

Lemma min_idempotent_S_l x : min (S x) x = x.
Proof. omega *. Qed.
Hint Rewrite min_idempotent_S_l : natsimplify.

Lemma min_idempotent_S_r x : min x (S x) = x.
Proof. omega *. Qed.
Hint Rewrite min_idempotent_S_r : natsimplify.

Lemma mod_pow_same b e : b <> 0 -> e <> 0 -> b^e mod b = 0.
Proof.
  intros; destruct e as [|e]; [ omega | simpl ].
  rewrite mul_comm, mod_mul by omega; omega.
Qed.

Lemma setbit_high : forall x i, (x < 2^i -> setbit x i = x + 2^i)%nat.
Proof.
  intros x i H; apply bits_inj; intro n.
  rewrite setbit_eqb.
  destruct (beq_nat i n) eqn:H'; simpl.
  { apply beq_nat_true in H'; subst.
    symmetry; apply testbit_true.
    rewrite div_minus, div_small by omega.
    reflexivity. }
  { assert (H'' : (((x + 2 ^ i) / 2 ^ n) mod 2) = ((x / 2 ^ n) mod 2)).
    { assert (2^(i-n) <> 0) by auto with arith.
      assert (2^(i-n) <> 0) by omega.
      destruct (lt_eq_lt_dec i n) as [ [?|?] | ? ]; [ | subst; rewrite <- beq_nat_refl in H'; congruence | ].
      { assert (i <= n - 1) by omega.
        assert (2^i <= 2^n) by auto using pow_le_mono_r with arith.
        assert (2^i <= 2^(n - 1)) by auto using pow_le_mono_r with arith.
        assert (2^(n-1) <> 0) by auto with arith.
        assert (2^(n-1) + 2^(n-1) = 2^n)
          by (transitivity (2^(S (n - 1))); [ simpl; omega | apply f_equal; omega ]).
        assert ((2^(n - 1) - 1) + (2^(n - 1)) < 2^n) by omega.
        rewrite !div_small; try omega. }
      { replace (2^i) with (2^(i - n) * 2^n)
          by (rewrite <- pow_add_r, ?le_plus_minus_r, ?sub_add by omega; omega).
        rewrite div_add by auto with arith.
        rewrite <- add_mod_idemp_r, mod_pow_same, add_0_r by omega.
        reflexivity. } }
    { match goal with
      | [ |- ?x = ?y ]
        => destruct x eqn:H0; destruct y eqn:H1; try reflexivity;
             try apply testbit_true in H0;
             try apply testbit_true in H1;
             first [ rewrite <- H0; clear H0 | rewrite <- H1; clear H1 ];
             first [ symmetry; apply testbit_true | apply testbit_true ]
      end;
        rewrite H'' in *; assumption. } }
Qed.
