Require Coq.Logic.Eqdep_dec.
Require Import Coq.NArith.NArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.micromega.Lia.
Import Nat.

Scheme Equality for nat.

Create HintDb natsimplify discriminated.

Global Hint Resolve mod_bound_pos plus_le_compat : arith.
#[global]
Hint Rewrite @mod_small @mod_mod @mod_1_l @mod_1_r succ_pred using lia : natsimplify.

#[global]
Hint Rewrite sub_diag add_0_l add_0_r sub_0_r sub_succ : natsimplify.

Local Open Scope nat_scope.

Lemma mod_bound_nonneg x y : 0 <= x mod y.
Proof.
  now apply Nat.le_0_l.
Qed.

Lemma mod_bound_lt x y : 0 < y -> x mod y < y.
Proof. apply Nat.mod_bound_pos; lia. Qed.

Global Hint Resolve mod_bound_nonneg mod_bound_lt : arith.

Lemma min_def {x y} : min x y = x - (x - y).
Proof. apply Min.min_case_strong; lia. Qed.
Lemma max_def {x y} : max x y = x + (y - x).
Proof. apply Max.max_case_strong; lia. Qed.
Ltac coq_lia := lia.
Ltac handle_min_max_for_lia_gen min max :=
  repeat match goal with
         | [ H : context[min _ _] |- _ ] => rewrite !min_def in H || setoid_rewrite min_def in H
         | [ H : context[max _ _] |- _ ] => rewrite !max_def in H || setoid_rewrite max_def in H
         | [ |- context[min _ _] ] => rewrite !min_def || setoid_rewrite min_def
         | [ |- context[max _ _] ] => rewrite !max_def || setoid_rewrite max_def
         end.
Ltac handle_min_max_for_lia_case_gen min max :=
  repeat match goal with
         | [ H : context[min _ _] |- _ ] => revert H
         | [ H : context[max _ _] |- _ ] => revert H
         | [ |- context[min _ _] ] => apply Min.min_case_strong
         | [ |- context[max _ _] ] => apply Max.max_case_strong
         end;
  intros.
Ltac handle_min_max_for_lia := handle_min_max_for_lia_gen min max.
Ltac handle_min_max_for_lia_case := handle_min_max_for_lia_case_gen min max.
(* In 8.4, Nat.min is a definition, so we need to unfold it *)
Ltac handle_min_max_for_lia_compat_84 :=
  let min := (eval cbv [min] in min) in
  let max := (eval cbv [max] in max) in
  handle_min_max_for_lia_gen min max.
Ltac handle_min_max_for_lia_case_compat_84 :=
  let min := (eval cbv [min] in min) in
  let max := (eval cbv [max] in max) in
  handle_min_max_for_lia_case_gen min max.
Ltac lia_with_min_max :=
  handle_min_max_for_lia;
  try handle_min_max_for_lia_compat_84;
  lia.
Ltac lia_with_min_max_case :=
  handle_min_max_for_lia_case;
  try handle_min_max_for_lia_case_compat_84;
  lia.
Tactic Notation "lia" := coq_lia.
Tactic Notation "lia" "*" := lia_with_min_max_case.
Tactic Notation "lia" "**" := lia_with_min_max.

Global Instance nat_rect_Proper {P} : Proper (Logic.eq ==> forall_relation (fun _ => forall_relation (fun _ => Logic.eq)) ==> forall_relation (fun _ => Logic.eq)) (@nat_rect P).
Proof.
  cbv [forall_relation]; intros O_case O_case' ? S_case S_case' HS n; subst O_case'; revert O_case.
  induction n as [|n IHn]; cbn [nat_rect]; intro; rewrite ?IHn, ?HS; reflexivity.
Qed.
Global Instance nat_rect_Proper_nondep {P} : Proper (Logic.eq ==> pointwise_relation _ (pointwise_relation _ Logic.eq) ==> Logic.eq ==> Logic.eq) (@nat_rect (fun _ => P)).
Proof. repeat intro; subst; apply (@nat_rect_Proper (fun _ => P)); eauto. Qed.

Global Instance nat_rect_Proper_nondep_gen {P} (R : relation P) : Proper (R ==> (Logic.eq ==> R ==> R) ==> Logic.eq ==> R) (@nat_rect (fun _ => P)) | 100.
Proof.
  cbv [forall_relation respectful]; intros O_case O_case' HO S_case S_case' HS n n' ?; subst n'; revert O_case O_case' HO.
  induction n as [|n IHn]; cbn [nat_rect]; intros; eauto.
Qed.

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
  assert (H0 : b = 1 * b) by lia.
  rewrite H0 at 1.
  rewrite <- Nat.div_add by auto.
  reflexivity.
Qed.

Lemma pred_mod : forall m, (0 < m)%nat -> ((pred m) mod m)%nat = pred m.
Proof.
  intros m H; apply Nat.mod_small.
  destruct m; try lia; rewrite Nat.pred_succ; auto.
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
  intros; apply Nat.div_small, mod_bound_pos; lia.
Qed.

Lemma divide2_1mod4_nat : forall c x, c = x / 4 -> x mod 4 = 1 -> exists y, 2 * y = (x / 2).
Proof.
  assert (4 <> 0) as ne40 by lia.
  induction c; intros x H H0; pose proof (div_mod x 4 ne40) as H1; rewrite <- H in H1. {
    rewrite H0 in H1.
    simpl in H1.
    rewrite H1.
    exists 0; auto.
  } {
    rewrite mult_succ_r in H1.
    assert (4 <= x) as le4x by (apply Nat.div_str_pos_iff; lia).
    rewrite <- Nat.add_1_r in H.
    replace x with ((x - 4) + 4) in H by lia.
    rewrite div_minus in H by auto.
    apply Nat.add_cancel_r in H.
    replace x with ((x - 4) + (1 * 4)) in H0 by lia.
    rewrite Nat.mod_add in H0 by auto.
    pose proof (IHc _ H H0) as H2.
    destruct H2 as [x0 H2].
    exists (x0 + 1).
    rewrite <- (Nat.sub_add 4 x) in H1 at 1 by auto.
    replace (4 * c + 4 + x mod 4) with (4 * c + x mod 4 + 4) in H1 by lia.
    apply Nat.add_cancel_r in H1.
    replace (2 * (x0 + 1)) with (2 * x0 + 2)
      by (rewrite Nat.mul_add_distr_l; auto).
    rewrite H2.
    rewrite <- Nat.div_add by lia.
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
  intros; lia.
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

Global Hint Resolve pow_nonzero : arith.

Lemma S_pred_nonzero : forall a, (a > 0 -> S (pred a) = a)%nat.
Proof.
  destruct a; simpl; lia.
Qed.

#[global]
Hint Rewrite S_pred_nonzero using lia : natsimplify.

Lemma mod_same_eq a b : a <> 0 -> a = b -> b mod a = 0.
Proof. intros; subst; apply mod_same; assumption. Qed.

#[global]
Hint Rewrite @mod_same_eq using lia : natsimplify.
Global Hint Resolve mod_same_eq : arith.

Lemma mod_mod_eq a b c : a <> 0 -> b = c mod a -> b mod a = b.
Proof. intros; subst; autorewrite with natsimplify; reflexivity. Qed.

#[global]
Hint Rewrite @mod_mod_eq using (reflexivity || lia) : natsimplify.

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

#[global]
Hint Rewrite S_mod_full using lia : natsimplify.

Lemma S_mod a b : a <> 0 -> S (b mod a) <> a -> (S b) mod a = S (b mod a).
Proof.
  intros; rewrite S_mod_full by assumption.
  edestruct eq_nat_dec; lia.
Qed.

#[global]
Hint Rewrite S_mod using (lia || autorewrite with natsimplify; lia) : natsimplify.

Lemma eq_nat_dec_refl x : eq_nat_dec x x = left (Logic.eq_refl x).
Proof.
  edestruct eq_nat_dec; try congruence.
  apply f_equal, Eqdep_dec.UIP_dec, eq_nat_dec.
Qed.

#[global]
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
    destruct IHm as [? IHm]; [ lia | ].
    eexists; rewrite IHm; reflexivity. }
Qed.

Lemma eq_nat_dec_S_n n : eq_nat_dec (S n) n = right (proj1_sig (@eq_nat_dec_right_val _ _ (@neq_succ_diag_l n))).
Proof.
  edestruct eq_nat_dec_right_val; assumption.
Qed.

#[global]
Hint Rewrite eq_nat_dec_S_n : natsimplify.

Lemma eq_nat_dec_n_S n : eq_nat_dec n (S n) = right (proj1_sig (@eq_nat_dec_right_val _ _ (n_Sn n))).
Proof.
  edestruct eq_nat_dec_right_val; assumption.
Qed.

#[global]
Hint Rewrite eq_nat_dec_n_S : natsimplify.

#[global]
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
#[global]
Hint Rewrite lt_dec_irrefl : natsimplify.

Lemma not_lt_n_pred_n n : ~n < pred n.
Proof. destruct n; simpl; lia. Qed.

Lemma lt_dec_n_pred_n n : lt_dec n (pred n) = right (proj1_sig (@lt_dec_right_val _ _ (not_lt_n_pred_n n))).
Proof. edestruct lt_dec_right_val; assumption. Qed.
#[global]
Hint Rewrite lt_dec_n_pred_n : natsimplify.

Lemma le_dec_refl n : le_dec n n = left (le_refl n).
Proof.
  edestruct le_dec; try ((idtac + exfalso); lia).
  apply f_equal, le_unique.
Qed.
#[global]
Hint Rewrite le_dec_refl : natsimplify.

Lemma le_dec_pred_l n : le_dec (pred n) n = left (le_pred_l n).
Proof.
  edestruct le_dec; [ | destruct n; simpl in *; (idtac + exfalso); lia ].
  apply f_equal, le_unique.
Qed.
#[global]
Hint Rewrite le_dec_pred_l : natsimplify.

Lemma le_pred_plus_same n : n <= pred (n + n).
Proof. destruct n; simpl; lia. Qed.

Lemma le_dec_pred_plus_same n : le_dec n (pred (n + n)) = left (le_pred_plus_same n).
Proof.
  edestruct le_dec; [ | destruct n; simpl in *; (idtac + exfalso); lia ].
  apply f_equal, le_unique.
Qed.
#[global]
Hint Rewrite le_dec_pred_plus_same : natsimplify.

Lemma minus_S_diag x : (S x - x = 1)%nat.
Proof. lia. Qed.
#[global]
Hint Rewrite minus_S_diag : natsimplify.

Lemma min_idempotent_S_l x : min (S x) x = x.
Proof. lia *. Qed.
#[global]
Hint Rewrite min_idempotent_S_l : natsimplify.

Lemma min_idempotent_S_r x : min x (S x) = x.
Proof. lia *. Qed.
#[global]
Hint Rewrite min_idempotent_S_r : natsimplify.

Lemma mod_pow_same b e : b <> 0 -> e <> 0 -> b^e mod b = 0.
Proof.
  intros; destruct e as [|e]; [ lia | simpl ].
  rewrite mul_comm, mod_mul by lia; lia.
Qed.

Lemma setbit_high : forall x i, (x < 2^i -> setbit x i = x + 2^i)%nat.
Proof.
  intros x i H; apply bits_inj; intro n.
  rewrite setbit_eqb.
  destruct (beq_nat i n) eqn:H'; simpl.
  { apply beq_nat_true in H'; subst.
    symmetry; apply testbit_true.
    rewrite div_minus, div_small by lia.
    reflexivity. }
  { assert (H'' : (((x + 2 ^ i) / 2 ^ n) mod 2) = ((x / 2 ^ n) mod 2)).
    { assert (2^(i-n) <> 0) by auto with arith.
      assert (2^(i-n) <> 0) by lia.
      destruct (lt_eq_lt_dec i n) as [ [?|?] | ? ]; [ | subst; rewrite <- beq_nat_refl in H'; congruence | ].
      { assert (i <= n - 1) by lia.
        assert (2^i <= 2^n) by auto using pow_le_mono_r with arith.
        assert (2^i <= 2^(n - 1)) by auto using pow_le_mono_r with arith.
        assert (2^(n-1) <> 0) by auto with arith.
        assert (2^(n-1) + 2^(n-1) = 2^n)
          by (transitivity (2^(S (n - 1))); [ simpl; lia | apply f_equal; lia ]).
        assert ((2^(n - 1) - 1) + (2^(n - 1)) < 2^n) by lia.
        rewrite !div_small; try lia. }
      { replace (2^i) with (2^(i - n) * 2^n)
          by (rewrite <- pow_add_r, ?le_plus_minus_r, ?sub_add by lia; lia).
        rewrite div_add by auto with arith.
        rewrite <- add_mod_idemp_r, mod_pow_same, add_0_r by lia.
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

Lemma max_0_iff a b : Nat.max a b = 0%nat <-> (a = 0%nat /\ b = 0%nat).
Proof. lia **. Qed.

Lemma push_f_nat_rect {P P'} (f : P -> P') PO PS PS' n
      (HS : forall x rec, f (PS x rec)
                          = PS' x (f rec))
  : f (nat_rect (fun _ => P) PO PS n)
    = nat_rect
        (fun _ => _)
        (f PO)
        PS'
        n.
Proof.
  induction n as [|n IHn]; cbn [nat_rect]; [ reflexivity | ].
  rewrite HS, IHn; reflexivity.
Qed.

Lemma push_f_nat_rect_arrow {P P'} (f : P -> P') {A} PO PS PS' n v
      (HS : forall x rec v, f (PS x rec v)
                            = PS' x (fun v => f (rec v)) v)
      (PS'_Proper : Proper (Logic.eq ==> pointwise_relation _ Logic.eq ==> Logic.eq ==> Logic.eq) PS')
  : f (nat_rect (fun _ => A -> P) PO PS n v)
    = nat_rect
        (fun _ => _)
        (fun v => f (PO v))
        PS'
        n
        v.
Proof.
  revert v; induction n as [|n IHn]; cbn [nat_rect]; [ reflexivity | ]; intro.
  rewrite HS; apply PS'_Proper; eauto.
Qed.

Lemma min_x_xy x y : Nat.min x (Nat.min x y) = Nat.min x y.
Proof. now rewrite Nat.min_assoc; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite min_x_xy : natsimplify.

Lemma min_x_yx x y : Nat.min x (Nat.min y x) = Nat.min x y.
Proof. now rewrite Nat.min_comm, <- Nat.min_assoc, Nat.min_comm; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite min_x_yx : natsimplify.

Lemma min_xy_x x y : Nat.min (Nat.min x y) x = Nat.min x y.
Proof. now rewrite Nat.min_comm, Nat.min_assoc; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite min_xy_x : natsimplify.

Lemma min_yx_x x y : Nat.min (Nat.min y x) x = Nat.min y x.
Proof. now rewrite <- Nat.min_assoc; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite min_yx_x : natsimplify.

Lemma max_x_xy x y : Nat.max x (Nat.max x y) = Nat.max x y.
Proof. now rewrite Nat.max_assoc; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite max_x_xy : natsimplify.

Lemma max_x_yx x y : Nat.max x (Nat.max y x) = Nat.max x y.
Proof. now rewrite Nat.max_comm, <- Nat.max_assoc, Nat.max_comm; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite max_x_yx : natsimplify.

Lemma max_xy_x x y : Nat.max (Nat.max x y) x = Nat.max x y.
Proof. now rewrite Nat.max_comm, Nat.max_assoc; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite max_xy_x : natsimplify.

Lemma max_yx_x x y : Nat.max (Nat.max y x) x = Nat.max y x.
Proof. now rewrite <- Nat.max_assoc; autorewrite with natsimplify. Qed.
#[global]
Hint Rewrite max_yx_x : natsimplify.

Ltac inversion_nat_eq_step :=
  match goal with
  | [ H : O = S _ |- _ ] => solve [ inversion H ]
  | [ H : S _ = O |- _ ] => solve [ inversion H ]
  | [ H : O = O |- _ ] => clear H
  | [ H : O = O |- _ ] => pose proof (@UIP_nat _ _ eq_refl H); subst H
  | [ H : S _ = S _ |- _ ]
    => apply (f_equal pred) in H; cbn [pred] in H
  end.
Ltac inversion_nat_eq := repeat inversion_nat_eq_step.

Ltac inversion_nat_rel_step :=
  first [ inversion_nat_eq_step
        | match goal with
          | [ H : S _ <= O |- _ ] => exfalso; clear -H; lia
          | [ H : _ < O |- _ ] => exfalso; clear -H; lia
          | [ H : O >= S _ |- _ ] => exfalso; clear -H; lia
          | [ H : O > _ |- _ ] => exfalso; clear -H; lia
          | [ H : O <= _ |- _ ] => clear H
          | [ H : O < S _ |- _ ] => clear H
          | [ H : _ >= O |- _ ] => clear H
          | [ H : S _ > O |- _ ] => clear H
          | [ H : S _ <= S _ |- _ ] => apply le_S_n in H
          | [ H : S _ < S _ |- _ ] => rewrite <- succ_lt_mono in H
          | [ H : S _ >= S _ |- _ ] => progress cbv [ge] in H
          | [ H : S _ > S _ |- _ ] => progress cbv [gt] in H
          end ].
Ltac inversion_nat_rel := repeat inversion_nat_rel_step.
