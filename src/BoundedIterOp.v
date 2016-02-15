Require Import Crypto.Tactics.VerdiTactics.
Require Import BinNums NArith Nnat ZArith.

Definition testbit_rev p i bound := Pos.testbit_nat p (bound - i).

(* implements Pos.iter_op only using testbit, not destructing the positive *)
Definition iter_op  {A} (op : A -> A -> A) (zero : A) (bound : nat) (p : positive) :=
  fix iter (i : nat) (a : A) {struct i} : A :=
    match i with
    | O => zero
    | S i' => let ret := iter i' (op a a) in
             if testbit_rev p i bound
               then op a ret
               else      ret
    end.

Lemma testbit_rev_xI : forall p i b, (i < S b) ->
  testbit_rev p~1 i (S b) = testbit_rev p i b.
Proof.
  unfold testbit_rev; intros.
  replace (S b - i) with (S (b - i)) by omega.
  case_eq (b - S i); intros; simpl; auto.
Qed.

Lemma testbit_rev_xO : forall p i b, (i < S b) ->
  testbit_rev p~0 i (S b) = testbit_rev p i b.
Proof.
  unfold testbit_rev; intros.
  replace (S b - i) with (S (b - i)) by omega.
  case_eq (b - S i); intros; simpl; auto.
Qed.

Lemma testbit_rev_1 : forall i b, (i < S b) ->
  testbit_rev 1%positive i (S b) = false.
Proof.
  unfold testbit_rev; intros.
  replace (S b - i) with (S (b - i)) by omega.
  case_eq (b - S i); intros; simpl; auto.
Qed.

Lemma iter_op_step_xI : forall {A} p i op z b (a : A), (i < S b) ->
  iter_op op z (S b) p~1 i a = iter_op op z b p i a.
Proof.
  induction i; intros; [pose proof (Gt.gt_irrefl 0); intuition | ].
  simpl; rewrite testbit_rev_xI by omega.
  case_eq i; intros; auto.
  rewrite <- H0; simpl.
  rewrite IHi by omega; auto.
Qed.

Lemma iter_op_step_xO : forall {A} p i op z b (a : A), (i < S b) ->
  iter_op op z (S b) p~0 i a = iter_op op z b p i a.
Proof.
  induction i; intros; [pose proof (Gt.gt_irrefl 0); intuition | ].
  simpl; rewrite testbit_rev_xO by omega.
  case_eq i; intros; auto.
  rewrite <- H0; simpl.
  rewrite IHi by omega; auto.
Qed.

Lemma iter_op_step_1 : forall {A} i op z b (a : A), (i < S b) ->
  iter_op op z (S b) 1%positive i a = z.
Proof.
  induction i; intros; [pose proof (Gt.gt_irrefl 0); intuition | ].
  simpl; rewrite testbit_rev_1 by omega.
  case_eq i; intros; auto.
  rewrite <- H0; simpl.
  rewrite IHi by omega; auto.
Qed.

Lemma pos_size_gt0 : forall p, 0 < Pos.size_nat p.
Proof.
  intros; case_eq p; intros; simpl; auto; try apply Lt.lt_0_Sn.
Qed.
Hint Resolve pos_size_gt0.

Ltac iter_op_step := match goal with
| [ |- context[iter_op ?op ?z ?b ?p~1 ?i ?a] ] => rewrite iter_op_step_xI
| [ |- context[iter_op ?op ?z ?b ?p~0 ?i ?a] ] => rewrite iter_op_step_xO
| [ |- context[iter_op ?op ?z ?b 1%positive ?i ?a] ] => rewrite iter_op_step_1
end; auto.

Lemma iter_op_spec : forall b p {A} op z (a : A) (zero_id : forall x : A, op x z = x), (Pos.size_nat p <= b) ->
  iter_op op z b p b a = Pos.iter_op op p a.
Proof.
  induction b; intros; [pose proof (pos_size_gt0 p); omega |].
  simpl; unfold testbit_rev; rewrite Minus.minus_diag.
  case_eq p; intros; simpl; iter_op_step; simpl; 
  rewrite IHb; rewrite H0 in *; simpl in H; apply Le.le_S_n in H; auto.
Qed.

Lemma xO_neq1 : forall p, (1 < p~0)%positive.
Proof.
  induction p; simpl; auto.
  replace 2%positive with (Pos.succ 1) by auto.
  apply Pos.lt_succ_diag_r.
Qed.

Lemma xI_neq1 : forall p, (1 < p~1)%positive.
Proof.
  induction p; simpl; auto.
  replace 3%positive with (Pos.succ (Pos.succ 1)) by auto.
  pose proof (Pos.lt_succ_diag_r (Pos.succ 1)).
  pose proof (Pos.lt_succ_diag_r 1).
  apply (Pos.lt_trans _ _ _ H0 H).
Qed.

Lemma xI_is_succ : forall n p
  (H : Pos.of_succ_nat n = p~1%positive),
  (Pos.to_nat (2 * p))%nat = n.
Proof.
  induction n; intros; simpl in *; auto. {
    pose proof (xI_neq1 p).
    rewrite H in H0.
    pose proof (Pos.lt_irrefl p~1).
    intuition.
  } {
    rewrite Pos.xI_succ_xO in H.
    pose proof (Pos.succ_inj _ _ H); clear H.
    rewrite Pos.of_nat_succ in H0.
    rewrite <- Pnat.Pos2Nat.inj_iff in H0.
    rewrite Pnat.Pos2Nat.inj_xO in H0.
    rewrite Pnat.Nat2Pos.id in H0 by apply NPeano.Nat.neq_succ_0.
    rewrite H0.
    apply Pnat.Pos2Nat.inj_xO.
  }
Qed.

Lemma xO_is_succ : forall n p
  (H : Pos.of_succ_nat n = p~0%positive),
  Pos.to_nat (Pos.pred_double p) = n.
Proof.
  induction n; intros; simpl; auto. {
    pose proof (xO_neq1 p).
    simpl in H; rewrite H in H0.
    pose proof (Pos.lt_irrefl p~0).
    intuition.
  } {
    rewrite Pos.pred_double_spec.
    rewrite <- Pnat.Pos2Nat.inj_iff in H.
    rewrite Pnat.Pos2Nat.inj_xO in H.
    rewrite Pnat.SuccNat2Pos.id_succ in H.
    rewrite Pnat.Pos2Nat.inj_pred by apply xO_neq1.
    rewrite <- NPeano.Nat.succ_inj_wd.
    rewrite Pnat.Pos2Nat.inj_xO.
    rewrite <-  H.
    auto.
  }
Qed.

Lemma size_of_succ : forall n,
  Pos.size_nat (Pos.of_nat n) <= Pos.size_nat (Pos.of_nat (S n)).
Proof.
  intros; induction n; [simpl; auto|].
  apply Pos.size_nat_monotone.
  apply Pos.lt_succ_diag_r.
Qed.