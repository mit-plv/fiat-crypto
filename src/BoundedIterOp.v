Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Numbers.BinNums Coq.NArith.NArith Coq.NArith.Nnat Coq.ZArith.ZArith.

Definition testbit_rev p i bound := Pos.testbit_nat p (bound - i).

Lemma testbit_rev_succ : forall p i b, (i < S b) ->
  testbit_rev p i (S b) =
    match p with
    | xI p' => testbit_rev p' i b
    | xO p' => testbit_rev p' i b
    | 1%positive => false
    end.
Proof.
  unfold testbit_rev; intros; destruct p; rewrite <- minus_Sn_m by omega; auto.
Qed.

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

Lemma iter_op_step : forall {A} op z b p i (a : A), (i < S b) ->
  iter_op op z (S b) p i a =
    match p with
    | xI p' => iter_op op z b p' i a
    | xO p' => iter_op op z b p' i a
    | 1%positive => z
    end.
Proof.
  destruct p; unfold iter_op; (induction i; [ auto |]); intros; rewrite testbit_rev_succ by omega; rewrite IHi by omega; reflexivity.
Qed.

Lemma pos_size_gt0 : forall p, 0 < Pos.size_nat p.
Proof.
  destruct p; intros; auto; try apply Lt.lt_0_Sn.
Qed.
Hint Resolve pos_size_gt0.

Lemma iter_op_spec : forall b p {A} op z (a : A) (zero_id : forall x : A, op x z = x), (Pos.size_nat p <= b) ->
  iter_op op z b p b a = Pos.iter_op op p a.
Proof.
  induction b; intros; [pose proof (pos_size_gt0 p); omega |].
  destruct p; simpl; rewrite iter_op_step by omega; unfold testbit_rev; rewrite Minus.minus_diag; try rewrite IHb; simpl in *; auto; omega.
Qed.

Lemma xO_neq1 : forall p, (1 < p~0)%positive.
Proof.
  induction p; auto; apply Pos.lt_succ_diag_r.
Qed.

Lemma xI_neq1 : forall p, (1 < p~1)%positive.
Proof.
  induction p; auto; eapply Pos.lt_trans; apply Pos.lt_succ_diag_r.
Qed.

Lemma xI_is_succ : forall n p, Pos.of_succ_nat n = p~1%positive ->
  (Pos.to_nat (2 * p))%nat = n.
Proof.
  induction n; intros; try discriminate.
  rewrite <- Pnat.Nat2Pos.id by apply NPeano.Nat.neq_succ_0.
  rewrite Pnat.Pos2Nat.inj_iff.
  rewrite <- Pos.of_nat_succ.
  apply Pos.succ_inj.
  rewrite <- Pos.xI_succ_xO.
  auto.
Qed.

Lemma xO_is_succ : forall n p, Pos.of_succ_nat n = p~0%positive ->
  Pos.to_nat (Pos.pred_double p) = n.
Proof.
  induction n; intros; try discriminate.
  rewrite Pos.pred_double_spec.
  rewrite <- Pnat.Pos2Nat.inj_iff in *.
  rewrite Pnat.Pos2Nat.inj_xO in *.
  rewrite Pnat.SuccNat2Pos.id_succ in *.
  rewrite Pnat.Pos2Nat.inj_pred by apply xO_neq1.
  rewrite <- NPeano.Nat.succ_inj_wd.
  rewrite Pnat.Pos2Nat.inj_xO.
  omega.
Qed.

Lemma size_of_succ : forall n,
  Pos.size_nat (Pos.of_nat n) <= Pos.size_nat (Pos.of_nat (S n)).
Proof.
  intros; induction n; [simpl; auto|].
  apply Pos.size_nat_monotone.
  apply Pos.lt_succ_diag_r.
Qed.
