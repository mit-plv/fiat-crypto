Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.BoundedIterOp.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import BinNums NArith Nnat ZArith.

Section EdwardsDoubleAndAdd.
  Context {prm:TwistedEdwardsParams}.
  Definition doubleAndAdd (b n : nat) (P : point) : point :=
    match N.of_nat n with
    | 0%N => zero
    | N.pos p => iter_op unifiedAdd zero b p b P
    end.

  Lemma scalarMult_double : forall n P, scalarMult (n + n) P = scalarMult n (P + P)%E.
  Proof.
    intros.
    replace (n + n)%nat with (n * 2)%nat by omega.
    induction n; simpl; auto.
    rewrite twistedAddAssoc.
    f_equal; auto.
  Qed.

  Lemma iter_op_double : forall p P,
    Pos.iter_op unifiedAdd (p + p) P = Pos.iter_op unifiedAdd p (P + P)%E.
  Proof.
    intros.
    rewrite Pos.add_diag.
    unfold Pos.iter_op; simpl.
    auto.
  Qed.

  Lemma doubleAndAdd_spec : forall n b P, (Pos.size_nat (Pos.of_nat n) <= b) ->
    scalarMult n P = doubleAndAdd b n P.
  Proof.
    induction n; auto; intros.
    unfold doubleAndAdd; simpl.
    rewrite Pos.of_nat_succ.
    rewrite iter_op_spec by (auto using zeroIsIdentity).
    case_eq (Pos.of_nat (S n)); intros. {
      simpl; f_equal.
      rewrite (IHn b) by (pose proof (size_of_succ n); omega).
      unfold doubleAndAdd.
      rewrite H0 in H.
      rewrite <- Pos.of_nat_succ in H0.
      rewrite <- (xI_is_succ n p) by apply H0.
      rewrite Znat.positive_nat_N; simpl.
      rewrite iter_op_spec; auto using zeroIsIdentity.
    } {
      simpl; f_equal.
      rewrite (IHn b) by (pose proof (size_of_succ n); omega).
      unfold doubleAndAdd.
      rewrite <- (xO_is_succ n p) by (rewrite Pos.of_nat_succ; auto).
      rewrite Znat.positive_nat_N; simpl.
      rewrite <- Pos.succ_pred_double in H0.
      rewrite H0 in H.
      rewrite iter_op_spec by (auto using zeroIsIdentity;
        pose proof (Pos.lt_succ_diag_r (Pos.pred_double p));
        apply Pos.size_nat_monotone in H1; omega; auto).
      rewrite <- iter_op_double.
      rewrite Pos.add_diag.
      rewrite <- Pos.succ_pred_double.
      rewrite Pos.iter_op_succ by apply twistedAddAssoc; auto.
    } {
      rewrite <- Pnat.Pos2Nat.inj_iff in H0.
      rewrite Pnat.Nat2Pos.id in H0 by auto.
      rewrite Pnat.Pos2Nat.inj_1 in H0.
      assert (n = 0)%nat by omega; subst.
      auto using zeroIsIdentity.
    }
  Qed.
End EdwardsDoubleAndAdd.