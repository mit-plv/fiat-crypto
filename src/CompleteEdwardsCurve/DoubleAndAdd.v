Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Util.IterAssocOp.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Coq.Numbers.BinNums Coq.NArith.NArith Coq.NArith.Nnat Coq.ZArith.ZArith.

Section EdwardsDoubleAndAdd.
  Context {prm:TwistedEdwardsParams}.
  Definition doubleAndAdd (bound n : nat) (P : point) : point :=
    iter_op unifiedAdd zero N.testbit_nat (N.of_nat n) P bound.

  Lemma scalarMult_double : forall n P, scalarMult (n + n) P = scalarMult n (P + P)%E.
  Proof.
    intros.
    replace (n + n)%nat with (n * 2)%nat by omega.
    induction n; simpl; auto.
    rewrite twistedAddAssoc.
    f_equal; auto.
  Qed.

  Lemma doubleAndAdd_spec : forall bound n P, N.size_nat (N.of_nat n) <= bound ->
    scalarMult n P = doubleAndAdd bound n P.
  Proof.
    induction n; auto; intros; unfold doubleAndAdd;
      rewrite iter_op_spec with (scToN := fun x => x); (
        unfold Morphisms.Proper, Morphisms.respectful, Equivalence.equiv;
        intros; subst; try rewrite Nat2N.id;
        reflexivity || assumption || apply twistedAddAssoc
        || rewrite twistedAddComm; apply zeroIsIdentity).
  Qed.
End EdwardsDoubleAndAdd.