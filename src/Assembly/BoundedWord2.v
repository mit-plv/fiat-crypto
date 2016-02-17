
Require Import Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Compare_dec.
Require Import ProofIrrelevance.
Require Import Ring.

Set Implicit Arguments.

Section BoundedWord.

  Delimit Scope Bounded_scope with bounded.

  Open Scope Bounded_scope.

  Lemma le_ge : forall n m, (n <= m -> m >= n)%nat.
  Proof.
    intros; omega.
  Qed.

  Lemma ge_le : forall n m, (n >= m -> m <= n)%nat.
  Proof.
    intros; omega.
  Qed.

  Definition wordLeN {n: nat} (a: word n) (b: N): Prop :=
    (wordToN a <= b)%N.

  Notation "A <= B" := (wordLeN A B) (at level 70) : Bounded_scope.

  Variable n : nat.

  Ltac ge_to_le :=
    try apply N.ge_le;
    repeat match goal with
           | [ H : _ |- _ ] => apply N.le_ge in H
           end.

  Ltac ge_to_le_nat :=
    try apply le_ge;
    repeat match goal with
           | [ H : _ |- _ ] => apply ge_le in H
           end.

  Ltac preomega := unfold wordLeN; intros; ge_to_le; pre_nomega.

  Hint Rewrite wordToN_nat Nat2N.inj_add N2Nat.inj_add Nat2N.inj_mul N2Nat.inj_mul Npow2_nat : N.

  Theorem wplus_bound : forall (w1 w2 : word n) b1 b2,
    w1 <= b1
    -> w2 <= b2
    -> w1 ^+ w2 <= b1 + b2.
  Proof.
    preomega.
    destruct (le_lt_dec (pow2 n) (N.to_nat b1 + N.to_nat b2)).

    specialize (wordToNat_bound (w1 ^+ w2)); nomega.

    rewrite wplus_alt.
    unfold wplusN, wordBinN.
    rewrite wordToNat_natToWord_idempotent; nomega.
  Qed.

  Theorem wmult_bound : forall (w1 w2 : word n) b1 b2,
    w1 <= b1
    -> w2 <= b2
    -> w1 ^* w2 <= b1 * b2.
  Proof.
    preomega.
    destruct (le_lt_dec (pow2 n) (N.to_nat b1 * N.to_nat b2)).

    specialize (wordToNat_bound (w1 ^* w2)); nomega.

    rewrite wmult_alt.
    unfold wmultN, wordBinN.
    rewrite wordToNat_natToWord_idempotent.
    ge_to_le_nat.
    apply Mult.mult_le_compat; nomega.
    pre_nomega.
    apply Lt.le_lt_trans with (N.to_nat b1 * N.to_nat b2); auto.
    apply Mult.mult_le_compat; nomega.
  Qed.

  Lemma example_bound_simpl: forall (w1 w2 w3 w4 : word n) b1 b2 b3 b4,
    w1 <= b1
    -> w2 <= b2
    -> w3 <= b3
    -> w4 <= b4
    -> { b | w1 ^+ (w2 ^* w3) ^* w4 <= b }.    
  Proof.
    eexists.
    repeat (eassumption || apply wplus_bound || apply wmult_bound).
  Defined.

  Eval simpl in fun (w1 w2 w3 w4 : word n) (b1 b2 b3 b4 : N)
                    (H1 : w1 <= b1) (H2 : w2 <= b2) (H3 : w3 <= b3) (H4 : w4 <= b4) =>
                  projT1 (example_bound_simpl H1 H2 H3 H4).

End BoundedWord.
