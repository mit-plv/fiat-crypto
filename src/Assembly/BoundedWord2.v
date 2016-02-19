
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

  Theorem constant_bound_N : forall k,
    NToWord n k <= k.
  Proof.
    preomega.
    rewrite NToWord_nat.
    destruct (le_lt_dec (pow2 n) (N.to_nat k)).

    specialize (wordToNat_bound (natToWord n (N.to_nat k))); nomega.

    rewrite wordToNat_natToWord_idempotent; nomega.
  Qed.

  Theorem constant_bound_nat : forall k,
    natToWord n k <= N.of_nat k.
  Proof.
    preomega.
    destruct (le_lt_dec (pow2 n) k).

    specialize (wordToNat_bound (natToWord n k)); nomega.

    rewrite wordToNat_natToWord_idempotent; nomega.
  Qed.

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

  Ltac word_bound := repeat (eassumption || apply wplus_bound || apply wmult_bound
                             || apply constant_bound_N || apply constant_bound_nat).

  Lemma example1 : forall (w1 w2 w3 w4 : word n) b1 b2 b3 b4,
    w1 <= b1
    -> w2 <= b2
    -> w3 <= b3
    -> w4 <= b4
    -> { b | w1 ^+ (w2 ^* w3) ^* w4 <= b }.    
  Proof.
    eexists.
    word_bound.
  Defined.

  Eval simpl in fun (w1 w2 w3 w4 : word n) (b1 b2 b3 b4 : N)
                    (H1 : w1 <= b1) (H2 : w2 <= b2) (H3 : w3 <= b3) (H4 : w4 <= b4) =>
                  projT1 (example1 H1 H2 H3 H4).

  Notation "$" := (natToWord _).

  Lemma example2 : forall (w1 w2 w3 w4 : word n) b1 b2 b3 b4,
    w1 <= b1
    -> w2 <= b2
    -> w3 <= b3
    -> w4 <= b4
    -> { b | w1 ^+ (w2 ^* $7 ^* w3) ^* w4 ^+ $8 ^+ w2 <= b }.
  Proof.
    eexists.
    word_bound.
  Defined.

  Eval simpl in fun (w1 w2 w3 w4 : word n) (b1 b2 b3 b4 : N)
                    (H1 : w1 <= b1) (H2 : w2 <= b2) (H3 : w3 <= b3) (H4 : w4 <= b4) =>
                  projT1 (example2 H1 H2 H3 H4).

  Lemma example3 : forall (w1 w2 w3 w4 : word n),
    w1 <= Npow2 3
    -> w2 <= Npow2 4
    -> w3 <= Npow2 8
    -> w4 <= Npow2 16
    -> { b | w1 ^+ (w2 ^* $7 ^* w3) ^* w4 ^+ $8 ^+ w2 <= b }.
  Proof.
    eexists.
    word_bound.
  Defined.

  Eval simpl in fun (w1 w2 w3 w4 : word n)
                    (H1 : w1 <= _) (H2 : w2 <= _) (H3 : w3 <= _) (H4 : w4 <= _) =>
                  projT1 (example3 H1 H2 H3 H4).


  Section MulmodExamples.

    Lemma example_and : forall x : word 32, wand x (NToWord 32 (N.ones 10)) <= 1023.
    Abort.
    
    Variable shiftrl : forall {l}, word l -> nat -> word l. (* "logical" aka "unsigned" bitshift *)
    Hypothesis shiftrl_spec : forall {l} (w : word l) (n:nat), wordToN (shiftrl w n) = N.shiftr (wordToN w) (N.of_nat n).

    Lemma example_shiftrl : forall x : word 32, shiftrl x 30 <= 3.
    Abort.

    Lemma example_shiftrl2 : forall x : word 32, x <= 1023 -> shiftrl x 5 <= 31.
    Abort.
    
    Variable f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 : word 32.
    Variable g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : word 32.
    Hypothesis Hf0 : f0 <= 2^26.
    Hypothesis Hf1 : f1 <= 2^25.
    Hypothesis Hf2 : f2 <= 2^26.
    Hypothesis Hf3 : f3 <= 2^25.
    Hypothesis Hf4 : f4 <= 2^26.
    Hypothesis Hf5 : f5 <= 2^25.
    Hypothesis Hf6 : f6 <= 2^26.
    Hypothesis Hf7 : f7 <= 2^25.
    Hypothesis Hf8 : f8 <= 2^26.
    Hypothesis Hf9 : f9 <= 2^25.
    Hypothesis Hg0 : g0 <= 2^26.
    Hypothesis Hg1 : g1 <= 2^25.
    Hypothesis Hg2 : g2 <= 2^26.
    Hypothesis Hg3 : g3 <= 2^25.
    Hypothesis Hg4 : g4 <= 2^26.
    Hypothesis Hg5 : g5 <= 2^25.
    Hypothesis Hg6 : g6 <= 2^26.
    Hypothesis Hg7 : g7 <= 2^25.
    Hypothesis Hg8 : g8 <= 2^26.
    Hypothesis Hg9 : g9 <= 2^25.
    
    Lemma example_mulmod_s_ppt : { b | f0 ^* g0  <= b}.
    Abort.

    Lemma example_mulmod_s_pp :  { b | f0 ^* g0 ^+  $19 ^* (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+ f2 ^* g8 ^+  f1 ^* g9 ^* $2) <= b}.
    Abort.

    Lemma example_mulmod_s_pp_shiftrl :
        { b | shiftrl (f0 ^* g0 ^+  $19 ^* (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+ f2 ^* g8 ^+  f1 ^* g9 ^* $2)) 26 <= b}.
    Abort.

    Lemma example_mulmod_u_fg1 :  { b |
          (let y : word 32 := (* the type declarations on the let-s make type inference not take forever *)
             (f0 ^* g0 ^+
              $19 ^*
              (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+ f2 ^* g8 ^+
               f1 ^* g9 ^* $2)) in
           let y0 : word 32 :=
             (shiftrl y 26 ^+
              (f1 ^* g0 ^+ f0 ^* g1 ^+
               $19 ^* (f9 ^* g2 ^+ f8 ^* g3 ^+ f7 ^* g4 ^+ f6 ^* g5 ^+ f5 ^* g6 ^+ f4 ^* g7 ^+ f3 ^* g8 ^+ f2 ^* g9))) in
           let y1 : word 32 :=
             (shiftrl y0 25 ^+
              (f2 ^* g0 ^+ f1 ^* g1 ^* $2 ^+ f0 ^* g2 ^+
               $19 ^* (f9 ^* g3 ^* $2 ^+ f8 ^* g4 ^+ f7 ^* g5 ^* $2 ^+ f6 ^* g6 ^+ f5 ^* g7 ^* $2 ^+ f4 ^* g8 ^+ f3 ^* g9 ^* $2))) in
           let y2 : word 32 :=
             (shiftrl y1 26 ^+
              (f3 ^* g0 ^+ f2 ^* g1 ^+ f1 ^* g2 ^+ f0 ^* g3 ^+
               $19 ^* (f9 ^* g4 ^+ f8 ^* g5 ^+ f7 ^* g6 ^+ f6 ^* g7 ^+ f5 ^* g8 ^+ f4 ^* g9))) in
           let y3 : word 32 :=
             (shiftrl y2 25 ^+
              (f4 ^* g0 ^+ f3 ^* g1 ^* $2 ^+ f2 ^* g2 ^+ f1 ^* g3 ^* $2 ^+ f0 ^* g4 ^+
               $19 ^* (f9 ^* g5 ^* $2 ^+ f8 ^* g6 ^+ f7 ^* g7 ^* $2 ^+ f6 ^* g8 ^+ f5 ^* g9 ^* $2))) in
           let y4 : word 32 :=
             (shiftrl y3 26 ^+
              (f5 ^* g0 ^+ f4 ^* g1 ^+ f3 ^* g2 ^+ f2 ^* g3 ^+ f1 ^* g4 ^+ f0 ^* g5 ^+
               $19 ^* (f9 ^* g6 ^+ f8 ^* g7 ^+ f7 ^* g8 ^+ f6 ^* g9))) in
           let y5 : word 32 :=
             (shiftrl y4 25 ^+
              (f6 ^* g0 ^+ f5 ^* g1 ^* $2 ^+ f4 ^* g2 ^+ f3 ^* g3 ^* $2 ^+ f2 ^* g4 ^+ f1 ^* g5 ^* $2 ^+ f0 ^* g6 ^+
               $19 ^* (f9 ^* g7 ^* $2 ^+ f8 ^* g8 ^+ f7 ^* g9 ^* $2))) in
           let y6 : word 32 :=
             (shiftrl y5 26 ^+
              (f7 ^* g0 ^+ f6 ^* g1 ^+ f5 ^* g2 ^+ f4 ^* g3 ^+ f3 ^* g4 ^+ f2 ^* g5 ^+ f1 ^* g6 ^+ f0 ^* g7 ^+
               $19 ^* (f9 ^* g8 ^+ f8 ^* g9))) in
           let y7 : word 32 :=
             (shiftrl y6 25 ^+
              (f8 ^* g0 ^+ f7 ^* g1 ^* $2 ^+ f6 ^* g2 ^+ f5 ^* g3 ^* $2 ^+ f4 ^* g4 ^+ f3 ^* g5 ^* $2 ^+ f2 ^* g6 ^+ f1 ^* g7 ^* $2 ^+
               f0 ^* g8 ^+ $19 ^* f9 ^* g9 ^* $2)) in
           let y8 : word 32 :=
             (shiftrl y7 26 ^+
              (f9 ^* g0 ^+ f8 ^* g1 ^+ f7 ^* g2 ^+ f6 ^* g3 ^+ f5 ^* g4 ^+ f4 ^* g5 ^+ f3 ^* g6 ^+ f2 ^* g7 ^+ f1 ^* g8 ^+
               f0 ^* g9)) in
           let y9 : word 32 :=
             ($19 ^* shiftrl y8 25 ^+
              wand
                (f0 ^* g0 ^+
                 $19 ^*
                 (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+
                  f2 ^* g8 ^+ f1 ^* g9 ^* $2)) (@NToWord 32 (N.ones 26%N))) in
           let fg1 : word 32 := (shiftrl y9 26 ^+
            wand
              (shiftrl y 26 ^+
               (f1 ^* g0 ^+ f0 ^* g1 ^+
                $19 ^* (f9 ^* g2 ^+ f8 ^* g3 ^+ f7 ^* g4 ^+ f6 ^* g5 ^+ f5 ^* g6 ^+ f4 ^* g7 ^+ f3 ^* g8 ^+ f2 ^* g9)))
              (@NToWord 32 (N.ones 26%N))) in
           fg1) <= b }.
    Abort.

    Require Import ZArith.
    Variable shiftra : forall {l}, word l -> nat -> word l. (* "arithmetic" aka "signed" bitshift *)
    Hypothesis shiftra_spec : forall {l} (w : word l) (n:nat), wordToZ (shiftra w n) = Z.shiftr (wordToZ w) (Z.of_nat n).

    Lemma example_shiftra : forall x : word 4, shiftra x 2 <= 15.
    Abort.

    Lemma example_shiftra : forall x : word 4, x <= 7 -> shiftra x 2 <= 1.
    Abort.

    Lemma example_mulmod_s_pp_shiftra :
        { b | shiftra (f0 ^* g0 ^+  $19 ^* (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+ f2 ^* g8 ^+  f1 ^* g9 ^* $2)) 26 <= b}.
    Abort.
  End MulmodExamples.
End BoundedWord.
