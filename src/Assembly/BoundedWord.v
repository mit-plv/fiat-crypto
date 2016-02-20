
Require Import Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Compare_dec Arith.
Require Import ProofIrrelevance.
Require Import Ring.

Section BoundedWord.

  Delimit Scope Bounded_scope with bounded.

  Open Scope Bounded_scope.

  Variable n: nat.

  (* Word Operations *)

  Definition wshiftr (w: word n) (bits: nat): word n.
    destruct (le_dec bits n).

    - replace n with (bits + (n - bits)) in * by (abstract intuition).
      refine (zext (split1 bits (n - bits) w) (n - bits)).

    - exact w.

  Defined.

  Lemma wshiftr_spec: forall (w : word n) (bits: nat),
      wordToN (wshiftr w n) = N.shiftr (wordToN w) (N.of_nat n).
    intros.
    admit.
  Qed.

  Definition mask (m: nat) (w: word n): word n.
    destruct (le_dec m n).

    - replace n with (m + (n - m)) in * by (abstract intuition).
      refine (w ^& (zext (wones m) (n - m))).

    - exact w.

  Defined.

  (* First, we make our BoundedWord sigma type *)
  Definition wordLeN {n: nat} (a: word n) (b: N): Prop :=
    (wordToN a <= b)%N.

  Notation "A <= B" := (wordLeN A B) (at level 70) : Bounded_scope.

  Lemma le_ge : forall n m, (n <= m -> m >= n)%nat.
  Proof.
    intros; omega.
  Qed.

  Lemma ge_le : forall n m, (n >= m -> m <= n)%nat.
  Proof.
    intros; omega.
  Qed.

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

  Theorem shiftr_bound : forall (w1 w2 : word n) b1 b2,
    w1 <= b1
    -> w2 <= b2
    -> w1 ^* w2 <= b1 * b2.
  Proof.
  Qed.

  Theorem mask_bound : forall (w1 w2 : word n) b1 b2 a b,
    w1 <= b1
    -> w2 <= b2
    -> word (a + b) = word (n)
    -> w1 ^& zext (wones a) b <= zext (wones a) b.
  Proof.
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

(* Old lemmas that might end up being useful

  Lemma low_word_bound: forall n (x : word n), x >= 0.
    intros; unfold wordGeN;
      try (apply N.le_ge; apply N.le_0_l);
      rewrite wordToN_nat.
  Qed.

  Lemma high_word_bound: forall n (x : word n), x <= Npow2 n.
    intros; unfold wordLeN; rewrite wordToN_nat.

    assert (B := wordToNat_bound (x));
      rewrite <- Npow2_nat in B;
      apply nat_compare_lt in B.

    unfold N.le; intuition;
      rewrite N2Nat.inj_compare in H;
      rewrite Nat2N.id in H;
      rewrite B in H;
      inversion H.
  Qed.

  (* We start with the functions bound and unbound *)
  Definition bound {n: nat} (x: word n) :=
    boundBy x 0 (Npow2 n) (low_word_bound n x) (high_word_bound n x).

  Definition unbound {n: nat} {x: word n} (b: BoundOn x) := x.

  Lemma bound_inv: forall (n: nat) (x: word n), x = unbound (bound x).
    intros; unfold unbound; intuition.
  Qed.

  Lemma bound_eq: forall (n: nat) (a b: word n), unbound (bound a) = unbound (bound b) -> a = b.
    intros; repeat rewrite <- bound_inv in H; intuition.
  Qed.

  Definition above {n: nat} {x: word n} {low: N} (H: x >= low) :=
    boundBy x low (Npow2 n) H (high_word_bound n x).

  Definition below {n: nat} {x: word n} {high: N} (H: x <= high) :=
    boundBy x 0%N high (low_word_bound n x) H.

  Definition intersect {n: nat} {x: word n} (A: BoundOn x) (B: BoundOn x): BoundOn x :=
    match A with
    | boundBy low0 high0 lb0 hb0 =>
      match B with
      | boundBy low1 high1 lb1 hb1 =>
        match (low0 ?= low1)%N with
        | Eq => 
          match (high0 ?= high1)%N with
          | Eq =>  boundBy x low0 high0 lb0 hb0
          | Lt =>  boundBy x low0 high0 lb0 hb0
          | Gt =>  boundBy x low0 high1 lb0 hb1
          end
        | Gt => 
          match (high0 ?= high1)%N with
          | Eq =>  boundBy x low0 high0 lb0 hb0
          | Lt =>  boundBy x low0 high0 lb0 hb0
          | Gt =>  boundBy x low0 high1 lb0 hb1
          end
        | Lt => 
          match (high0 ?= high1)%N with
          | Eq =>  boundBy x low1 high0 lb1 hb0
          | Lt =>  boundBy x low1 high0 lb1 hb0
          | Gt =>  boundBy x low1 high1 lb1 hb1
          end
        end
      end
    end.

  Lemma replace_intersect {n: nat} {x: word n} (new: BoundOn x):
      forall (old: BoundOn x), old = intersect old new.
    intros; apply proof_irrelevance.
  Qed.

  Lemma wand_upper_l: forall (n: nat) (x a b: word n), x = wand a b -> x <= (2 * wordToN a)%N.
    admit.
  Qed.

  Lemma wand_upper_r: forall (n: nat) (x a b: word n), x = wand a b -> x <= (2 * wordToN b)%N.
    admit.
  Qed.


  Definition wand_bound_l {n: nat} {x a b: word n} (H: x = wand a b): BoundOn x :=
    below (wand_upper_l n x a b H).

  Definition wand_bound_r {n: nat} {x a b: word n} (H: x = wand a b): BoundOn x :=
    below (wand_upper_r n x a b H).

  Definition zero_dec (x: N): {(x = 0)%N} + {(x > 0)%N}.
    intros; unfold N.gt;
      assert (Z := N.compare_0_r x);
      assert ({x ?= 0 = Eq} + {x ?= 0 = Gt})%N by (induction (x ?= 0)%N; abstract intuition).

    inversion H.

    - left; abstract (
        unfold N.compare in H0;
        destruct x; inversion H0;
        simpl; intuition ).

    - abstract intuition.

  Qed.

  Lemma NToWord_inv: forall (n: nat) (x: word n), x = NToWord n (wordToN x).
    intros; rewrite NToWord_nat, wordToN_nat.
    rewrite Nat2N.id.
    rewrite natToWord_wordToNat; intuition.
  Qed.

  Lemma replace_zero: forall (n: nat) (x: word n), (x <= 0%N) -> x = NToWord n 0.
    intros; unfold wordLeN in H.

    assert (wordToN x = 0)%N by (
      induction (zero_dec (wordToN x));
      unfold N.le, N.gt in *; intuition).

    rewrite <- H0; rewrite <- NToWord_inv; intuition.
  Qed.

  Lemma Npow2_nonzero: forall (n: nat), (Npow2 n <> 0)%N.
    intros; induction n; simpl; intuition.

    - inversion H.
    - apply IHn; induction (Npow2 n); intuition.
      inversion H.
  Qed.

  Definition bplus {n: nat} {x y: word n} (A: BoundOn x) (B: BoundOn y): BoundOn (wplus x y).
    destruct A as [low0 high0 lb0 hb0], B as [low1 high1 lb1 hb1].

    induction (zero_dec high0), (zero_dec high1).

    - apply (boundBy (x ^+ y) 0%N 0%N); admit.

    - apply (boundBy (x ^+ y) low1 high1); admit.

    - apply (boundBy (x ^+ y) low0 high0); admit.

    - apply (boundBy (x ^+ y) (low0 + low1)%N (high0 + high1)%N); admit.
  Defined.

  Definition bmult {n: nat} {x y: word n} (A: BoundOn x) (B: BoundOn y): BoundOn (wmult x y).
    destruct A as [low0 high0 lb0 hb0], B as [low1 high1 lb1 hb1].
    apply (boundBy (x ^* y) (low0 * low1)%N (high0 * high1)%N); admit.
  Defined.

  Lemma bound_plus: forall (n: nat) (a b: word n), bound (wplus a b) = bplus (bound a) (bound b).
    intros; apply proof_irrelevance.
  Qed.

  Lemma bound_mult: forall (n: nat) (a b: word n), bound (wmult a b) = bmult (bound a) (bound b).
    intros; apply proof_irrelevance.
  Qed.

  Ltac convert_to_bounded :=
    apply bound_eq;
    repeat first [rewrite bound_plus | rewrite bound_mult].

  Ltac propagate_bounds :=
    match goal with
    | [H : ?x = wzero _ ^& _ |- _] =>
      rewrite (replace_intersect (wand_bound_l H) (bound x))
    | _ => fail
    end.

  Ltac match_match :=
    repeat (
      match goal with
      | [|- context[match (zero_dec ?x) with | _ => _ end]] => destruct (zero_dec x)
      | [|- context[match (N.compare ?x ?y) with | _ => _ end]] => destruct (N.compare x y)
      | [|- context[sumbool_ind _ _ _ (zero_dec ?x)]] => destruct (zero_dec x)
      end; subst).

  Ltac word_simpl :=
    repeat (
      match goal with
      | [|- context [unbound _]] => unfold unbound
      | [ H: (Npow2 ?x = 0)%N |- _] =>
        let Z := fresh in
          apply (Npow2_nonzero x) in H; intuition
      | [ H: (?x <= 0) |- _] =>
        unfold wordLeN in H;
        apply replace_zero in H;
        rewrite H; clear H
      | _ => fail 
      end; subst);
    simpl; intuition.

  Ltac unfold_ops := 
    unfold intersect, below, above,
           bound, bplus, bmult,
           wand_bound_l, wand_bound_r.

  Ltac bound_simpl:=
    convert_to_bounded;
    propagate_bounds;
    unfold_ops;
    repeat match_match;
    word_simpl.

  Lemma example_bound_simpl: forall (n: nat) (a b: word n),
    a = wand (wzero n) b -> b = a ^+ b.
  Proof.
    intros.
    convert_to_bounded.
    propagate_bounds.
    unfold_ops; simpl.
    match_match; word_simpl.
  Qed. *)

End BoundedWord.
