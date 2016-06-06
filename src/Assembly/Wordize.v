
Require Export Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits Nnat.
Require Import Arith Ring List Compare_dec.

Delimit Scope wordize_scope with wordize.
Local Open Scope wordize_scope.

Notation "& x" := (wordToNat x) (at level 30) : wordize_scope.

Lemma word_size_bound : forall {n} (w: word n),
  (& w <= pow2 n - 1)%nat.
Proof. intros; assert (B := wordToNat_bound w); omega. Qed.

Lemma pow2_gt0 : forall x, (pow2 x > 0)%nat.
Proof. intros; induction x; simpl; intuition. Qed.

Lemma wordize_plus: forall {n} (x y: word n) (b: nat),
    (&x <= b)%nat
  -> (&y <= (pow2 n - b - 1))%nat
  -> (&x + &y) = wordToNat (x ^+ y).
Proof.
  intros; unfold wplus, wordBin;
    repeat rewrite wordToN_nat in *;
    repeat rewrite NToWord_nat in *;
    rewrite <- Nat2N.inj_add; rewrite Nat2N.id.

  destruct (wordToNat_natToWord n (&x + &y)) as [k HW];
    destruct HW as [HW HK]; rewrite HW; clear HW.

  assert ((&x) + (&y) <= (pow2 n - 1))%nat by (
    pose proof (word_size_bound x);
    pose proof (word_size_bound y);
    omega).

  assert (k * pow2 n <= pow2 n - 1)%nat by omega.

  destruct k; subst; simpl in *; intuition;
    clear H H0 H1 HK;
    contradict H2.

  pose proof (pow2_gt0 n).
  induction k; simpl; intuition.
Qed.

Lemma wordize_mult: forall {n} (x y: word n) (b: nat),
    (1 <= n)%nat
  -> (&x <= b)%nat
  -> (&y <= (pow2 n - 1) / b)%nat
  -> (&x * &y)%nat = wordToNat (x ^* y).
Proof.
  intros; unfold wmult, wordBin;
    repeat rewrite wordToN_nat in *;
    repeat rewrite NToWord_nat in *;
    rewrite <- Nat2N.inj_mul; rewrite Nat2N.id.

  destruct (wordToNat_natToWord n (&x * &y)) as [k HW];
    destruct HW as [HW HK]; rewrite HW; clear HW.

  assert ((&x) * (&y) <= (pow2 n - 1))%nat. {
    destruct (Nat.eq_dec b 0); subst;
      try abstract (replace (&x) with 0 by intuition; omega).

    transitivity ((&x * (pow2 n - 1)) / b). {
      transitivity (&x * ((pow2 n - 1) / b)).

      + apply Nat.mul_le_mono_nonneg_l; intuition.
      + apply Nat.div_mul_le; assumption.
    }

    transitivity ((b * (pow2 n - 1)) / (b * 1)). {
      rewrite Nat.div_mul_cancel_l; intuition.
      rewrite Nat.div_1_r.
      apply Nat.div_le_upper_bound; intuition.
      apply Nat.mul_le_mono_pos_r; intuition.
      induction n; try inversion H; simpl; intuition.
      pose proof (pow2_gt0 n).
      omega.
    }

    rewrite Nat.div_mul_cancel_l; intuition.
    rewrite Nat.div_1_r; intuition.
  }

  assert (k * (pow2 n) <= pow2 n - 1)%nat by omega.

  induction k; try omega.

  assert (pow2 n - 1 < S k * (pow2 n))%nat. {
    destruct n; try inversion H; simpl; try omega.
    pose proof (pow2_gt0 n).
    induction k; try omega.
    
    transitivity (pow2 n + pow2 n + pow2 n); try omega.
    replace (pow2 n + (pow2 n + 0) + S k * _)
      with (pow2 n + pow2 n + pow2 n +
           (pow2 n + k * (pow2 n + (pow2 n + 0)))).
    apply Nat.lt_add_pos_r.
    apply Nat.add_pos_nonneg; try omega; intuition.

    simpl; omega.
  }

  contradict H3; omega.
Qed.

Ltac wordize :=
  repeat match goal with
   | [ |- context[?a - 1] ] =>
     let c := eval simpl in (a - 1) in
     replace (a - 1) with c by omega
  | [ |- vec (word ?n) O -> ?T] => apply (@lift0 T n)
  | [ |- vec (word ?n) ?m -> ?T] => apply (@liftS T n (m - 1))
  end.

Section Examples.
  Lemma vectorize_example: (vec (word 32) 2 -> word 32).
    vectorize; refine (@wplus 32).
  Qed.
End Examples.
