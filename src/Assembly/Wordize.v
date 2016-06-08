
Require Export Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits Nnat Pnat.
Require Import Arith Ring List Compare_dec Bool.
Require Import FunctionalExtensionality.

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

Definition even_dec (x: nat): {exists x', x = 2*x'} + {exists x', x = 2*x' + 1}.
  refine (if (bool_dec (odd x) true) then right _ else left _).

  - apply odd_spec in _H; destruct _H; exists x0. abstract intuition.
  - unfold odd in _H.
    assert (even x = true) by abstract (destruct (even x); intuition).
    apply even_spec in H; destruct H; exists x0; abstract intuition.
Defined.

Lemma testbit_spec: forall (n x y: nat), (x < pow2 n)%nat -> (y < pow2 n)%nat -> 
    (forall k, (k < n)%nat -> testbit x k = testbit y k) -> x = y.
Proof.
  intro n; induction n; intros. simpl in *; omega.
  destruct (even_dec x) as [px|px], (even_dec y) as [py|py];
    destruct px as [x' px], py as [y' py];
    rewrite px in *; rewrite py in *;
    clear x y px py;
    replace (pow2 (S n)) with (2 * (pow2 n)) in * by intuition;
    assert (x' < pow2 n)%nat by intuition;
    assert (y' < pow2 n)%nat by intuition.

  - apply Nat.mul_cancel_l; intuition.
    apply IHn; intuition.
    assert (S k < S n)%nat as Z by intuition.
    pose proof (H1 (S k) Z); intuition.
    repeat rewrite testbit_even_succ in H5; intuition.

  - assert (0 < S n)%nat as Z by intuition.
    apply (H1 0) in Z.
    rewrite testbit_even_0 in Z;
      rewrite testbit_odd_0 in Z;
      inversion Z.

  - assert (0 < S n)%nat as Z by intuition.
    apply (H1 0) in Z.
    rewrite testbit_even_0 in Z;
      rewrite testbit_odd_0 in Z;
      inversion Z.

  - apply Nat.add_cancel_r; apply Nat.mul_cancel_l; intuition.
    apply IHn; intuition.
    assert (S k < S n)%nat as Z by intuition.
    pose proof (H1 (S k) Z); intuition.
    repeat rewrite testbit_odd_succ in H5; intuition.
Qed. 

Inductive BinF := | binF: forall (a b c d: bool), BinF.

Definition applyBinF (f: BinF) (x y: bool) :=
  match f as f' return f = f' -> _ with
  | binF a b c d => fun _ =>
    if x
    then if y
      then a
      else b
    else if y
      then c
      else d
  end eq_refl.

Definition boolToBinF (f: bool -> bool -> bool): {g: BinF | f = applyBinF g}.
  intros; exists (binF (f true true) (f true false) (f false true) (f false false));
    abstract (
      apply functional_extensionality; intro x;
      apply functional_extensionality; intro y;
      destruct x, y; unfold applyBinF; simpl; intuition).
Qed.

Lemma testbit_odd_succ': forall x k, testbit (S (x * 2)) (S k) = testbit x k.
  intros.
  replace (S (x * 2)) with ((2 * x) + 1) by omega.
  apply testbit_odd_succ.
Qed. 

Lemma testbit_even_succ': forall x k, testbit (x * 2) (S k) = testbit x k.
  intros; replace (x * 2) with (2 * x) by omega; apply testbit_even_succ.
Qed. 

Lemma testbit_odd_zero': forall x, testbit (S (x * 2)) 0 = true.
  intros.
  replace (S (x * 2)) with ((2 * x) + 1) by omega.
  apply testbit_odd_0.
Qed. 

Lemma testbit_even_zero': forall x, testbit (x * 2) 0 = false.
  intros; replace (x * 2) with (2 * x) by omega; apply testbit_even_0.
Qed. 

Lemma testbit_bitwp: forall {n} (x y: word n) f k, (k < n)%nat ->
  testbit (wordToNat (bitwp f x y)) k = f (testbit (&x) k) (testbit (&y) k).
Proof.
  intros.

  pose proof (shatter_word x);
    pose proof (shatter_word y);
    simpl in *.

  induction n. inversion H. clear IHn; rewrite H0, H1; clear H0 H1; simpl.

  replace f with (applyBinF (proj1_sig (boolToBinF f))) in *
    by (destruct (boolToBinF f); simpl; intuition);
    generalize (boolToBinF f) as g; intro g;
    destruct g as [g pg]; simpl; clear pg f.

  revert x y H; generalize k n; clear k n; induction k, n;
    intros; try omega. 

  - destruct g as [a b c d], (whd x), (whd y);
      destruct a, b, c, d; unfold applyBinF in *; clear H;
      repeat rewrite testbit_odd_zero';
      repeat rewrite testbit_even_zero';
      reflexivity.

  - destruct g as [a b c d], (whd x), (whd y);
      destruct a, b, c, d; unfold applyBinF in *; clear H;
      repeat rewrite testbit_odd_zero';
      repeat rewrite testbit_even_zero';
      reflexivity.

  - assert (k < S n)%nat as HB by omega;
      pose proof (IHk n (wtl x) (wtl y) HB) as Z; clear HB IHk.

    assert (forall {m} (w: word (S m)),
      &w = if whd w
           then S (& wtl w * 2)
           else & wtl w * 2) as r0. {
      clear H Z x y; intros.
      pose proof (shatter_word w); simpl in H; rewrite H; clear H; simpl.
      destruct (whd w); intuition.
    } repeat rewrite <- r0 in Z; clear r0.

    assert (forall {m} (a b: word (S m)),
      & bitwp (applyBinF g) a b
         = if applyBinF g (whd a) (whd b)
           then S (& bitwp (applyBinF g) (wtl a) (wtl b) * 2)
           else & bitwp (applyBinF g) (wtl a) (wtl b) * 2) as r1. {
      clear H Z x y; intros.
      pose proof (shatter_word a); pose proof (shatter_word b);
        simpl in *; rewrite H; rewrite H0; clear H H0; simpl.
      destruct (applyBinF g (whd a) (whd b)); intuition.
    } repeat rewrite <- r1 in Z; clear r1.

    destruct g as [a b c d], (whd x), (whd y);
      destruct a, b, c, d; unfold applyBinF in *; clear H;
      repeat rewrite testbit_odd_succ';
      repeat rewrite testbit_even_succ';
      assumption.
Qed.

(* (forall k, testbit x k = testbit y k) <-> x = y. *)
Lemma wordize_and: forall {n} (x y: word n),
  (Nat.land (&x) (&y))%nat = & (x ^& y).
Proof.
  intros n x y.
  pose proof (pow2_gt0 n).
  assert (&x < pow2 n)%nat by (pose proof (word_size_bound x); intuition).
  assert (&y < pow2 n)%nat by (pose proof (word_size_bound y); intuition).
  apply (testbit_spec n).

  - induction n.

    + simpl in *; intuition.
      replace (&x) with 0 by intuition.
      replace (&y) with 0 by intuition.
      simpl; intuition.

    + admit.

  - pose (word_size_bound (x ^& y)); intuition.

  - intros; rewrite land_spec.
    unfold wand; rewrite testbit_bitwp; intuition.
Qed.

Definition take (k n: nat) (p: (k <= n)%nat) (w: word n): word k.
  replace n with (k + (n - k)) in * by abstract omega.
  refine (split1 k _ w).
Defined.

Lemma wordize_shiftr: forall {n} (x: word n) (k: nat) (p: (k <= n)%nat),
  (Nat.shiftr (&x) k)%nat = & (take k n p x).
Proof.
  intros.
Admitted.
