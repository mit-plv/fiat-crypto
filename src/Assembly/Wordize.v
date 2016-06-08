
Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow Compare_dec.
Require Import FunctionalExtensionality.

Hint Rewrite wordToN_nat Nat2N.inj_add N2Nat.inj_add
             Nat2N.inj_mul N2Nat.inj_mul Npow2_nat : N.

Delimit Scope wordize_scope with wordize.
Open Scope wordize_scope.

Notation "& x" := (wordToN x) (at level 30) : wordize_scope.
Notation "** x" := (NToWord _ x) (at level 30) : wordize_scope.
Notation "$ x" := (natToWord x) (at level 30) : wordize_scope.

Section Definitions.

  Definition take (k n: nat) (p: (k <= n)%nat) (w: word n): word k.
    replace n with (k + (n - k)) in * by abstract omega.
    refine (split1 k _ w).
  Defined.

  Definition shiftr {n} (w: word n) (k: nat): word n.
    destruct (le_dec k n).

    - replace n with (k + (n - k)) in * by abstract intuition.
        refine (sext (take k (k + (n - k)) l w) _).

    - exact (wzero n).
  Defined.

  Definition mask {n} (m: nat) (w: word n): word n.
    destruct (le_dec m n).

    - replace n with (m + (n - m)) in * by (abstract intuition).
        refine (w ^& (zext (wones m) (n - m))).

    - exact w.
  Defined.

End Definitions.

Section WordizeUtil.

  Lemma to_nat_lt: forall x b, (x < b)%N <-> (N.to_nat x < N.to_nat b)%nat.
  Proof. (* via Nat2N.inj_compare *) Admitted.

  Lemma of_nat_lt: forall x b, (x < b)%nat <-> (N.of_nat x < N.of_nat b)%N.
  Proof. (* via N2Nat.inj_compare *) Admitted.

  Lemma Npow2_spec : forall n, Npow2 n = N.pow 2 (N.of_nat n).
  Proof. (* by induction and omega *) Admitted.

  Lemma NToWord_wordToN: forall sz x, NToWord sz (wordToN x) = x.
  Proof.
    intros.
    rewrite NToWord_nat.
    rewrite wordToN_nat.
    rewrite Nat2N.id.
    rewrite natToWord_wordToNat.
    intuition.
  Qed.

  Lemma wordToN_NToWord: forall sz x, (x < Npow2 sz)%N -> wordToN (NToWord sz x) = x.
  Proof.
    intros.
    rewrite NToWord_nat.
    rewrite wordToN_nat.
    rewrite <- (N2Nat.id x).
    apply Nat2N.inj_iff.
    rewrite Nat2N.id.
    apply natToWord_inj with (sz:=sz);
        try rewrite natToWord_wordToNat;
        intuition.

    - apply wordToNat_bound.
    - rewrite <- Npow2_nat; apply to_nat_lt; assumption.
  Qed.

  Lemma word_size_bound : forall {n} (w: word n), (&w < Npow2 n)%N.
  Proof.
    intros; pose proof (wordToNat_bound w) as B;
        rewrite of_nat_lt in B;
        rewrite <- Npow2_nat in B;
        rewrite N2Nat.id in B;
        rewrite <- wordToN_nat in B;
        assumption.
  Qed.

  Lemma Npow2_gt0 : forall x, (0 < Npow2 x)%N.
  Proof.
    intros; induction x.

    - simpl; apply N.lt_1_r; intuition.

    - replace (Npow2 (S x)) with (2 * (Npow2 x))%N by intuition.
        apply (N.lt_0_mul 2 (Npow2 x)); left; split; apply N.neq_0_lt_0.

        + intuition; inversion H.

        + apply N.neq_0_lt_0 in IHx; intuition.
  Qed.

End WordizeUtil.

(** Wordization Lemmas **)

Section Wordization.

  Lemma wordize_plus: forall {n} (x y: word n) (b: N),
      (b <= Npow2 n)%N
    -> (&x < b)%N
    -> (&y < (Npow2 n - b))%N
    -> (&x + &y)%N = & (x ^+ y).
  Proof.
    intros.
    unfold wplus, wordBin.
    rewrite wordToN_NToWord; intuition.
    apply (N.lt_le_trans _ (b + &y)%N _).

    - apply N.add_lt_le_mono; try assumption; intuition.

    - replace (Npow2 n) with (b + Npow2 n - b)%N by nomega.
        replace (b + Npow2 n - b)%N with (b + (Npow2 n - b))%N by (
        replace (b + (Npow2 n - b))%N with ((Npow2 n - b) + b)%N by nomega;
        rewrite (N.sub_add b (Npow2 n)) by assumption;
        nomega).

        apply N.add_le_mono_l; try nomega.
        apply N.lt_le_incl; assumption.
  Qed.

  Lemma wordize_mult: forall {n} (x y: word n) (b: N),
      (1 < n)%nat -> (0 < b)%N
    -> (&x < b)%N
    -> (&y < (Npow2 n) / b)%N
    -> (&x * &y)%N = & (x ^* y).
  Proof.
    intros; unfold wmult, wordBin.
    rewrite wordToN_NToWord; intuition.
    apply (N.lt_le_trans _ (b * ((Npow2 n) / b))%N _).

    - apply N.mul_lt_mono; assumption.

    - apply N.mul_div_le; nomega.
  Qed.

  Lemma wordize_and: forall {n} (x y: word n),
    N.land (&x) (&y) = & (x ^& y).
  Proof.
    intros; pose proof (Npow2_gt0 n).
    pose proof (word_size_bound x).
    pose proof (word_size_bound y).

    induction n.

    - rewrite (shatter_word_0 x) in *.
        rewrite (shatter_word_0 y) in *.
        simpl; intuition.

    - rewrite (shatter_word x) in *.
        rewrite (shatter_word y) in *.
        induction (whd x), (whd y).

        + admit.
        + admit.
        + admit.
        + admit.
  Qed.

  Lemma wordize_shiftr: forall {n} (x: word n) (k: nat),
    (N.shiftr_nat (&x) k) = & (shiftr x k).
  Proof.
    intros.
    admit.
  Qed.

End Wordization.

Section Bounds.

  Theorem constant_bound_N : forall {n} (k: word n),
    (& k < & k + 1)%N.
  Proof. intros; nomega. Qed.

  Lemma let_bound : forall {n} (x: word n) (f: word n -> word n) xb fb,
      (& x < xb)%N
    -> (forall x', & x' < xb -> & (f x') < fb)%N
    -> ((let k := x in &(f k)) < fb)%N.
  Proof. intros; eauto. Qed.

  Definition Nlt_dec (x y: N): {(x < y)%N} + {(x >= y)%N}.
    refine (
      let c := N.compare x y in
      match c as c' return c = c' -> _ with
      | Lt => fun _ => left _
      | _ => fun _ => right _
      end eq_refl); admit.
  Defined.

  Theorem wplus_bound : forall {n} (w1 w2 : word n) b1 b2,
      (&w1 < b1)%N
    -> (&w2 < b2)%N
    -> (&(w1 ^+ w2) < b1 + b2)%N.
  Proof.
    intros.

    destruct (N.compare (b1 + b2)%N (Npow2 n));
      rewrite <- wordize_plus with (b := b1);
      try apply N.add_lt_mono;
      try assumption.

    - apply N.add_lt_mono; assumption.

    - admit. 
    - admit.

    - apply N.add_lt_mono; assumption.
    - apply N.add_lt_mono; assumption.

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

  Theorem shiftr_bound : forall (w : word n) b bits,
    w <= b
    -> shiftr w bits <= N.shiftr b (N.of_nat bits).
  Proof.
    admit.
  Qed.

  Theorem mask_bound : forall (w : word n) m,
    mask m w <= Npow2 m - 1.
  Proof.
    admit.
  Qed.

  Theorem mask_update_bound : forall (w : word n) b m,
    w <= b
    -> mask m w <= (N.min b (Npow2 m - 1)).
  Proof.
    admit.
  Qed.

End Bounds.

(** Wordization Tactics **)

Ltac wordize_ast :=
  repeat match goal with
  | [ H: (& ?x < ?b)%N |- context[((& ?x) + (& ?y))%N] ] => rewrite (wordize_plus x y b)
  | [ H: (& ?x < ?b)%N |- context[((& ?x) * (& ?y))%N] ] => rewrite (wordize_mult x y b)
  | [ |- context[N.land (& ?x) (& ?y)] ] => rewrite (wordize_and x y)
  | [ |- context[N.shiftr (& ?x) ?k] ] => rewrite (wordize_shiftr x k)
  | [ |- (_ < _ / _)%N ] => unfold N.div; simpl
  | [ |- context[Npow2 _] ] => simpl
  | [ |- (?x < ?c)%N ] => assumption
  | [ |- _ = _ ] => reflexivity
  end.

Ltac lt_crush := try abstract (clear; vm_compute; intuition).

(** Bounding Tactics **)

(** Examples **)

Module WordizationExamples.

  Lemma wordize_example0: forall (x y z: word 16),
    (wordToN x < 10)%N ->
    (wordToN y < 10)%N ->
    (wordToN z < 10)%N ->
    & (x ^* y) = (&x * &y)%N.
  Proof.
    intros.
    wordize_ast; lt_crush.
    transitivity 10%N; try assumption; lt_crush.
  Qed.

End WordizationExamples.