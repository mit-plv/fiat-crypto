
Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Compare_dec.
Require Import FunctionalExtensionality ProofIrrelevance.

Hint Rewrite wordToN_nat Nat2N.inj_add N2Nat.inj_add
             Nat2N.inj_mul N2Nat.inj_mul Npow2_nat : N.

Delimit Scope wordize_scope with wordize.
Open Scope wordize_scope.

Notation "& x" := (wordToN x) (at level 30) : wordize_scope.
Notation "** x" := (NToWord _ x) (at level 30) : wordize_scope.
Notation "$ x" := (natToWord x) (at level 30) : wordize_scope.

Section Definitions.
  Definition convS {A B: Set} (x: A) (H: A = B): B :=
    eq_rect A (fun B0 : Set => B0) x B H.

  Definition take {k n: nat} (p: (k <= n)%nat) (w: word n): word k.
    refine (split1 k (n - k) (convS w _)).
    abstract (replace n with (k + (n - k)) by omega; intuition).
  Defined.

  Definition extend {k n: nat} (p: (k <= n)%nat) (w: word k): word n.
    refine (convS (zext w (n - k)) _).
    abstract (replace (k + (n - k)) with n by omega; intuition).
  Defined.

  Definition shiftr {n} (w: word n) (k: nat): word n :=
    match (le_dec k n) with
    | left p => extend p (take p w)
    | right _ => wzero n
    end.

  Definition mask {n} (k: nat) (w: word n): word n :=
    match (le_dec k n) with
    | left p => w ^& (extend p (wones k))
    | right _ => w
    end.

End Definitions.

Section WordizeUtil.
  Lemma convS_id: forall A x p, x = (@convS A A x p).
  Proof.
    intros; unfold convS; vm_compute.
    replace p with (eq_refl A); intuition.
    apply proof_irrelevance.
  Qed.

  Lemma word_param_eq: forall n m, word n = word m -> n = m.
  Proof. (* TODO: How do we prove this *) Admitted. 

  Lemma word_conv_eq: forall {n m} (y: word m) p,
      &y = &(@convS (word m) (word n) y p).
  Proof.
    intros.
    revert p.
    destruct (Nat.eq_dec n m).

    - rewrite e; intros; apply f_equal; apply convS_id.

    - intros; contradict n0.
      apply word_param_eq; rewrite p; intuition.
  Qed.

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

  Lemma natToWord_convS: forall {n m} (x: word n) p,
      & x = & @convS (word n) (word m) x p.
  Proof. admit. Qed.

  Lemma natToWord_combine: forall {n} (x: word n) k,
      & x = & combine x (wzero k).
  Proof. admit. Qed.

  Lemma natToWord_split1: forall {n} (x: word n) p,
      & x = & split1 n 0 (convS x p).
  Proof. admit. Qed.

  Lemma extend_bound: forall k n (p: (k <= n)%nat) (w: word k),
    (& (extend p w) < Npow2 k)%N.
  Proof.
    intros.
    assert (n = k + (n - k)) by abstract omega.
    replace (& (extend p w)) with (& w); try apply word_size_bound.
    unfold extend.
    rewrite <- word_conv_eq.
    unfold zext.
    clear; revert w; induction (n - k).

    - intros.
      assert (word k = word (k + 0)) as Z by intuition.
      replace w with (split1 k 0 (convS w Z)).
      replace (wzero 0) with (split2 k 0 (convS w Z)).
      rewrite <- natToWord_split1 with (p := Z).
      rewrite combine_split.
      apply natToWord_convS.

      + admit.
      + admit.

    - intros; rewrite <- natToWord_combine; intuition.
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
      end eq_refl);
      abstract (unfold c in *; try first [
        apply N.compare_eq_iff in _H
      | apply N.compare_lt_iff in _H
      | pose proof (N.compare_antisym x y) as _H0;
        rewrite _H in _H0; simpl in _H0;
        apply N.compare_lt_iff in _H0 ]; nomega).
  Defined.

  Theorem wplus_bound : forall {n} (w1 w2 : word n) b1 b2,
      (&w1 < b1)%N
    -> (&w2 < b2)%N
    -> (&(w1 ^+ w2) < b1 + b2)%N.
  Proof.
    intros.

    destruct (Nlt_dec (b1 + b2)%N (Npow2 n));
      rewrite <- wordize_plus with (b := b1);
      try apply N.add_lt_mono;
      try assumption.

    (* A couple inequality subgoals *)
  Admitted.

  Theorem wmult_bound : forall {n} (w1 w2 : word n) b1 b2,
      (1 < n)%nat
    -> (&w1 < b1)%N
    -> (&w2 < b2)%N
    -> (&(w1 ^* w2) < b1 * b2)%N.
  Proof.
    intros.
    destruct (Nlt_dec (b1 * b2)%N (Npow2 n));
      rewrite <- wordize_mult with (b := b1);
      try apply N.mul_lt_mono;
      try assumption;
      try nomega.

    (* A couple inequality subgoals *)
  Admitted.

  Theorem shiftr_bound : forall {n} (w : word n) b bits,
      (&w <= b)%N
    -> (&(shiftr w bits) <= N.shiftr_nat b bits)%N.
  Proof.
    intros.
    rewrite <- wordize_shiftr.
    induction bits; unfold N.shiftr_nat in *; simpl; intuition.
    revert IHbits;
      generalize (nat_iter bits N.div2 (& w)),
                 (nat_iter bits N.div2 b);
      clear; intros x y H.

    admit. (* Monotonicity of N.div2 *)
  Qed.

  Theorem mask_bound : forall {n} (w : word n) m,
    (n > 1)%nat ->
    (&(mask m w) < Npow2 m)%N.
  Proof.
    intros.
    unfold mask in *; destruct (le_dec m n); simpl.

    - admit.

    - transitivity (Npow2 n); try assumption; try apply word_size_bound.
      replace m with (n + (m - n)) by intuition.
      replace (Npow2 n) with ((Npow2 n) * 1)%N by nomega.
      replace (Npow2 (n + (m - n)))
         with (Npow2 n * Npow2 (m - n))%N.

      + admit.

      + admit.
  Qed.

  Theorem mask_update_bound : forall {n} (w : word n) b m,
      (n > 1)%nat
    -> (&w < b)%N
    -> (&(mask m w) < (N.min b (Npow2 m)))%N.
  Proof.
    intros.
    pose proof (mask_bound w m H).
    assert (&(mask m w) < b)%N.

    - induction m.

      + replace (&(mask 0 w)) with 0%N by admit.
        admit.

      + induction (&w); intuition.

      induction n; rewrite (shatter_word w) in *;
        try inversion H; subst.

      + rewrite (shatter_word (wtl w)) in *.
        replace (wtl (wtl w)) with WO in * by admit.
        induction (whd w), (whd (wtl w)); simpl in *.
      +

    - unfold N.min; destruct (b ?= Npow2 m)%N;
        simpl; try assumption.
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
Ltac multi_apply0 A L := pose proof (L A).

Ltac multi_apply1 A L :=
  match goal with
  | [ H: A <= ?b |- _] => pose proof (L A b H)
  end.

Ltac multi_apply2 A B L :=
  match goal with
  | [ H1: A <= ?b1, H2: B <= ?b2 |- _] => pose proof (L A B b1 b2 H1 H2)
  end.

Ltac multi_recurse n T :=
  match goal with
  | [ H: T <= _ |- _] => idtac
  | _ =>
    is_var T;
    let T' := (eval cbv delta [T] in T) in multi_recurse n T';
    match goal with
    | [ H : T' <= ?x |- _ ] =>
    pose proof (H : T <= x)
    end

  | _ =>
    match T with
    | ?W1 ^+ ?W2 =>
      multi_recurse n W1; multi_recurse n W2;
      multi_apply2 W1 W2 (@wplus_bound n)

    | ?W1 ^* ?W2 =>
      multi_recurse n W1; multi_recurse n W2;
      multi_apply2 W1 W2 (@wmult_bound n)

    | mask ?m ?w =>
      multi_recurse n w;
      multi_apply1 w (fun b => @mask_update_bound n w b)

    | mask ?m ?w =>
      multi_recurse n w;
      pose proof (@mask_bound n w m)

    | ?x ^& (@NToWord _ (N.ones ?m)) =>
      multi_recurse n (mask (N.to_nat m) x);
      match goal with
      | [ H: (mask (N.to_nat m) x) <= ?b |- _] =>
        pose proof (@mask_wand n x m b H)
      end

    | shiftr ?w ?bits =>
      multi_recurse n w;
      match goal with
      | [ H: w <= ?b |- _] =>
        pose proof (@shiftr_bound n w b bits H)
      end

    | NToWord _ ?k => pose proof (@constant_bound_N n k)
    | natToWord _ ?k => pose proof (@constant_bound_nat n k)
    | ($ ?k) => pose proof (@constant_bound_nat n k)
    | _ => pose proof (@word_size_bound n T)
    end
  end.

Lemma unwrap_let: forall {n} (y: word n) (f: word n -> word n) (b: N),
    (let x := y in f x) <= b <-> let x := y in (f x <= b).
Proof. intuition. Qed.

Ltac multi_bound n :=
  match goal with
  | [|- let A := ?B in _] =>
    multi_recurse n B; intro; multi_bound n
  | [|- (let A := _ in _) <= _] =>
    apply unwrap_let; multi_bound n
  | [|- ?W <= _ ] =>
    multi_recurse n W
  end.

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