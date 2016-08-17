Require Export Bedrock.Word Bedrock.Nomega.
Require Import Coq.NArith.NArith Coq.Numbers.Natural.Peano.NPeano Coq.Lists.List Coq.Bool.Sumbool Coq.Arith.Compare_dec Coq.omega.Omega.
Require Import Crypto.Assembly.QhasmCommon Crypto.Assembly.QhasmEvalCommon Crypto.Assembly.QhasmUtil Crypto.Assembly.Pseudo Crypto.Assembly.State.
Require Export Crypto.Assembly.Wordize Crypto.Assembly.Listize.
Require Export Crypto.Assembly.Pseudo Crypto.Assembly.WordizeUtil.
Require Export Crypto.Util.FixCoqMistakes.

Import Pseudo ListNotations StateCommon EvalUtil ListState.

Section Conversion.

  Hint Unfold setList getList getVar setCarry setCarryOpt getCarry
       getMem setMem overflows ensureLength evalCarryOp.

  Lemma eval_in_length: forall {w s n m} p x M c x' M' c',
      @pseudoEval n m w s p (x, M, c) = Some (x', M', c')
    -> Datatypes.length x = n.
  Proof.
    intros until c'; intro H; autounfold.

    destruct (Nat.eq_dec (Datatypes.length (getList (x, M, c))) n)
      as [Hn|Hn].

    - intuition.
    - assert (pseudoEval p (x, M, c) = None) as H0.
      induction p; simpl; unfold ensureLength;
        destruct (Nat.eq_dec _ n);
        simpl; intuition.
      rewrite H in H0; inversion H0.
  Qed.

  Set Printing Universes.
  Lemma pseudo_var: forall {w s n} b k x v m m' c c',
      (k < n)%nat -> m = m' -> c = c' -> Datatypes.length x = n
    -> nth_error x k = Some v
    -> pseudoEval (@PVar w s n b (indexize k)) (x, m, c) =
        Some ([v], m', c').
  Proof.
    intros until c'.
    intros B r0 r1 H H0; rewrite r0, r1.

    autounfold; simpl; unfold indexize;
      autounfold; unfold getList; simpl;
      rewrite H.

    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity).

    destruct (le_dec n 0).

    - replace k with 0 in * by omega.
      autounfold; simpl in *.
      rewrite H0; simpl; intuition.

    - autounfold; simpl.
      replace (k mod n) with k.

      + rewrite H0; simpl; reflexivity.

      + revert B; clear; intro B.
        assert (n <> 0) as NZ by omega.
        pose proof (Nat.div_mod k n NZ).
        replace (k mod n) with (k - n * (k / n)) by omega.
        rewrite (Nat.div_small k n); omega.
  Qed.

  Lemma pseudo_mem: forall {w s} n v m c x name len index,
      Datatypes.length x = n
    -> TripleM.find (w, name mod n, index mod len)%nat m = Some (@wordToN w v)
    -> pseudoEval (@PMem w s n len (indexize name) (indexize index)) (x, m, c) = Some ([v], m, c).
  Proof.
    intros until index; intros H H0; autounfold; simpl.
    unfold indexize.
    destruct (le_dec n 0), (le_dec len 0); try omega;
      autounfold; unfold getList; simpl; rewrite H;
      destruct (Nat.eq_dec n n) as [C|C];
        try (contradict C; reflexivity);
      try replace n with 0 in * by omega;
      try replace len with 0 in * by omega;
      simpl in H0; try rewrite H0; simpl;
      try rewrite NToWord_wordToN;
      reflexivity.
  Qed.

  Lemma pseudo_const: forall {w s n} x v m c,
      Datatypes.length x = n
    -> pseudoEval (@PConst w s n v) (x, m, c) = Some ([v], m, c).
  Proof.
    intros; unfold pseudoEval, ensureLength; autounfold; simpl.
    rewrite H.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity);
      reflexivity.
  Qed.

  Lemma pseudo_plus:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1,
      pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PBin n IAdd p) (x, m0, c0) =
        Some ([out0 ^+ out1], m1,
          Some (proj1_sig (bool_of_sumbool
               (overflows w (&out0 + &out1)%N)%w))).
  Proof.
    intros until c1; intro H; simpl; rewrite H; simpl.

    autounfold; unfold getList; simpl;
      apply eval_in_length in H.

    destruct (Nat.eq_dec (Datatypes.length x) n);
      destruct (Nge_dec _ _);
      try rewrite NToWord_wordToN; simpl; intuition.
  Qed.

  Lemma pseudo_bin:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1 op,
      op <> IAdd
    -> pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PBin n op p) (x, m0, c0) =
        Some ([fst (evalIntOp op out0 out1)], m1, c1).
  Proof.
    intros until op; intros H H0; simpl; rewrite H0; simpl.

    autounfold; unfold getList; induction op;
      try (contradict H; reflexivity);
      unfold evalIntOp; autounfold; simpl;

      apply eval_in_length in H0;
      destruct (Nat.eq_dec (Datatypes.length x) n);
      intuition.
  Qed.

  Lemma pseudo_and:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1,
      pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PBin n IAnd p) (x, m0, c0) =
        Some ([out0 ^& out1], m1, c1).
  Proof.
    intros.
    replace (out0 ^& out1) with (fst (evalIntOp IAnd out0 out1)).
    - eapply pseudo_bin; try assumption.
      intro Z; inversion Z.

    - unfold evalIntOp; simpl; intuition.
  Qed.

  Lemma pseudo_awc:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c,
      pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, Some c)
    -> pseudoEval (PCarry n AddWithCarry p) (x, m0, c0) =
        Some ([addWithCarry out0 out1 c], m1,
          Some (proj1_sig (bool_of_sumbool (overflows w
          (&out0 + &out1 + (if c then 1 else 0))%N)%w))).
  Proof.
    intros until c; intro H; simpl; rewrite H; simpl.
    unfold addWithCarry, evalCarryOp.

    autounfold; unfold getList; simpl;
      apply eval_in_length in H;
      rewrite H;
      destruct (Nat.eq_dec n n) as [C|C];
        try (contradict C; reflexivity);
      simpl.

    destruct (Nge_dec _ _) as [g|g]; simpl;
      repeat f_equal.
  Qed.

  Lemma pseudo_shiftr:
    forall {w s n} (p: @Pseudo w s n 1) x out m0 m1 c0 c1 k,
      pseudoEval p (x, m0, c0) = Some ([out], m1, c1)
    -> pseudoEval (PShift n Shr k p) (x, m0, c0) =
        Some ([shiftr out k], m1, c1).
  Proof.
    intros; simpl; autounfold; unfold getList; simpl.
    rewrite H; apply eval_in_length in H; rewrite H; simpl.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity).

    rewrite wordize_shiftr; rewrite NToWord_wordToN; intuition.
  Qed.

  Lemma pseudo_cons:
    forall {w s n m} (p0: @Pseudo w s n 1) (p1: @Pseudo w s n m)
        input x xs m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some ([x], m1, c1)
    -> pseudoEval p1 (input, m1, c1) = Some (xs, m2, c2)
    -> pseudoEval (@PCons w s _ _ p0 p1) (input, m0, c0) = Some (x :: xs, m2, c2).
  Proof.
    intros until c2; intros H H0; simpl.

    rewrite H; autounfold; unfold getList; simpl.
    rewrite H0; apply eval_in_length in H0; rewrite H0.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity).
    simpl; reflexivity.
  Qed.

  Lemma pseudo_let:
    forall {w s n k m} (p0: @Pseudo w s n k) (p1: @Pseudo w s (n + k) m)
      input out0 out1 m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some (out0, m1, c1)
    -> pseudoEval p1 (input ++ out0, m1, c1) = Some (out1, m2, c2)
    -> pseudoEval (@PLet w s n k m p0 p1) (input, m0, c0) =
        Some (out1, m2, c2).
  Proof.
    intros; autounfold; simpl.
    rewrite H; autounfold; unfold getList; simpl.
    rewrite H0; apply eval_in_length in H; rewrite H.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl;
      reflexivity.
  Qed.

  Lemma pseudo_let_var:
    forall {w s n k m} (p0: @Pseudo w s n k) (p1: @Pseudo w s (n + k) m)
      input a f m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some ([a], m1, c1)
    -> pseudoEval p1 (input ++ [a], m1, c1) = Some (f (nth n (input ++ [a]) (wzero _)), m2, c2)
    -> pseudoEval (@PLet w s n k m p0 p1) (input, m0, c0) =
        Some (Let_In a f, m2, c2).
  Proof.
    intros; unfold Let_In; cbv zeta.
    eapply pseudo_let; try eassumption.
    replace (f a) with (f (nth n (input ++ [a]) (wzero w))); try assumption.
    apply f_equal.
    assert (Datatypes.length input = n) as L by (
      eapply eval_in_length; eassumption).

    rewrite app_nth2; try rewrite L; try omega.
    replace (n - n) with 0 by omega; simpl; intuition.
  Qed.

  Lemma pseudo_let_list:
    forall {w s n k m} (p0: @Pseudo w s n k) (p1: @Pseudo w s (n + k) m)
      input lst f m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some (lst, m1, c1)
    -> pseudoEval p1 (input ++ lst, m1, c1) = Some (f lst, m2, c2)
    -> pseudoEval (@PLet w s n k m p0 p1) (input, m0, c0) =
        Some (Let_In lst f, m2, c2).
  Proof.
    intros; unfold Let_In; cbv zeta.
    eapply pseudo_let; try eassumption.
  Qed.

  Lemma pseudo_mult_single_let:
    forall {w s n m} (p0: @Pseudo w s n 2)
                (p1: @Pseudo w s (n + 2) m)
        out0 out1 f x m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval p1 (x ++ [out0 ^* out1; multHigh out0 out1], m1, c1) =
        Some (f (nth n (x ++ [out0 ^* out1; multHigh out0 out1]) (wzero _)), m2, c2)
    -> pseudoEval (@PLet w s n 2 m (PDual n Mult p0) p1) (x, m0, c0) =
      Some (Let_In (out0 ^* out1) f, m2, c2).
  Proof.
    intros until c2; intros H H0; simpl;
      rewrite H; autounfold; unfold getList; simpl.

    apply eval_in_length in H; rewrite H.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl.
    rewrite H0; unfold Let_In; simpl.

    replace (nth n (x ++ _) _) with (out0 ^* out1); try reflexivity.
    rewrite app_nth2; try rewrite H; try omega.
    replace (n - n) with 0 by omega.
    simpl; intuition.
  Qed.

  Lemma pseudo_mult_dual_let:
    forall {w s n m} (p0: @Pseudo w s n 2)
                (p1: @Pseudo w s (n + 2) m)
        out0 out1 f x m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval p1 (x ++ [out0 ^* out1; multHigh out0 out1], m1, c1) =
      Some (f (nth n (x ++ [out0 ^* out1; multHigh out0 out1]) (wzero _))
              (nth (S n) (x ++ [out0 ^* out1; multHigh out0 out1]) (wzero _)),
            m2, c2)
    -> pseudoEval (@PLet w s n 2 m (PDual n Mult p0) p1) (x, m0, c0) =
      Some (Let_In (multHigh out0 out1) (fun x =>
            Let_In (out0 ^* out1) (fun y =>
            f y x)), m2, c2).
  Proof.
    intros until c2; intros H H0; simpl;
      rewrite H; autounfold; unfold getList; simpl.

    apply eval_in_length in H; rewrite H.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl.
    rewrite H0; unfold Let_In; simpl.


    replace (nth n (x ++ _) _) with (out0 ^* out1);
      try replace (nth (S n) (x ++ _) _) with (multHigh out0 out1);
      try reflexivity.

    - rewrite app_nth2; try rewrite H; try omega.
      replace (S n - n) with 1 by omega.
      simpl; intuition.

    - rewrite app_nth2; try rewrite H; try omega.
      replace (n - n) with 0 by omega.
      simpl; intuition.
  Qed.

  Lemma nth_error_default: forall {T} k (lst: list T),
    nth_error lst k = nth_default (@None T) (map (@Some T) lst) k.
  Proof.
    induction k, lst; intros; simpl;
      try rewrite IHk; unfold nth_default;
      simpl; try reflexivity.
  Qed.

  Lemma pseudo_mult_low:
    forall {w s n} (p0: @Pseudo w s n 2)
        out0 out1 x m0 m1 c0 c1,
      pseudoEval p0 (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (@PLet w s n 2 1 (PDual n Mult p0) (PVar (n + 2) None (indexize n))) (x, m0, c0) =
      Some ([out0 ^* out1], m1, c1).
  Proof.
    intros until c1; intro H.
    replace [out0 ^* out1] with (Let_In (out0 ^* out1) (fun x => [x])) by (cbv zeta; reflexivity).
    eapply pseudo_mult_single_let; try apply H.
    apply eval_in_length in H.
    apply pseudo_var; try reflexivity; try omega.

    - rewrite app_length; rewrite H; simpl; reflexivity.

    - rewrite nth_error_default.
      rewrite nth_default_eq.
      rewrite map_app.
      repeat rewrite app_nth2;
        try rewrite map_length;
        rewrite H; try omega.
      replace (n - n) with O by omega; simpl.
      reflexivity.
  Qed.

  Lemma pseudo_mult_high:
    forall {w s n} (p0: @Pseudo w s n 2)
        out0 out1 x m0 m1 c0 c1,
      pseudoEval p0 (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (@PLet w s n 2 1 (PDual n Mult p0) (PVar (n + 2) None (indexize (n + 1)))) (x, m0, c0) =
      Some ([multHigh out0 out1], m1, c1).
  Proof.
    intros until c1; intro H.
    replace [multHigh out0 out1] with (
      Let_In (multHigh out0 out1) (fun x =>
        Let_In (out0 ^* out1) (fun y => [x]))) by (cbv zeta; reflexivity).

    eapply pseudo_mult_dual_let; try apply H.
    apply eval_in_length in H.
    apply pseudo_var; try reflexivity; try omega.

    - rewrite app_length; rewrite H; simpl; reflexivity.

    - rewrite nth_error_default.
      rewrite nth_default_eq.
      rewrite map_app.
      repeat rewrite app_nth2;
        try rewrite map_length;
        rewrite H; try omega.
      replace (S n - n) with 1 by omega.
      replace (n + 1 - n) with 1 by omega.
      simpl; reflexivity.
  Qed.

  Lemma pseudo_if_left:
    forall {w s n m} (p0: @Pseudo w s n m) (p1: @Pseudo w s n m)
      input t (i0 i1: Index n) out0 out1 m0 m1 m2 c0 c1 c2,
      Datatypes.length input = n
    -> (i0 < n)%nat -> (i1 < n)%nat
    -> evalTest t (nth i0 input (wzero _)) (nth i1 input (wzero _)) = true
    -> pseudoEval p0 (input, m0, c0) = Some (out0, m1, c1)
    -> pseudoEval p1 (input, m0, c0) = Some (out1, m2, c2)
    -> pseudoEval (@PIf w s n m t i0 i1 p0 p1) (input, m0, c0) =
        Some (out0, m1, c1).
  Proof.
    intros until c2; intros L nn0 nn1 T H H0; simpl.
    rewrite H, H0; autounfold; unfold getList; simpl.
    rewrite L.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl.

    assert (nth_error input i0 <> None) as cc0. {
      rewrite nth_error_default, nth_default_eq.
      rewrite nth_indep with (d' := Some (wzero w)).

      - rewrite map_nth; intro Z; inversion Z.
      - rewrite map_length, L; assumption.
    }

    assert (nth_error input i1 <> None) as cc1. {
      rewrite nth_error_default, nth_default_eq.
      rewrite nth_indep with (d' := Some (wzero w)).

      - rewrite map_nth; intro Z; inversion Z.
      - rewrite map_length, L; assumption.
    }

    repeat rewrite <- nth_default_eq in T; unfold nth_default in T.
    induction (nth_error input i0),
              (nth_error input i1); simpl;
      try match goal with
      | [H: ?x <> ?x |- _] => contradict H; reflexivity
      end;
      try rewrite T; try reflexivity.
  Qed.

  Lemma pseudo_if_right:
    forall {w s n m} (p0: @Pseudo w s n m) (p1: @Pseudo w s n m)
      input t (i0 i1: Index n) out0 out1 m0 m1 m2 c0 c1 c2,
      Datatypes.length input = n
    -> (i0 < n)%nat -> (i1 < n)%nat
    -> evalTest t (nth i0 input (wzero _)) (nth i1 input (wzero _)) = false
    -> pseudoEval p0 (input, m0, c0) = Some (out0, m1, c1)
    -> pseudoEval p1 (input, m0, c0) = Some (out1, m2, c2)
    -> pseudoEval (@PIf w s n m t i0 i1 p0 p1) (input, m0, c0) =
        Some (out1, m2, c2).
  Proof.
    intros until c2; intros L nn0 nn1 T H H0; simpl.
    rewrite H, H0; autounfold; unfold getList; simpl.
    rewrite L.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl.

    assert (nth_error input i0 <> None) as cc0. {
      rewrite nth_error_default, nth_default_eq.
      rewrite nth_indep with (d' := Some (wzero w)).

      - rewrite map_nth; intro Z; inversion Z.
      - rewrite map_length, L; assumption.
    }

    assert (nth_error input i1 <> None) as cc1. {
      rewrite nth_error_default, nth_default_eq.
      rewrite nth_indep with (d' := Some (wzero w)).

      - rewrite map_nth; intro Z; inversion Z.
      - rewrite map_length, L; assumption.
    }

    repeat rewrite <- nth_default_eq in T; unfold nth_default in T.
    induction (nth_error input i0),
              (nth_error input i1); simpl;
      try match goal with
      | [H: ?x <> ?x |- _] => contradict H; reflexivity
      end;
      try rewrite T; try reflexivity.
  Qed.

  Lemma pseudo_mask:
    forall {w s n} (p: @Pseudo w s n 1) k x out m0 m1 c0 c1,
      (k <= w)%nat
    -> pseudoEval p (x, m0, c0) = Some ([out], m1, c1)
    -> pseudoEval (PBin n IAnd (PCons _ _ p
          (PConst _ (NToWord _ (N.ones (N.of_nat k)))))) (x, m0, c0) =
        Some ([mask k out], m1, c1).
  Proof.
    intros until c1; intros B H.
    pose proof (eval_in_length _ _ _ _ _ _ _ H).
    rewrite conv_mask.
    eapply pseudo_and.
    eapply pseudo_cons; try reflexivity; try apply H.
    eapply pseudo_const; try assumption.
    assumption.
  Qed.

  Lemma pseudo_funexp':
    forall {w s n} input f p e (m0 m1: TripleNMap) (c0 c1: option bool),
      Datatypes.length input = n
    -> (forall x m c, {st | pseudoEval p (x, m, c) = Some (setList (f x) st)})
    -> {st |
        pseudoEval (@PFunExp w s n p e) (input, m0, c0) =
          Some (setList (funexp f input e) st)}.
  Proof.
    intros until m0; intros m1 c0 c1 L H.
    autounfold; simpl; autounfold; unfold getList; simpl.
    rewrite L.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl.

    induction e; eexists; simpl.

    - transitivity (Some
       (input,
        snd (fst (input, m0, c0)),
        snd (input, m0, c0)));
      try reflexivity.

    - rewrite (proj2_sig IHe); simpl.
      rewrite
        (proj2_sig (H (funexp f input e)
           (snd (fst (proj1_sig IHe)))
           (snd (proj1_sig IHe)))).
      unfold setList; simpl.
      reflexivity.
  Qed.

  Lemma pseudo_funexp_O:
    forall {w s n} input p m c,
      Datatypes.length input = n
    -> pseudoEval (@PFunExp w s n p O) (input, m, c) =
        Some (input, m, c).
  Proof.
    intros until c; intros H.
    autounfold; simpl; autounfold; unfold getList; simpl; rewrite H.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl; reflexivity.
  Qed.

  Lemma pseudo_funexp_S:
    forall {w s n} e input p (m: TripleNMap) (c: option bool),
      Datatypes.length input = n
    -> pseudoEval (@PFunExp w s n p (S e)) (input, m, c) =
        omap (pseudoEval (@PFunExp w s n p e) (input, m, c)) (pseudoEval p).
  Proof.
    intros until c; intros H.
    autounfold; simpl; autounfold; unfold getList; simpl; rewrite H.
    destruct (Nat.eq_dec n n) as [C|C];
      try (contradict C; reflexivity); simpl; reflexivity.
  Qed.

  Lemma pseudo_funexp:
    forall {w s n} e input input' f p (m0 m1: TripleNMap) (c0 c1: option bool),
      Datatypes.length input = n
    -> (forall x m c x' m' c',
            pseudoEval p (x, m, c) = Some (x', m', c')
          -> pseudoEval p (x, m, c) = Some (f x, m', c'))
    -> pseudoEval (@PFunExp w s n p e) (input, m0, c0) = Some (input', m1, c1)
    -> pseudoEval (@PFunExp w s n p e) (input, m0, c0) =
        Some (funexp f input e, m1, c1).
  Proof.
    intros until c1; intros H Hf He.
    revert He H; revert input input' m0 m1 c0 c1.
    induction e; intros.

    - rewrite pseudo_funexp_O; try assumption.
      simpl in *; autounfold in He; unfold getList in He; simpl in He.
      rewrite H in He; destruct (Nat.eq_dec n n) as [C|C];
        try (contradict C; reflexivity).
      inversion He; subst.
      reflexivity.

    - rewrite (pseudo_funexp_S); try assumption.
      rewrite (pseudo_funexp_S) in He; try assumption.
      assert (exists a b c, pseudoEval (@PFunExp _ _ _ p e) (input, m0, c0) = Some (a, b, c)) as Z. {
        induction (pseudoEval (@PFunExp _ _ _ p e) (input, m0, c0)) as [z|].

        + exists (fst (fst z)); exists (snd (fst z)); exists (snd z).
          induction z as [z0 z2]; induction z0 as [z0 z1]; simpl; reflexivity.

        + simpl in He; inversion He.
      }

      destruct Z as [a Z], Z as [b Z], Z as [c Z].
      replace (funexp f input (S e)) with (f (funexp f input e)) by (simpl; intuition).

      erewrite <- Hf with (x' := input').

      + rewrite (IHe _ a _ b _ c); try assumption.
        simpl; reflexivity.

      + rewrite Z in *; simpl in He.
        rewrite <- He.
        f_equal.
        assert (Some (funexp f input e, b, c) = Some (a, b, c)) as HSome. {
          rewrite <- Z.
          rewrite (IHe _ a _ b _ c); try assumption.
          reflexivity.
        }

        inversion HSome; subst; intuition.
  Qed.
 
  Definition pseudeq {w s} (n m: nat) (f: list (word w) -> list (word w)) : Type := 
    {p: @Pseudo w s n m | forall x: (list (word w)),
      List.length x = n -> exists m' c',
      pseudoEval p (x, TripleM.empty N, None) = Some (f x, m', c')}.
End Conversion.

Ltac pseudo_step :=
  match goal with
  | [ |- pseudoEval ?p _ = Some ((
            Let_In (multHigh ?a ?b) (fun x =>
            Let_In (?a ^* ?b) (fun y => _))), _, _) ] =>
    is_evar p; eapply pseudo_mult_dual_let

  | [ |- pseudoEval ?p _ = Some (Let_In (?a ^* ?b) _, _, _) ] =>
    is_evar p; eapply pseudo_mult_single_let

  | [ |- pseudoEval ?p _ = Some ([?x ^& ?y], _, _) ] =>
    is_evar p; eapply pseudo_and

  | [ |- pseudoEval ?p _ = Some ([?x ^+ ?y], _, _) ] =>
    is_evar p; eapply pseudo_plus

  | [ |- pseudoEval ?p _ = Some ([?x ^* ?y], _, _) ] =>
    is_evar p; eapply pseudo_mult_low

  | [ |- pseudoEval ?p _ = Some ([multHigh ?x ?y], _, _) ] =>
    is_evar p; eapply pseudo_mult_high

  | [ |- pseudoEval ?p _ = Some ([mask ?k ?x], _, _) ] =>
    is_evar p; eapply pseudo_mask

  | [ |- pseudoEval ?p _ = Some (cons ?x (cons _ _), _, _) ] =>
    is_evar p; eapply pseudo_cons

  | [ |- pseudoEval ?p _ = Some ([natToWord _ ?x], _, _) ] =>
    is_evar p; eapply pseudo_const

  | [ |- pseudoEval ?p _ = Some ([NToWord _ (@wordToN _ ?x)], _, _) ] =>
    is_evar p; rewrite NToWord_wordToN

  | [ |- pseudoEval ?p _ = Some ([NToWord _ ?x], _, _) ] =>
    is_evar p; eapply pseudo_const

  | [ |- pseudoEval ?p _ = Some ((Let_In ?a ?f), _, _) ] =>
    is_evar p;
    match (type of a) with
    | list _ => eapply pseudo_let_list
    | word _ => eapply pseudo_let_var
    | (_ * _)%type => rewrite detuple_let
    end

  | [ |- @pseudoEval ?n _ _ _ ?P _ =
        Some ([nth ?i ?lst _], _, _) ] =>
    eapply (pseudo_var None i);
      try reflexivity; list_destruct;
      simpl; intuition

  | [ |- context [@NToWord ?x (@wordToN ?x _)]] =>
    rewrite NToWord_wordToN

  (* clean up generated inequalities *)
  | [ |- (_ <= _)%nat ] => vm_compute; omega
  | [ |- (_ < _)%nat ] => vm_compute; omega
  end.

Ltac pseudo_solve :=
  repeat eexists;
  autounfold; unfold getList;
  list_destruct;
  repeat pseudo_step;
  try reflexivity.
