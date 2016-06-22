Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith NPeano List Sumbool Compare_dec.
Require Import QhasmCommon QhasmEvalCommon QhasmUtil Pseudo State.
Require Export Wordize Vectorize.

Module Conversion.
  Import Pseudo ListNotations StateCommon EvalUtil ListState.

  Hint Unfold setList getList getVar setCarry setCarryOpt getCarry
       getMem setMem overflows.

  Lemma pseudo_var: forall {w s n} b k x v m c,
      (k < n)%nat
    -> nth_error x k = Some v
    -> pseudoEval (@PVar w s n b (indexize k)) (x, m, c) = Some ([v], m, c).
  Proof.
    intros; autounfold; simpl; unfold indexize.
    destruct (le_dec n 0); simpl. {
      replace k with 0 in * by omega; autounfold; simpl in *.
      rewrite H0; simpl; intuition.
    }

    replace (k mod n) with k by admit. (* TODO (rsloan): find lemma name *)

    autounfold; simpl.
    destruct (nth_error x k); simpl; try inversion H0; intuition.
  Qed.

  Lemma pseudo_mem: forall {w s} n v m c x name len index,
      TripleM.find (w, name mod n, index mod len)%nat m = Some (@wordToN w v)
    -> pseudoEval (@PMem w s n len (indexize name) (indexize index)) (x, m, c) = Some ([v], m, c).
  Proof.
    intros; autounfold; simpl.
    unfold indexize;
      destruct (le_dec n 0), (le_dec len 0);
      try replace n with 0 in * by intuition;
      try replace len with 0 in * by intuition;
      autounfold; simpl in *; rewrite H;
      autounfold; simpl; rewrite NToWord_wordToN;
      intuition.
  Qed.

  Lemma pseudo_const: forall {w s n} x v m c,
      pseudoEval (@PConst w s n v) (x, m, c) = Some ([v], m, c).
  Proof. intros; simpl; intuition. Qed.

  Lemma pseudo_plus:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1,
      pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PBin n Add p) (x, m0, c0) =
        Some ([out0 ^+ out1], m1,
          Some (proj1_sig (bool_of_sumbool
               (overflows w (&out0 + &out1)%N)%w))).
  Proof.
    intros; simpl; rewrite H; simpl.

    pose proof (wordize_plus out0 out1).
    destruct (overflows w _); autounfold; simpl; try rewrite H0;
      try rewrite <- (@Npow2_ignore w (out0 ^+ out1));
      try rewrite NToWord_wordToN; intuition.
  Qed.

  Lemma pseudo_bin:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1 op,
      op <> Add
    -> pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PBin n op p) (x, m0, c0) =
        Some ([fst (evalIntOp op out0 out1)], m1, c1).
  Proof.
    intros; simpl; rewrite H0; simpl.

    induction op;
      try (contradict H; reflexivity);
      unfold evalIntOp; autounfold; simpl;
      reflexivity.
  Qed.

  Lemma pseudo_and:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1,
      pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PBin n And p) (x, m0, c0) =
        Some ([out0 ^& out1], m1, c1).
  Proof.
    intros.
    replace (out0 ^& out1) with (fst (evalIntOp And out0 out1)).
    - apply pseudo_bin; intuition; inversion H0.
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
    intros; simpl; rewrite H; simpl.

    pose proof (wordize_awc out0 out1); unfold evalCarryOp.
    destruct (overflows w ((& out0)%w + (& out1)%w +
                           (if c then 1%N else 0%N)));
      autounfold; simpl; try rewrite H0; intuition.
  Qed.

  Lemma pseudo_shiftr:
    forall {w s n} (p: @Pseudo w s n 1) x out m0 m1 c0 c1 k,
      pseudoEval p (x, m0, c0) = Some ([out], m1, c1)
    -> pseudoEval (PShift n Shr k p) (x, m0, c0) =
        Some ([shiftr out k], m1, c1).
  Proof.
    intros; simpl; rewrite H; autounfold; simpl.
    rewrite wordize_shiftr; rewrite NToWord_wordToN; intuition.
  Qed.

  Lemma pseudo_mult:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1,
      pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PDual n Mult p) (x, m0, c0) =
      Some ([out0 ^* out1; multHigh out0 out1], m1, c1).
  Proof.
    intros; simpl; rewrite H; autounfold; simpl; intuition.
  Qed.

  Lemma pseudo_comb:
    forall {w s n a b} (p0: @Pseudo w s n a) (p1: @Pseudo w s n b)
      input out0 out1 m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some (out0, m1, c1)
    -> pseudoEval p1 (input, m1, c1) = Some (out1, m2, c2)
    -> pseudoEval (@PComb w s n _ _ p0 p1) (input, m0, c0) =
        Some (out0 ++ out1, m2, c2).
  Proof.
    intros; autounfold; simpl.
    rewrite H; autounfold; simpl.
    rewrite H0; autounfold; simpl; intuition.
  Qed.

  Lemma pseudo_cons:
    forall {w s n b} (p0: @Pseudo w s n 1) (p1: @Pseudo w s n b)
        (p2: @Pseudo w s n (S b)) input x xs m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some ([x], m1, c1)
    -> pseudoEval p1 (input, m1, c1) = Some (xs, m2, c2)
    -> p2 = (@PComb w s n _ _ p0 p1)
    -> pseudoEval p2 (input, m0, c0) = Some (x :: xs, m2, c2).
  Proof.
    intros.
    replace (x :: xs) with ([x] ++ xs) by (simpl; intuition).
    rewrite H1.
    apply (pseudo_comb p0 p1 input _ _ m0 m1 m2 c0 c1 c2); intuition.
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
    rewrite H; autounfold; simpl.
    rewrite H0; autounfold; simpl; intuition.
  Qed.

  Lemma pseudo_let_var:
    forall {w s n k m} (p0: @Pseudo w s n k) (p1: @Pseudo w s (n + k) m)
      input out0 out1 m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some ([a], m1, c1)
    -> pseudoEval p1 (input ++ [a], m1, c1) = Some (f (nth n (input ++ [a]) (wzero _)), m2, c2)
    -> pseudoEval (@PLet w s n k m p0 p1) (input, m0, c0) =
        Some (let x := a in f a, m2, c2).
  Proof.
    intros; cbv beta; simpl in *; apply pseudo_let.
  Qed.

  Lemma pseudo_let_list:
    forall {w s n k m} (p0: @Pseudo w s n k) (p1: @Pseudo w s (n + k) m)
      input out0 out1 m0 m1 m2 c0 c1 c2,
      pseudoEval p0 (input, m0, c0) = Some (lst, m1, c1)
    -> pseudoEval p1 (input ++ lst, m1, c1) = Some (f lst, m2, c2)
    -> pseudoEval (@PLet w s n k m p0 p1) (input, m0, c0) =
        Some (let x := lst in f a, m2, c2).
  Proof.
    intros; cbv beta; simpl in *; apply pseudo_let.
  Qed.

  Definition pseudeq {w s} (n m: nat) (f: list (word w) -> list (word w)) : Type := 
    {p: @Pseudo w s n m | forall x: (list (word w)),
      List.length x = n -> exists m' c',
      pseudoEval p (x, TripleM.empty N, None) = Some (f x, m', c')}.

  Ltac autodestruct :=
    repeat match goal with
    | [H: context[Datatypes.length (cons _ _)] |- _] => simpl in H
    | [H: context[Datatypes.length nil] |- _] => simpl in H
    | [H: S ?a = S ?b |- _] => inversion H; clear H
    | [H: (S ?a) = 0 |- _] => contradict H; intuition
    | [H: 0 = (S ?a) |- _] => contradict H; intuition
    | [H: 0 = 0 |- _] => clear H
    | [x: list ?T |- _] =>
      match goal with
      | [H: context[Datatypes.length x] |- _] => destruct x
      end
    end.

  Ltac pseudo_step :=
    match goal with
    | [ |- pseudoEval ?p _ = Some ([?x ^& ?y], _, _) ] =>
      is_evar p; eapply pseudo_and
    | [ |- pseudoEval ?p _ = Some ([?x ^+ ?y], _, _) ] =>
      is_evar p; eapply pseudo_plus
    | [ |- pseudoEval ?p _ = Some (cons ?x (cons _ _), _, _) ] =>
      is_evar p; eapply pseudo_cons; try reflexivity
    | [ |- pseudoEval ?p _ = Some ([natToWord _ ?x], _, _)%p ] =>
      is_evar p; eapply pseudo_const
    | [ |- @pseudoEval ?n _ _ _ ?P (?lst, _, _) =
            Some ([nth ?i ?lst _], _, _)%p ] =>
      eapply (pseudo_var None); simpl; intuition
    end.

  Ltac pseudo_solve :=
    repeat eexists;
    autounfold;
    autodestruct;
    repeat pseudo_step.

  Definition convert_example: @pseudeq 32 W32 1 1 (fun v =>
      let a := natToWord _ 1 in
      let b := nth 0 v (wzero _) in
      [a ^& b]).

    cbv zeta; pseudo_solve.

  Defined.

  Eval simpl in (proj1_sig convert_example).

End Conversion.

