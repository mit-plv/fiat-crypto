Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith NPeano List Sumbool.
Require Import QhasmCommon QhasmUtil Pseudo State Wordize.

Module Conversion.
  Import Pseudo ListNotations StateCommon.

  Hint Unfold ListState.setList ListState.getList ListState.getVar
       ListState.setCarry ListState.setCarryOpt ListState.getCarry
       ListState.getMem ListState.setMem overflows.

  Lemma pseudo_var: forall {w s n} x k v b p m c,
      nth_error x k = Some v
    -> pseudoEval (@PVar w s n b (exist _ k p)) (x, m, c) = Some ([v], m, c).
  Proof.
    intros; simpl; autounfold; simpl.
    destruct (nth_error x k); simpl; try inversion H; intuition.
  Qed.

  Lemma pseudo_mem: forall {w s} n v m c x name len index p0 p1,
      TripleM.find (w, name mod n, index mod len)%nat m = Some (@wordToN w v)
    -> pseudoEval (@PMem w s n len (indexize _ p0 name) (indexize _ p1 index)) (x, m, c) = Some ([v], m, c).
  Proof.
    intros; autounfold; simpl.
    unfold ListState.getMem; simpl.
    rewrite H; autounfold; simpl.
    rewrite NToWord_wordToN; intuition.
  Qed.

  Lemma pseudo_const: forall {w s n} x v m c,
      pseudoEval (@PConst w s n v) (x, m, c) = Some ([v], m, c).
  Proof. intros; simpl; intuition. Qed.

  Lemma pseudo_plus:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1,
      pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    -> pseudoEval (PBin n Add p) (x, m0, c0) =
        Some ([out0 ^+ out1], m1,
          Some (proj1_sig (bool_of_sumbool (overflows out0 out1)))).
  Proof.
    intros; simpl; rewrite H; simpl.

    pose proof (wordize_plus out0 out1).
    destruct (overflows out0 out1); autounfold; simpl; try rewrite H0;
      try rewrite <- (@Npow2_ignore w (out0 ^+ out1));
      try rewrite NToWord_wordToN; intuition.
  Qed.

  Lemma pseudo_plus:
    forall {w s n} (p: @Pseudo w s n 2) x out0 out1 m0 m1 c0 c1 op,
      op ⋄ Add
    → pseudoEval p (x, m0, c0) = Some ([out0; out1], m1, c1)
    → pseudoEval (PBin n op p) (x, m0, c0) =
        Some ([out0 ^+ out1], m1,
          Some (proj1_sig (bool_of_sumbool (overflows out0 out1)))).
  Proof.
    intros; simpl; rewrite H; simpl.

    pose proof (wordize_plus out0 out1).
    destruct (overflows out0 out1); autounfold; simpl; try rewrite H0;
      try rewrite <- (@Npow2_ignore w (out0 ^+ out1));
      try rewrite NToWord_wordToN; intuition.
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

  Program Definition ex0: Program Unary32 := ($0 :-: $0)%p.

  Eval vm_compute in (run ex0 [natToWord _ 7]).

End Conversion.

