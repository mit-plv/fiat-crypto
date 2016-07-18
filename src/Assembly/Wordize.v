Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec.
Require Import Compare_dec Omega Bool.
Require Import FunctionalExtensionality ProofIrrelevance.
Require Import QhasmUtil QhasmEvalCommon.
Require Import WordizeUtil Bounds List Listize.

Import EvalUtil ListNotations.

Hint Rewrite wordToN_nat Nat2N.inj_add N2Nat.inj_add
             Nat2N.inj_mul N2Nat.inj_mul Npow2_nat : N.

Open Scope nword_scope.

Coercion ind : bool >-> N.

Section ToWord.
  Lemma wordize_plus: forall {n} (x y: word n),
      (&x + &y < Npow2 n)%N
    -> (&x + &y)%N = & (x ^+ y).
  Proof.
    intros n x y H.
    pose proof (word_size_bound x) as Hbx.
    pose proof (word_size_bound y) as Hby.

    unfold wplus, wordBin.
    rewrite wordToN_NToWord; intuition.
  Qed.

  Lemma wordize_awc: forall {n} (x y: word n) (c: bool),
      (&x + &y + c < Npow2 n)%N
    -> (&x + &y + c)%N = &(addWithCarry x y c).
  Proof.
    intros n x y c H.
    unfold wplus, wordBin, addWithCarry.
    destruct c; simpl in *.

    - replace 1%N with (wordToN (natToWord n 1)) in * by (
        rewrite wordToN_nat;
        rewrite wordToNat_natToWord_idempotent;
        nomega).

      rewrite <- N.add_assoc.
      rewrite wordize_plus; try nomega.
      rewrite wordize_plus; try nomega.

      + rewrite wplus_assoc.
        reflexivity.

      + apply (N.le_lt_trans _ (& x + & y + & natToWord n 1)%N _);
          try assumption.
        rewrite <- N.add_assoc.
        apply N.add_le_mono.

        * apply N.eq_le_incl; reflexivity.

        * apply plus_le.

    - rewrite wplus_comm.
      rewrite wplus_unit.
      rewrite N.add_0_r in *.
      apply wordize_plus; assumption.
  Qed.

  Lemma wordize_mult: forall {n} (x y: word n),
      (&x * &y < Npow2 n)%N
    -> (&x * &y)%N = &(x ^* y).
  Proof.
    intros n x y H.
    pose proof (word_size_bound x) as Hbx.
    pose proof (word_size_bound y) as Hby.

    unfold wmult, wordBin.
    rewrite wordToN_NToWord; intuition.
  Qed.

  Lemma wordize_shiftr: forall {n} (x: word n) (k: nat),
    (N.shiftr_nat (&x) k) = & (shiftr x k).
  Proof.
    intros n x k.
    unfold shiftr, extend, high.
    destruct (le_dec k n).

    - repeat first [
        rewrite wordToN_convS
      | rewrite wordToN_zext
      | rewrite wordToN_split2 ].
      rewrite <- Nshiftr_equiv_nat.
      reflexivity.

    - rewrite (wordToN_nat (wzero n)); unfold wzero.
      destruct (Nat.eq_dec n O); subst.

      + rewrite (shatter_word_0 x); simpl; intuition.
        rewrite <- Nshiftr_equiv_nat.
        rewrite N.shiftr_0_l.
        reflexivity.

      + rewrite wordToNat_natToWord_idempotent;
          try nomega.

        * pose proof (word_size_bound x).
          rewrite <- Nshiftr_equiv_nat.
          rewrite N.shiftr_eq_0_iff.
          destruct (N.eq_dec (&x) 0%N) as [E|E];
            try rewrite E in *;
            try abstract (left; reflexivity).

          right; split; try nomega.
          apply (N.le_lt_trans _ (N.log2 (Npow2 n)) _). {
            apply N.log2_le_mono.
            apply N.lt_le_incl.
            assumption.
          }

          rewrite Npow2_N.
          rewrite N.log2_pow2; try nomega.
          apply N_ge_0.

        * simpl; apply Npow2_gt0.
  Qed.

  Lemma conv_mask: forall {n} (x: word n) (k: nat),
    (k <= n)%nat ->
    mask k x = x ^& (NToWord _ (N.ones (N.of_nat k))).
  Proof.
    intros n x k H.
    apply NToWord_equal.

    rewrite <- (Nat2N.id k).
    rewrite mask_spec.
    apply N.bits_inj_iff; unfold N.eqf; intro m.
    rewrite N.land_spec.
    repeat rewrite wordToN_testbit.
    rewrite <- (N2Nat.id m).
    rewrite <- wordToN_wones.
    repeat rewrite wordToN_testbit.
    repeat rewrite N2Nat.id.
    rewrite <- wordToN_wones.

    assert (forall n (a b: word n) k,
        wbit (a ^& b) k = andb (wbit a k) (wbit b k)) as Hwand. {
      intros n0 a b.
      induction n0 as [|n1];
        shatter a; shatter b;
        simpl; try reflexivity.

      intro k0; induction k0 as [|k0];
        simpl; try reflexivity.

      fold wand.
      rewrite IHn1.
      reflexivity.
    }

    rewrite Hwand; clear Hwand.
    induction (wbit x (N.to_nat m));
      repeat rewrite andb_false_l;
      repeat rewrite andb_true_l;
      try reflexivity.

    repeat rewrite <- wordToN_testbit.
    rewrite wordToN_NToWord; try reflexivity.
    apply (N.lt_le_trans _ (Npow2 k) _).

    + apply word_size_bound.

    + apply Npow2_ordered.
      omega.
  Qed.
End ToWord.

Section WordEq.
  Definition wordeq {ins outs} (n: nat) (f: Curried N N ins outs) :=
    {g: Curried (word n) (word n) ins outs |
    forall (x: list (word n)), length x = ins ->
      (curriedToListF (wzero _) g) x =
        map (@NToWord n) ((curriedToListF 0%N f) (map (@wordToN n) x))}.

  Definition wordeq_kill_arg: forall {n ins outs} (f: Curried N N (S ins) outs),
    (forall x, wordeq n (f x)) -> wordeq n f.
  Proof. Admitted.

  Definition wordeq_break_cons: forall {n m} (a: N) (b: list N),
    @wordeq O 1 n [a] ->
    @wordeq O (S m) n b ->
    @wordeq O (S (S m)) n (cons a b).
  Proof. Admitted.

  Definition wordeq_nil: forall n, @wordeq O O n [].
  Proof. Admitted.

  Definition wordeq_cut_let: forall {n outs} (x: N) (f: N -> list N),
    @wordeq 1 outs n f -> @wordeq O 1 n [x] ->
    @wordeq O outs n (Let_In x f).
  Proof. Admitted.

  Definition wordeq_let_const: forall {T n outs} (a: T) (f: T -> list N),
    @wordeq O outs n (f a) -> @wordeq O outs n (Let_In a f).
  Proof. Admitted.

  Definition wordeq_debool_andb: forall {n outs} (a b: bool) (f: bool -> list N),
    @wordeq O outs n (Let_In a (fun x => Let_In b (fun y => f (andb x y)))) ->
    @wordeq O outs n (Let_In (andb a b) f).
  Proof. Admitted.

  Definition wordeq_debool_ltb: forall {n outs} (x y: N) (f: bool -> list N),
    @wordeq O outs n (f true) -> @wordeq O outs n (f false) ->
    @wordeq O 1 n [x] -> @wordeq O 1 n [y] ->
    @wordeq O outs n (Let_In (x <? y)%N f).
  Proof. Admitted.

  Definition wordeq_debool_eqb: forall {n outs} (x y: N) (f: bool -> list N),
    @wordeq O outs n (f true) -> @wordeq O outs n (f false) ->
    @wordeq O 1 n [x] -> @wordeq O 1 n [y] ->
    @wordeq O outs n (Let_In (x =? y)%N f).
  Proof. Admitted.

End WordEq.

(** Wordization Tactics **)

Ltac standardize_wordeq :=
  repeat match goal with
  | [|- @wordeq (S ?m) _ _ _] => apply wordeq_kill_arg; intro
  | [|- @wordeq O _ _ (Let_In true _)] => apply wordeq_let_const
  | [|- @wordeq O _ _(Let_In false _)] => apply wordeq_let_const
  | [|- @wordeq O _ _ (Let_In (_ <? _)%Z _)] => apply wordeq_debool_ltb
  | [|- @wordeq O _ _ (Let_In (_ =? _)%Z _)] => apply wordeq_debool_eqb
  | [|- @wordeq O _ _ (Let_In (andb _ _) _)] => apply wordeq_debool_andb
  | [|- @wordeq O _ _ (Let_In _ _)] => apply wordeq_cut_let
  | [|- @wordeq O _ _ (cons _ _)] => apply wordeq_break_cons
  end.

Ltac wordize_iter :=
  repeat match goal with
  | [ |- context[& ?x + & ?y + ind ?b] ] =>
    find_bound_on x; find_bound_on y; rewrite wordize_awc
  | [ |- context[N.mul (& ?x) (& ?y)] ] =>
    find_bound_on x; find_bound_on y; erewrite wordize_mult'
  | [ |- context[N.add (& ?x) (& ?y)] ] =>
    find_bound_on x; find_bound_on y; erewrite wordize_plus'
  | [ |- context[N.land (& ?x) _] ] =>
    find_bound_on x; rewrite <- mask_spec
  | [ |- context[N.shiftr (& ?x) ?k] ] =>
    find_bound_on x; rewrite (wordize_shiftr x k)
  end.

Ltac simpl' := cbn beta delta iota.

Ltac wordize_intro := repeat eexists; intros; list_destruct; simpl'.

Ltac wordize :=
  standardize_wordeq;
  wordize_intro;
  wordize_iter;
  bound_compute;
  try reflexivity.

Close Scope nword_scope.
