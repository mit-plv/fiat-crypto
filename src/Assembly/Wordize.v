Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec.
Require Import Compare_dec Omega Bool.
Require Import FunctionalExtensionality ProofIrrelevance.
Require Import QhasmUtil QhasmEvalCommon.
Require Import WordizeUtil Bounds List Listize Natize.
Require Import Crypto.Specific.GF1305.

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

  Definition getBits (x: N) := N.log2 (x + 1).
End ToWord.

Section WordEq.
  Definition wordeq {ins outs} (n: nat) (f: Curried N N ins outs) :=
    {g: Curried (word n) (word n) ins outs | forall (x: list (word n)),
      (curriedToListF (wzero _) g) x =
        map (@NToWord n) ((curriedToListF 0%N f) (map (@wordToN n) x))}.

  Definition wordeq_kill_arg'' {m n w}
      (f: Curried N N (S m) n)
      (g: forall x, wordeq w (f (wordToN x))):
      Curried (word w) (word w) (S m) n :=
    fun x => proj1_sig (g x).

  Lemma wordToN_zero: forall w, wordToN (wzero w) = 0%N.
  Proof.
    intros.
    unfold wzero; rewrite wordToN_nat.
    rewrite wordToNat_natToWord_idempotent; simpl; intuition.
    apply Npow2_gt0.
  Qed.

  Lemma wordeq_kill_arg': forall {m n w: nat}
        (f: Curried N N (S m) n)
        (g: forall x, wordeq w (f (wordToN x)))
        (x: list (word w)),
    curriedToListF (wzero w) (wordeq_kill_arg'' f g) x =
        map (NToWord w) (curriedToListF 0%N f (map (@wordToN w) x)).
  Proof.
    intros; unfold wordeq_kill_arg'', curriedToListF; simpl in *.
    destruct (g _) as [f' p]; simpl.
    pose proof (p (tl x)) as p'; clear p.
    rewrite <- (wordToN_zero w).
    replace (m - m) with O in * by omega.
    rewrite map_nth.
    unfold curriedToListF in p'.
    replace (map (@wordToN w) (tl x)) with (tl (map (@wordToN w) x)) in p'.
    replace (curriedToListF' (S m) (wzero w) f' x)
        with (curriedToListF' m (wzero w) f' (tl x));
        try rewrite p'; try clear f'; try clear f; try f_equal.

    - rewrite curriedToListF'_tl; try omega.
      repeat f_equal; intuition.
      rewrite wordToN_zero.
      reflexivity.

    - rewrite curriedToListF'_tl; try omega.
      rewrite p'.
      reflexivity.

    - induction x; simpl; intuition.
  Qed.

  Definition wordeq_kill_arg {m n w} (f: Curried N N (S m) n):
    (forall x, wordeq w (f (@wordToN w x))) -> wordeq w f.
  Proof.
    refine (fun g => exist _ (wordeq_kill_arg'' f g) _).
    apply wordeq_kill_arg'.
  Defined.

  Definition wordeq_break_cons: forall {m w} (a: N) (b: list N),
    @wordeq O 1 w [a] ->
    @wordeq O (S m) w b ->
    @wordeq O (S (S m)) w (cons a b).
  Proof.
    intros m w a b n0 n1.
    exists (@cons (word w) (hd (wzero w) (proj1_sig n0)) (proj1_sig n1)); intro x.
    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    pose proof (p0 x) as p0'.
    pose proof (p1 x) as p1'.

    abstract (
        unfold curriedToListF in *;
        simpl in *;
        rewrite p0', p1';
        simpl; reflexivity).
  Defined.

  Definition wordeq_nil: forall w, @wordeq O O w [].
  Proof. intro; exists []; abstract (intro; simpl; reflexivity). Qed.

  Definition wordeq_cut_let: forall {outs w} (x: N) (f: N -> list N),
    (x < Npow2 w)%N ->
    (0 <= x)%N ->
    @wordeq 1 outs w f -> @wordeq O 1 w [x] ->
    @wordeq O outs w (Let_In x f).
  Proof.
    intros outs w x f B H n0 n1.
    exists (Let_In (hd (wzero w) (proj1_sig n1)) (proj1_sig n0)); intro x0.

    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    pose proof (p0 [NToWord w x]) as p0'.
    pose proof (p1 x0) as p1'.

    abstract (
        unfold curriedToListF, Let_In in *;
        simpl in *;
        rewrite p1'; simpl;
        rewrite p0'; simpl;
        f_equal;
        rewrite wordToN_NToWord;
        intuition).
  Defined.

  Definition wordeq_let_const: forall {T outs w} (a: T) (f: T -> list N),
    @wordeq O outs w (f a) -> @wordeq O outs w (Let_In a f).
  Proof.
    intros T outs w a f n0.
    exists (proj1_sig n0); intro x0.
    destruct n0 as [f0 p0].
    pose proof (p0 x0) as p0'.
    abstract (
        simpl; rewrite p0'; unfold Let_In;
        simpl; reflexivity).
  Defined.

  Definition wordeq_debool_andb: forall {outs w} (a b: bool) (f: bool -> list N),
    @wordeq O outs w (Let_In a (fun x => Let_In b (fun y => f (andb x y)))) ->
    @wordeq O outs w (Let_In (andb a b) f).
  Proof.
    intros T outs w a f n0.
    exists (proj1_sig n0); intro x0.
    destruct n0 as [f0 p0].
    pose proof (p0 x0) as p0'.
    abstract (
        simpl; rewrite p0'; unfold Let_In;
        simpl; reflexivity).
  Defined.

  Definition wordeq_debool_ltb: forall {outs w} (x y: N) (f: bool -> list N),
    (x < Npow2 w)%N -> (y < Npow2 w)%N ->
    (0 <= x)%N -> (0 <= y)%N ->
    @wordeq O outs w (f true) -> @wordeq O outs w (f false) ->
    @wordeq O 1 w [x] -> @wordeq O 1 w [y] ->
    @wordeq O outs w (Let_In (x <? y)%N f).
  Proof.
    intros outs w a b f B0 B1 I0 I1 n0 n1 n2 n3.

    exists (if ((wordToN (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n2) [])))
            <? wordToN (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n3) [])))%N
        then (proj1_sig n0) else (proj1_sig n1)); intro x.

    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    destruct n2 as [f2 p2].
    destruct n3 as [f3 p3].

    pose proof (p0 x) as p0'.
    pose proof (p1 x) as p1'.
    pose proof (p2 x) as p2'.
    pose proof (p3 x) as p3'.

    abstract (
        unfold Let_In; simpl;
        rewrite p2, p3; simpl;
        repeat rewrite wordToN_NToWord; try assumption;
        destruct (a <? b)%N; try assumption).
  Defined.

  Lemma Ninj_eqb: forall w a b,
      (a < Npow2 w)%N -> (b < Npow2 w)%N ->
      (weqb (NToWord w a) (NToWord w b)) = (a =? b)%N.
  Proof.
    intros w a b B0 B1.
    symmetry.
    rewrite <- (wordToN_NToWord w a) at 1; try assumption.
    rewrite <- (wordToN_NToWord w b) at 1; try assumption.
    destruct (weq (NToWord w a) (NToWord w b)) as [e|e].

    - rewrite e at 1.
      apply weqb_true_iff in e; rewrite e.
      repeat rewrite wordToN_NToWord; try assumption.
      apply N.eqb_eq.
      reflexivity.

    - assert (a <> b) as H by (
        intro H; rewrite H in e; apply e; reflexivity).
      repeat rewrite wordToN_NToWord; try assumption.
      replace (weqb _ _) with false.

      + assert ((a =? b)%N <> true). {
          intro H0.
          rewrite N.eqb_eq in H0.
          rewrite H0 in H.
          apply H.
          reflexivity.
        }

        induction (a =? b)%N; intuition.

      + assert (weqb (NToWord w a) (NToWord w b) <> true). {
          intro H0.
          rewrite weqb_true_iff in H0.
          rewrite H0 in e.
          apply e.
          reflexivity.
        }

        induction (weqb _ _); intuition.
  Defined.

  Definition wordeq_debool_eqb: forall {outs w} (x y: N) (f: bool -> list N),
    (x < Npow2 w)%N -> (y < Npow2 w)%N ->
    (0 <= x)%N -> (0 <= y)%N ->
    @wordeq O outs w (f true) -> @wordeq O outs w (f false) ->
    @wordeq O 1 w [x] -> @wordeq O 1 w [y] ->
    @wordeq O outs w (Let_In (N.eqb x y) f).
  Proof.
    intros outs w a b f B0 B1 I0 I1 n0 n1 n2 n3.

    exists (if (weqb
            (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n2) []))
            (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n3) [])))%N
        then (proj1_sig n0) else (proj1_sig n1)); intro x.

    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    destruct n2 as [f2 p2].
    destruct n3 as [f3 p3].

    pose proof (p0 x) as p0'.
    pose proof (p1 x) as p1'.
    pose proof (p2 x) as p2'.
    pose proof (p3 x) as p3'.

    abstract (
        unfold Let_In; simpl;
        rewrite p2, p3; simpl;
        rewrite Ninj_eqb;
        destruct (a =? b)%N;
        assumption).
  Defined.

End WordEq.

(** Wordization Tactics **)

Ltac replace_ones x :=
  let e := fresh in (
    destruct (N.eq_dec x (N.ones (getBits x))) as [e|e];
    try rewrite e;
    vm_compute in e;
    match goal with
    | [H: ?x = ?x |- _] => clear H
    | [H: ?x = ?x -> False |- _] => contradict H; reflexivity
    | [H: _ = _ -> False |- _] => clear H
    | [H: _ = _ |- _] => inversion H
    end).

Ltac standardize_wordeq :=
  repeat match goal with
  | [|- @wordeq (S ?m) _ _ _] => apply wordeq_kill_arg; intro
  | [|- @wordeq O _ _ (Let_In true _)] => apply wordeq_let_const
  | [|- @wordeq O _ _(Let_In false _)] => apply wordeq_let_const
  | [|- @wordeq O _ _ (Let_In (_ <? _)%N _)] => apply wordeq_debool_ltb
  | [|- @wordeq O _ _ (Let_In (_ =? _)%N _)] => apply wordeq_debool_eqb
  | [|- @wordeq O _ _ (Let_In (andb _ _) _)] => apply wordeq_debool_andb
  | [|- @wordeq O _ _ (Let_In _ _)] => apply wordeq_cut_let
  | [|- @wordeq O _ _ (cons _ _)] => apply wordeq_break_cons
  end.

Transparent wordeq_kill_arg wordeq_let_const wordeq_debool_ltb
            wordeq_debool_eqb wordeq_debool_andb wordeq_cut_let
            wordeq_break_cons.

Ltac wordize_iter :=
  repeat match goal with
  | [ |- context[& ?x + & ?y + ind ?b] ] =>
    find_bound_on x; find_bound_on y; rewrite wordize_awc
  | [ |- context[N.mul (& ?x) (& ?y)] ] =>
    find_bound_on x; find_bound_on y; erewrite wordize_mult'
  | [ |- context[N.add (& ?x) (& ?y)] ] =>
    find_bound_on x; find_bound_on y; erewrite wordize_plus'
  | [ |- context[N.land (& ?x) ?y] ] =>
    find_bound_on x; replace_ones y; rewrite <- mask_spec
  | [ |- context[N.shiftr (& ?x) ?k] ] =>
    find_bound_on x; rewrite (wordize_shiftr x k)
  | [ |- context[@NToWord _ (@wordToN _ _)] ] =>
    rewrite NToWord_wordToN
  end.

Ltac simpl' := cbn beta delta iota.

Ltac wordize_intro := repeat eexists; intros; simpl'.

Ltac wordize :=
  standardize_wordeq;
  wordize_intro;
  wordize_iter;
  bound_compute;
  try reflexivity.
