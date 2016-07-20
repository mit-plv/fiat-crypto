Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec.
Require Import Compare_dec Omega Bool.
Require Import FunctionalExtensionality ProofIrrelevance.
Require Import QhasmUtil QhasmEvalCommon.
Require Import WordizeUtil Bounds List Listize Natize.

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

  Lemma map_nth': forall w k x d,
      (d < Npow2 w)%N ->
      nth k (map (@wordToN w) x) d =
             @wordToN w (nth k x (NToWord w d)).
  Proof.
    intros; rewrite <- (wordToN_NToWord w d); try assumption.
    rewrite map_nth.
    rewrite NToWord_wordToN.
    reflexivity.
  Qed.
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

  Lemma NToWord_zero: forall w, NToWord w 0%N = wzero w.
  Proof.
    intros.
    unfold wzero; rewrite NToWord_nat.
    f_equal.
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

Section Masked.
  Definition maskeq {ins outs} (n: nat) (f: Curried N N ins outs) (masks: list nat) :=
    {g: Curried (word n) (word n) ins outs | forall (x: list (word n)),
        (forall k, (wordToN (nth k x (wzero _)) < Npow2 (nth k masks n))%N) ->
      (curriedToListF (wzero _) g) x =
        map (@NToWord n) ((curriedToListF 0%N f) (map (@wordToN n) x))}.

  Definition maskeq_kill_arg'' {m n w}
      (f: Curried N N (S m) n) masks
      (g: forall x, (wordToN x < Npow2 (hd w masks))%N ->
               maskeq w (f (@wordToN w x)) (tl masks)):
        Curried (word w) (word w) (S m) n.
    refine (fun x =>
      match (Nge_dec (wordToN x) (Npow2 (hd w masks))) with
      | right p => proj1_sig (g x p)
      | left _ => proj1_sig (g (wzero _) _)
      end); abstract (rewrite wordToN_zero; apply Npow2_gt0).
  Defined.

  Lemma nth_tl: forall {T k} (x: list T) d, nth k (tl x) d = nth (S k) x d.
  Proof. intros; induction x, k; simpl; intuition. Qed.

  Lemma maskeq_kill_arg': forall {m n w: nat}
      (f: Curried N N (S m) n) masks
      (g: forall x, (wordToN x < Npow2 (hd w masks))%N ->
               maskeq w (f (wordToN x)) (tl masks))
      (x: list (word w)),
    (forall k : nat, (& nth k x (wzero w) < Npow2 (nth k masks w))%N) ->
    curriedToListF (wzero w) (maskeq_kill_arg'' f masks g) x =
        map (NToWord w) (curriedToListF 0%N f (map (@wordToN w) x)).
  Proof.
    intros; unfold maskeq_kill_arg'', curriedToListF; simpl in *.
    destruct (Nge_dec _ _) as [g0|g0].

    - destruct (g _) as [f' p]; simpl.
      replace (m - m) with O in * by omega.
      unfold N.ge in g0.
      contradict g0.
      pose proof (H 0) as H0; unfold N.lt in H0.
      induction masks; simpl in *; assumption.

    - destruct (g _) as [f' p]; simpl.
      pose proof (p (tl x)) as p'; clear p.
      rewrite <- (wordToN_zero w).
      replace (m - m) with O in * by omega.
      rewrite map_nth.
      unfold curriedToListF in p'.
      replace (map (@wordToN w) (tl x)) with (tl (map (@wordToN w) x)) in p'.
      replace (curriedToListF' (S m) (wzero w) f' x)
          with (curriedToListF' m (wzero w) f' (tl x));
        try rewrite p'; try clear f'; try clear f; try f_equal;
        try (intro; repeat rewrite nth_tl; apply H).

      + rewrite curriedToListF'_tl; try omega.
        repeat f_equal; intuition.
        rewrite wordToN_zero.
        reflexivity.

      + rewrite curriedToListF'_tl; try omega.
        rewrite p'.
        reflexivity.
        intro; repeat rewrite nth_tl; apply H.

      + induction x; simpl; intuition.
  Qed.

  Definition maskeq_kill_arg {m n w} (f: Curried N N (S m) n) masks:
    (forall x, (wordToN x < Npow2 (hd w masks))%N ->
          maskeq w (f (@wordToN w x)) (tl masks)) -> maskeq w f masks.
  Proof.
    refine (fun g => exist _ (maskeq_kill_arg'' f _ g) _).
    intros; unfold maskeq_kill_arg''.
    apply maskeq_kill_arg'; intro; apply H.
  Defined.

  Definition maskeq_break_cons: forall {m w} (a: N) (b: list N) m0 ms,
    @maskeq O 1 w [a] [m0] ->
    @maskeq O (S m) w b ms ->
    @maskeq O (S (S m)) w (cons a b) (cons m0 ms).
  Proof.
    intros m w a b m0 ms n0 n1.
    exists (@cons (word w) (hd (wzero w) (proj1_sig n0)) (proj1_sig n1)); intros x H.
    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    pose proof (p0 x) as p0'.
    pose proof (p1 (tl x)) as p1'.

    abstract (
        unfold curriedToListF in *; simpl in *;
        rewrite p0', p1'; simpl; try reflexivity; intro k;
        induction k; try rewrite nth_tl; try apply H;
        induction k; apply word_size_bound ).
  Defined.

  Definition maskeq_nil: forall w, @maskeq O O w [] [].
  Proof. intro; exists []; abstract (intro; simpl; reflexivity). Qed.

  Definition maskeq_cut_let: forall {outs w} (x: N) (f: N -> list N) m0 ms,
    (x < Npow2 w)%N -> (x < Npow2 m0)%N ->
    @maskeq 1 outs w f (cons m0 ms) ->
    @maskeq O 1 w [x] [m0] ->
    @maskeq O outs w (Let_In x f) ms.
  Proof.
    intros outs w x f m0 ms W B n0 n1.
    exists (Let_In (hd (wzero w) (proj1_sig n1)) (proj1_sig n0)); intros x0 M.

    destruct n0 as [f0 p0].
    destruct n1 as [f1 p1].
    pose proof (p0 [NToWord w x]) as p0'.
    pose proof (p1 (cons (NToWord w x) x0)) as p1'.

    abstract (
      unfold curriedToListF, Let_In in *; simpl in *;

      rewrite p1'; simpl;
      try rewrite p0'; simpl;
      try rewrite wordToN_NToWord; intuition;

      induction k; try induction k;
      try rewrite wordToN_zero;
      try apply Npow2_gt0;
      try apply word_size_bound;
      pose proof (M 1) as M'; simpl in M';
      try rewrite nth_tl;
      try rewrite wordToN_NToWord;
      try assumption).
  Defined.

  Definition maskeq_let_const: forall {T outs w} (a: T) (f: T -> list N) masks,
    @maskeq O outs w (f a) masks -> @maskeq O outs w (Let_In a f) masks.
  Proof.
    intros T outs w a f masks n0.
    exists (proj1_sig n0); intros x0 H.
    destruct n0 as [f0 p0].
    pose proof (p0 x0) as p0'.
    abstract (
        simpl; rewrite p0'; unfold Let_In; try intro;
        try reflexivity;
        apply H).
  Defined.

  Definition maskeq_debool_andb: forall {outs w} (a b: bool) (f: bool -> list N) masks,
    @maskeq O outs w (Let_In a (fun x => Let_In b (fun y => f (andb x y)))) masks ->
    @maskeq O outs w (Let_In (andb a b) f) masks.
  Proof.
    intros T outs w a f masks n0.
    exists (proj1_sig n0); intros x0 H.
    destruct n0 as [f0 p0].
    pose proof (p0 x0) as p0'.
    abstract (
        simpl; rewrite p0'; unfold Let_In;
        simpl; try reflexivity; try intro; try apply H).
  Defined.

  Definition maskeq_debool_ltb: forall {outs w} (x y: N) (f: bool -> list N) m0 m1 masks,
    (x < Npow2 w)%N -> (y < Npow2 w)%N ->
    (0 <= x)%N -> (0 <= y)%N ->
    @maskeq O outs w (f true) masks -> @maskeq O outs w (f false) masks ->
    @maskeq O 1 w [x] m0 -> @maskeq O 1 w [y] m1 ->
    @maskeq O outs w (Let_In (x <? y)%N f) masks.
  Proof.
    intros outs w a b f m0 m1 masks B0 B1 I0 I1 n0 n1 n2 n3.

    exists (if ((wordToN (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n2) [])))
            <? wordToN (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n3) [])))%N
        then (proj1_sig n0) else (proj1_sig n1)); intros x H.

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
        destruct (a <? b)%N; try assumption;
        try apply p0; try apply p1; intro k;
        induction k; try induction k;
        try rewrite wordToN_zero;
        try apply Npow2_gt0;
        apply H).
  Defined.

  Definition maskeq_debool_eqb: forall {outs w} (x y: N) (f: bool -> list N) m0 m1 masks,
    (x < Npow2 w)%N -> (y < Npow2 w)%N ->
    (0 <= x)%N -> (0 <= y)%N ->
    @maskeq O outs w (f true) masks -> @maskeq O outs w (f false) masks ->
    @maskeq O 1 w [x] m0 -> @maskeq O 1 w [y] m1 ->
    @maskeq O outs w (Let_In (N.eqb x y) f) masks.
  Proof.
    intros outs w a b f m0 m1 masks B0 B1 I0 I1 n0 n1 n2 n3.

    exists (if (weqb
            (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n2) []))
            (hd (wzero w) (curriedToListF (wzero w) (proj1_sig n3) [])))%N
        then (proj1_sig n0) else (proj1_sig n1)); intros x H.

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
        try rewrite Ninj_eqb;
        repeat rewrite wordToN_NToWord; try assumption;
        destruct (a =? b)%N; try assumption;
        try apply p0; try apply p1; intro k;
        induction k; try induction k;
        try rewrite wordToN_zero;
        try apply Npow2_gt0;
        apply H).
  Defined.
End Masked.

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

Ltac standardize_maskeq :=
  repeat match goal with
  | [|- @maskeq (S ?m) _ _ _ _] => apply maskeq_kill_arg; intro
  | [|- @maskeq O _ _ (Let_In true _) _] => apply maskeq_let_const
  | [|- @maskeq O _ _(Let_In false _) _] => apply maskeq_let_const
  | [|- @maskeq O _ _ (Let_In (_ <? _)%N _) _] => apply maskeq_debool_ltb
  | [|- @maskeq O _ _ (Let_In (_ =? _)%N _) _] => apply maskeq_debool_eqb
  | [|- @maskeq O _ _ (Let_In (andb _ _) _) _] => apply maskeq_debool_andb
  | [|- @maskeq O _ _ (Let_In _ _) _] => apply maskeq_cut_let
  | [|- @maskeq O _ _ (cons _ _) _] => apply maskeq_break_cons
  end.

Transparent curriedToListF curriedToListF'. 

Transparent wordeq_kill_arg wordeq_let_const wordeq_debool_ltb
            wordeq_debool_eqb wordeq_debool_andb wordeq_cut_let
            wordeq_break_cons.

Transparent maskeq_kill_arg maskeq_let_const maskeq_debool_ltb
            maskeq_debool_eqb maskeq_debool_andb maskeq_cut_let
            maskeq_break_cons maskeq_kill_arg''.

Ltac wordize_iter :=
  match goal with
  | [ |- context[@NToWord _ 0%N] ] =>
    rewrite NToWord_zero
  | [ H: context[@NToWord _ 0%N] |- _ ] =>
    rewrite NToWord_zero
  | [ |- context[(nth _ (map ?f ?lst) ?d)] ] =>
    match type of lst with
    | list (word ?n) => find_bound_on (NToWord n d); rewrite map_nth'
    end
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

Ltac wordize_intro := repeat eexists; intros.

Ltac wordize :=
  standardize_wordeq;
  wordize_intro;
  simpl in *;
  repeat wordize_iter;
  simpl in *;
  bound_compute;
  try reflexivity.

Ltac unfold_bounds' n H :=
  let H' := fresh in
  match n with
  | O => pose proof (H O) as H'; simpl in H'
  | S ?k =>
    pose proof (H k) as H';
      simpl in H';
      unfold_bounds' k H
  end.

Ltac unfold_bounds :=
  match goal with
  | [H: forall _, (& nth _ ?x ?d < Npow2 (nth _ ?lst ?w))%N |- _] =>
    let n := eval simpl in (length lst) in
    unfold_bounds' n H
  end.

Ltac wordize_masked :=
  standardize_maskeq;
  wordize_intro;
  unfold_bounds;
  simpl in *;
  repeat wordize_iter;
  simpl in *;
  match goal with
  | [|- (_ < _)%N] => bound_compute
  | [|- (_ <= _)%N] => bound_compute
  | [|- _ = _] => simpl';
    repeat match goal with
    | [ |- context[nth ?k ?x ?d] ] => generalize (nth k x d); intro
    end; reflexivity
  end.
