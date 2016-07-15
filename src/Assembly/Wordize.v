Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec.
Require Import Compare_dec Omega.
Require Import FunctionalExtensionality ProofIrrelevance.
Require Import QhasmUtil QhasmEvalCommon.
Require Import WordizeUtil Bounds Vectorize List.
Require Import NArithRing.

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
  Admitted.

  Lemma wordize_awc: forall {n} (x y: word n) (c: bool),
      (&x + &y + c < Npow2 n)%N
    -> (&x + &y + c)%N = &(addWithCarry x y c).
  Proof. Admitted.

  Lemma wordize_mult: forall {n} (x y: word n),
      (&x * &y < Npow2 n)%N
    -> (&x * &y)%N = &(x ^* y).
  Proof. intros. Admitted.

  Lemma wordize_shiftr: forall {n} (x: word n) (k: nat),
    (N.shiftr_nat (&x) k) = & (shiftr x k).
  Proof. Admitted.

  Lemma conv_mask: forall {n} (x: word n) (k: nat),
    mask k x = x ^& (NToWord _ (N.ones (N.of_nat k))).
  Proof.
    intros.
    apply NToWord_equal.
    rewrite <- (Nat2N.id k).
    rewrite mask_spec.
    apply N.bits_inj_iff; unfold N.eqf; intro m.
    rewrite N.land_spec.
    repeat rewrite wordToN_testbit.
    rewrite <- (N2Nat.id m).
    rewrite <- wordToN_wones.
    induction n; shatter x; try abstract (simpl; intuition).
    induction (N.to_nat m).

    - rewrite wordToN_wones in *.
      rewrite N2Nat.id in *; rewrite Nat2N.id in *.
      induction (whd x);
        repeat rewrite andb_true_l;
        repeat rewrite andb_false_l;
        try reflexivity.
      rewrite <- (Nat2N.id 0) in *.
      rewrite <- wordToN_testbit.
      setoid_rewrite <- wordToN_testbit in IHn.
      admit.

    - admit.
  Admitted.
End ToWord.

Definition wordeq {ins outs} (n: nat) (f: Curried N N ins outs) :=
  {g: Curried (word n) (word n) ins outs |
   forall (x: list (word n)), length x = ins ->
      map (@wordToN n) ((curriedToList (wzero _) g) x) =
        (curriedToList 0%N f) (map (@wordToN n) x)}.

(** Wordization Tactics **)

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

Ltac wordize_intro :=
  repeat eexists; intros; list_destruct; simpl.

Ltac wordize :=
  wordize_intro;
  wordize_iter;
  bound_compute;
  try reflexivity.

Close Scope nword_scope.
