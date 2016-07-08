Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec.
Require Import Compare_dec Omega.
Require Import FunctionalExtensionality ProofIrrelevance.
Require Import QhasmUtil QhasmEvalCommon.
Require Import WordizeUtil Bounds Vectorize List.

Import EvalUtil ListNotations.

Hint Rewrite wordToN_nat Nat2N.inj_add N2Nat.inj_add
             Nat2N.inj_mul N2Nat.inj_mul Npow2_nat : N.

Open Scope nword_scope.

Coercion ind : bool >-> N.

Section ToWord.
  Lemma wordize_plus: forall {n} (x y: word n),
    (&x + &y)%N =
      if (overflows n (&x + &y)%N)
      then (& (x ^+ y) + Npow2 n)%N
      else (& (x ^+ y)).
  Proof. Admitted.

  Lemma wordize_awc: forall {n} (x y: word n) (c: bool),
    (&x + &y + c)%N =
      if (overflows n (&x + &y + c)%N)
      then (&(addWithCarry x y c) + Npow2 n)%N
      else (&(addWithCarry x y c)).
  Proof. Admitted.

  Lemma wordize_mult: forall {n} (x y: word n) (b: N),
    (&x * &y)%N = (&(x ^* y) +
      &((EvalUtil.highBits (n/2) x) ^* (EvalUtil.highBits (n/2) y)) * Npow2 n)%N.
  Proof. intros. Admitted.

  Lemma wordize_shiftr: forall {n} (x: word n) (k: nat),
    (N.shiftr_nat (&x) k) = & (shiftr x k).
  Proof. Admitted.
End ToWord.

Definition wordeq {ins outs} (n: nat) (f: Curried N N ins outs) :=
  {g: Curried (word n) (word n) ins outs |
   forall (x: list (word n)), length x = ins ->
      map (@wordToN n) ((curriedToList (wzero _) g) x) =
        (curriedToList 0%N f) (map (@wordToN n) x)}.

(** Wordization Tactics **)

Ltac wordize_iter :=
  repeat match goal with
  | [ |- context[overflows ?n ?x] ] => destruct (overflows n x)
  | [ |- context[& ?x + & ?y + ind ?b] ] => rewrite wordize_awc
  | [ |- context[N.mul (& ?x) (& ?y)] ] => rewrite wordize_mult
  | [ |- context[N.add (& ?x) (& ?y)] ] => rewrite wordize_plus
  | [ |- context[N.land (& ?x) _] ] => rewrite <- mask_spec
  | [ |- context[N.shiftr (& ?x) ?k] ] => rewrite (wordize_shiftr x k)
  | [ |- _ = _ ] => reflexivity
  end.

Ltac wordize_intro :=
  repeat eexists; intros; list_destruct; simpl.

Ltac wordize_contra :=
  match goal with
  | [ H: (_ >= _)%N |- _ ] =>
    unfold N.ge in H;
      contradict H;
      apply N.compare_lt_iff
  end.

Ltac lt_crush := try abstract (clear; vm_compute; intuition).

(** Examples **)

Module WordizationExamples.
  Definition example0 : Curried N N 2 1 := fun x y =>
    N.add (N.land x (N.ones 16)) (N.land y (N.ones 16)).

  Lemma wordize_example0: wordeq 16 example0.
  Proof.
    unfold example0.
    wordize_intro.
    wordize_iter.
    wordize_contra.
  Admitted.

End WordizationExamples.

Close Scope nword_scope.
