Require Export Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits Compare_dec Arith.
Require Import ProofIrrelevance Ring List Omega.
Require Import Program.Equality.
Require Import Crypto.Util.Tuple.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x :=
  let y := x in f y.

Notation "'plet' x := y 'in' z" := (Let_In y (fun x => z)) (at level 60).

Section Listize.
  Import ListNotations.

  Transparent tuple.

  Fixpoint tupleToList' {A k}: tuple' A k -> list A :=
    match k as k' return tuple' A k' -> list A with
    | O => fun x => [x]
    | (S k'') => fun x =>
      match x with
      | (t, v) => v :: (@tupleToList' _ _ t)
      end
    end.

  Definition tupleToList {A} (k: nat): tuple A k -> list A :=
    match k as k' return tuple A k' -> list A with
    | O => fun _ => []
    | (S k'') => @tupleToList' A k''
    end.

  Lemma app_cons: forall {T} (x: T) (lst: list T), [x] ++ lst = cons x lst.
  Proof. intros; simpl; reflexivity. Qed.

  Fixpoint Curried (A B: Type) (ins: nat) (outs: nat): Type :=
    match ins with
    | O => list B
    | S ins' => A -> (Curried A B ins' outs)
    end.

  Definition ListF (A B: Type): Type := list A -> list B.

  Fixpoint curriedToListF' {A B: Type} {ins outs: nat} (args: nat) (default: A)
      (f: Curried A B ins outs): ListF A B := fun (lst: list A) =>
    match ins as ins' return Curried A B ins' outs -> list B with
    | O => fun g => g
    | S ins'' => fun g =>
      (curriedToListF' args default (g (nth (args - ins) lst default))) lst
    end f.

  Definition curriedToListF {A B: Type} {ins outs: nat} (default: A)
      (f: Curried A B ins outs): ListF A B :=
    curriedToListF' ins default f.

End Listize.

Section Lets.
  Import ListNotations.

  Lemma detuple_let: forall {A B C} (y0: A) (y1: B) (z: (A * B) -> C),
      Let_In (y0, y1) z =
        Let_In y0 (fun x0 =>
          Let_In y1 (fun x1 =>
            z (x0, x1))).
  Proof. intros; unfold Let_In; cbv zeta; intuition. Qed.

  Lemma listize_let: forall {A B} (y d: A) (z: A -> B),
      Let_In y z = Let_In [y] (fun x => z (nth 0 x d)).
  Proof. intros; unfold Let_In; cbv zeta; intuition. Qed.

  Lemma combine_let_lists: forall {A B} (a: list A) (b: list A) (d: A) (z: list A -> list A -> B),
      Let_In a (fun x => Let_In b (z x)) =
        Let_In (a ++ b) (fun x => z (firstn (length a) x) (skipn (length a) x)).
  Proof.

    intros; unfold Let_In; cbv zeta.

    assert (forall b0, firstn (length a) (a ++ b0) = a) as HA. {
      induction a; intros; simpl; try reflexivity.
      apply f_equal; apply IHa.
    }

    assert (forall b0, skipn (length a) (a ++ b0) = b0) as HB. {
      induction a; intros; simpl; try reflexivity.
      apply IHa; intro; simpl in HA.
      pose proof (HA b1) as HA'; inversion HA' as [HA''].
      rewrite HA''.
      assumption.
    }

    rewrite HA, HB; reflexivity.
  Qed.

End Lets.

Ltac list_destruct :=
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
