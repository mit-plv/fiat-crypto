
Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Compare_dec Arith.
Require Import ProofIrrelevance Ring List.
Require Export MultiBoundedWord QhasmCommon.

Import ListNotations.

(* Tuple Manipulations *)

Fixpoint Tuple (T: Type) (n: nat): Type :=
  match n with
  | O => T
  | S m => (T * (Tuple T m))%type
  end.

Definition just {T} (x: T): Tuple T O := x.

Definition cross {T n} (x: T) (tup: Tuple T n): Tuple T (S n) := (x, tup).

Definition getLen {T n} (tup: Tuple T n) := (S n).

Fixpoint tget' {T n} (tup: Tuple T n) (x: nat): T.
  induction x, n; try exact tup.

  exact (fst tup).
  exact (tget' _ _ (snd tup) x).
Defined.

Definition tget {T n} (tup: Tuple T n) (x: nat): T :=
  tget' tup (n - x).

Lemma tget_inc: forall {T k} (x: nat) (v: T) (tup: Tuple T k),
    (x <= k)%nat -> tget tup x = tget (cross v tup) x.
Proof.
  intros; unfold cross, tget.
  replace (S k - x) with (S (k - x)) by intuition.
  unfold tget'; simpl; intuition.
Qed.

Ltac tupleize n :=
  repeat match goal with
  | [T: Tuple _ ?k, w: word n |- _] => let H := fresh in
    replace w with (tget (cross w T) (S k)) by (simpl; intuition);

      assert (forall m, (m <= k)%nat -> tget T m = tget (cross w T) m) as H
        by (intros; apply tget_inc; intuition);
      repeat rewrite H by intuition;

      generalize (cross w T); clear w T H; intro T

  | [w: word n |- _] =>
    replace w with (tget (just w) O) by (simpl; intuition);
      generalize (just w); clear w; let T := fresh in intro T
  end.

(* Conversion from nvec functions to wvec functions *)

