Require Export Bedrock.Word Bedrock.Nomega.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.NArith.NArith Coq.PArith.PArith Coq.NArith.Ndigits Coq.Arith.Compare_dec Coq.Arith.Arith.
Require Import Coq.Logic.ProofIrrelevance Coq.setoid_ring.Ring Coq.Lists.List Coq.omega.Omega.

Require Export Crypto.Util.FixCoqMistakes.

Definition Let_In {A P} (x : A) (f : forall a : A, P a) : P x :=
  let y := x in f y.

Notation "'plet' x := y 'in' z" := (Let_In y (fun x => z)) (at level 60).

Section Vector.
  Import ListNotations.

  Definition vec T n := {x: list T | length x = n}.

  Definition vget {n T} (x: vec T n) (i: {v: nat | (v < n)%nat}): T.
    refine (
      match (proj1_sig x) as x' return (proj1_sig x) = x' -> _ with
      | [] => fun _ => _
      | x0 :: xs => fun _ => nth (proj1_sig i) (proj1_sig x) x0
      end eq_refl);
    abstract (
      destruct x as [x xp], i as [i ip]; destruct x as [|x0 xs];
      simpl in *; subst; try omega;
      match goal with
      | [H: _ = @nil _ |- _] => inversion H
      end).
  Defined.

  Lemma vget_spec: forall {T n} (x: vec T n) (i: {v: nat | (v < n)%nat}) (d: T),
      vget x i = nth (proj1_sig i) (proj1_sig x) d.
  Proof.
    intros; destruct x as [x xp], i as [i ip];
      destruct x as [|x0 xs]; induction i; unfold vget; simpl;
      intuition; try (simpl in xp; subst; omega);
      induction n; simpl in xp; try omega; clear IHi IHn.

    apply nth_indep.
    assert (length xs = n) by omega; subst.
    omega.
  Qed.

  Definition vec0 {T} : vec T 0.
    refine (exist _ [] _); abstract intuition.
  Defined.

  Lemma lift0: forall {T n} (x: T), vec (word n) 0 -> T.
    intros; refine x.
  Defined.

  Lemma liftS: forall {T n m} (f: vec (word n) m -> word n -> T),
    (vec (word n) (S m) -> T).
  Proof.
    intros T n m f v; destruct v as [v p]; induction m, v;
      try (abstract (inversion p)).

    - refine (f (exist _ [] _) w); abstract intuition.
    - refine (f (exist _ v _) w); abstract intuition.
  Defined.

  Lemma vecToList: forall T n m (f: vec (word n) m -> T),
    (list (word n) -> option T).
  Proof.
    intros T n m f x; destruct (Nat.eq_dec (length x) m).

    - refine (Some (f (exist _ x _))); abstract intuition.
    - refine None.
  Defined.
End Vector.

Section Vectorization.
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

End Vectorization.

Ltac vectorize :=
  repeat match goal with
   | [ |- context[?a - 1] ] =>
     let c := eval simpl in (a - 1) in
     replace (a - 1) with c by omega
  | [ |- vec (word ?n) O -> ?T] => apply (@lift0 T n)
  | [ |- vec (word ?n) ?m -> ?T] => apply (@liftS T n (m - 1))
  end.

Section Examples.
  Lemma vectorize_example: (vec (word 32) 2 -> word 32).
    vectorize; refine (@wplus 32).
  Qed.
End Examples.
