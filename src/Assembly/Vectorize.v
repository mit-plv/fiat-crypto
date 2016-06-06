
Require Export Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits Compare_dec Arith.
Require Import ProofIrrelevance Ring List.
Require Import MultiBoundedWord.

Section Vector.
  Import ListNotations.

  Definition vec T n := {x: list T | length x = n}.

  Definition vget {n T} (x: vec T n) (i: {v: nat | (v < n)%nat}): T.
    refine (
      match (proj1_sig x) as x' return (proj1_sig x) = x' -> _ with
      | [] => fun _ => _
      | x0 :: xs => fun _ => nth (proj1_sig i) (proj1_sig x) x0
      end eq_refl); abstract (
      destruct x as [x xp], i as [i ip]; destruct x as [|x0 xs];
      simpl in xp; subst; inversion _H; clear _H; omega).
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
