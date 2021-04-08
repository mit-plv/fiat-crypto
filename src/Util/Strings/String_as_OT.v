Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Strings.Ascii Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Export Crypto.Util.FixCoqMistakes.

(** This should disappear whenever we bump the minimum version to a version where https://github.com/coq/coq/pull/14096 has been merged *)

Module Ascii_as_OT <: UsualOrderedType.
  Definition t := ascii.
  Include HasUsualEq <+ UsualIsEq.
  Definition eqb := Ascii.eqb.
  Definition eqb_eq := Ascii.eqb_eq.
  Include HasEqBool2Dec.

  Definition compare (a b : ascii) := N_as_OT.compare (N_of_ascii a) (N_of_ascii b).
  Definition lt (a b : ascii) := N_as_OT.lt (N_of_ascii a) (N_of_ascii b).

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    intros x x' Hx y y' Hy. rewrite Hx, Hy; intuition.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split; unfold lt; [ intro | intros ??? ]; eapply N_as_OT.lt_strorder.
  Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    intros x y; unfold eq, lt, compare.
    destruct (N_as_OT.compare_spec (N_of_ascii x) (N_of_ascii y)) as [H|H|H]; constructor; try assumption.
    now rewrite <- (ascii_N_embedding x), <- (ascii_N_embedding y), H.
  Qed.
End Ascii_as_OT.

(** [String] is an ordered type with respect to the usual lexical order. *)

Module String_as_OT <: UsualOrderedType.
  Definition t := string.
  Include HasUsualEq <+ UsualIsEq.
  Definition eqb := String.eqb.
  Definition eqb_eq := String.eqb_eq.
  Include HasEqBool2Dec.

  Fixpoint compare (a b : string)
    := match a, b with
       | EmptyString, EmptyString => Eq
       | EmptyString, _ => Lt
       | String _ _, EmptyString => Gt
       | String a_head a_tail, String b_head b_tail =>
         match Ascii_as_OT.compare a_head b_head with
         | Lt => Lt
         | Gt => Gt
         | Eq => compare a_tail b_tail
         end
       end.

  Definition lt (a b : string) := compare a b = Lt.

  Instance lt_compat : Proper (eq==>eq==>iff) lt.
  Proof.
    intros x x' Hx y y' Hy. rewrite Hx, Hy; intuition.
  Qed.

  Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
  Proof.
    unfold eq, lt.
    induction x as [|x xs IHxs], y as [|y ys]; cbn [compare]; try constructor; cbn [compare]; try reflexivity.
    specialize (IHxs ys).
    destruct (Ascii_as_OT.compare x y) eqn:H; [ destruct IHxs; constructor | constructor | constructor ]; cbn [compare].
    all: destruct (Ascii_as_OT.compare_spec y x), (Ascii_as_OT.compare_spec x y); cbv [Ascii_as_OT.eq] in *; try congruence; subst.
    all: exfalso; eapply irreflexivity; (idtac + etransitivity); eassumption.
  Qed.

  Instance lt_strorder : StrictOrder lt.
  Proof.
    split; unfold lt; [ intro x | intros x y z ]; unfold complement.
    { induction x as [|x xs IHxs]; cbn [compare]; [ congruence | ].
      destruct (Ascii_as_OT.compare x x) eqn:H; try congruence.
      exfalso; eapply irreflexivity; eassumption. }
    { revert x y z.
      induction x as [|x xs IHxs], y as [|y ys], z as [|z zs]; cbn [compare]; try congruence.
      specialize (IHxs ys zs).
      destruct (Ascii_as_OT.compare x y) eqn:Hxy, (Ascii_as_OT.compare y z) eqn:Hyz, (Ascii_as_OT.compare x z) eqn:Hxz;
        try intuition (congruence || eauto).
      all: destruct (Ascii_as_OT.compare_spec x y), (Ascii_as_OT.compare_spec y z), (Ascii_as_OT.compare_spec x z);
        try discriminate.
      all: unfold Ascii_as_OT.eq in *; subst.
      all: exfalso; eapply irreflexivity; (idtac + etransitivity); (idtac + etransitivity); eassumption. }
  Qed.
End String_as_OT.
