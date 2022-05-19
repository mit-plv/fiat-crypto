Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.NArith.NArith.
Require Import Crypto.Util.MSets.MSetIso.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Iso.

Local Set Implicit Arguments.

(* TODO: Swap out for the version in Util/Structures/OrdersEx.v, and profile to see if there are any perf implications *)
Module NIsoPositive <: IsoOrderedType PositiveSet.E.
  Definition t := N.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := N.eq_dec.
  Definition to_ : t -> PositiveSet.E.t := N.succ_pos.
  Definition of_ : PositiveSet.E.t -> t := Pos.pred_N.
  Lemma Proper_to_ : Proper (eq ==> PositiveSet.E.eq) to_.
  Proof. cbv [eq]; repeat intro; subst; reflexivity. Qed.
  Lemma Proper_of_ : Proper (PositiveSet.E.eq ==> eq) of_.
  Proof. cbv [PositiveSet.E.eq]; repeat intro; subst; reflexivity. Qed.
  Lemma of_to : forall x : t, eq (of_ (to_ x)) x.
  Proof. cbv [eq of_ to_]; intros; now rewrite N.pos_pred_succ. Qed.
  Lemma to_of : forall x : PositiveSet.E.t, PositiveSet.E.eq (to_ (of_ x)) x.
  Proof.
    intro x.
    cut (N.pos (to_ (of_ x)) = N.pos x); [ congruence | ].
    cbv [PositiveSet.E.eq of_ to_].
    rewrite N.pos_pred_spec, N.succ_pos_spec.
    lia.
  Qed.
  Definition lt (x y : t) : Prop := PositiveSet.E.lt (to_ x) (to_ y).
  Global Instance lt_strorder : StrictOrder lt | 100.
  Proof.
    split; hnf; cbv [lt complement]; intros *;
      apply PositiveSet.E.lt_strorder.
  Qed.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt := _.
  Definition compare (x y : t) : comparison := PositiveSet.E.compare (to_ x) (to_ y).
  Lemma compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    cbv [eq lt compare].
    destruct (PositiveSet.E.compare_spec (to_ x) (to_ y)); constructor; try assumption.
    cbv [PositiveSet.E.eq] in *.
    rewrite <- (of_to x), <- (of_to y).
    congruence.
  Qed.
  Global Instance Proper_to_lt : Proper (lt ==> PositiveSet.E.lt) to_ | 100.
  Proof. cbv [lt Proper respectful]; trivial. Qed.
  Global Instance Proper_of_lt : Proper (PositiveSet.E.lt ==> lt) of_ | 100.
  Proof. cbv [lt Proper respectful]; intros *; rewrite !to_of; trivial. Qed.
End NIsoPositive.

Module NSet <: S := IsoSets PositiveSet NIsoPositive.
