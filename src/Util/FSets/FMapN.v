Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.NArith.NArith.
Require Import Crypto.Util.FSets.FMapIso.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.Iso.

Local Set Implicit Arguments.

(* TODO: Swap out for the version in Util/Structures/OrdersEx.v, and profile to see if there are any perf implications *)
Module NIsoPositive <: IsoOrderedTypeOrig PositiveMap.E.
  Definition t := N.
  Definition eq : t -> t -> Prop := eq.
  Definition eq_equiv : Equivalence eq := _.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := N.eq_dec.
  Definition to_ : t -> PositiveMap.E.t := N.succ_pos.
  Definition of_ : PositiveMap.E.t -> t := Pos.pred_N.
  Lemma Proper_to_ : Proper (eq ==> PositiveMap.E.eq) to_.
  Proof. cbv [eq]; repeat intro; subst; reflexivity. Qed.
  Lemma Proper_of_ : Proper (PositiveMap.E.eq ==> eq) of_.
  Proof. cbv [PositiveMap.E.eq]; repeat intro; subst; reflexivity. Qed.
  Lemma of_to : forall x : t, eq (of_ (to_ x)) x.
  Proof. cbv [eq of_ to_]; intros; now rewrite N.pos_pred_succ. Qed.
  Lemma to_of : forall x : PositiveMap.E.t, PositiveMap.E.eq (to_ (of_ x)) x.
  Proof.
    intro x.
    cut (N.pos (to_ (of_ x)) = N.pos x); [ congruence | ].
    cbv [PositiveMap.E.eq of_ to_].
    rewrite N.pos_pred_spec, N.succ_pos_spec.
    lia.
  Qed.
  Definition eq_refl : Reflexive eq := _.
  Definition eq_sym : Symmetric eq := _.
  Definition eq_trans : Transitive eq := _.
  Definition lt (x y : t) : Prop := PositiveMap.E.lt (to_ x) (to_ y).
  Global Instance lt_trans : Transitive lt | 100.
  Proof. repeat intro; eapply PositiveMap.E.lt_trans; eassumption. Qed.
  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    cbv [lt eq]; intros * H ?; apply PositiveMap.E.lt_not_eq in H; subst.
    cbv [PositiveMap.E.eq] in *; congruence.
  Qed.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    refine match PositiveMap.E.compare (to_ x) (to_ y) with
           | LT pf => LT _
           | EQ pf => EQ (eq_trans (eq_sym (of_to _)) (eq_trans (f_equal _ pf) (of_to _)))
           | GT pf => GT _
           end;
      cbv [lt eq PositiveMap.E.eq] in *; try assumption.
  Defined.
  Global Instance Proper_to_lt : Proper (lt ==> PositiveMap.E.lt) to_ | 10.
  Proof. cbv [lt Proper]; repeat intro; assumption. Qed.
  Global Instance Proper_of_lt : Proper (PositiveMap.E.lt ==> lt) of_ | 10.
  Proof. cbv [lt Proper]; repeat intro; rewrite !to_of; assumption. Qed.
End NIsoPositive.

Module NMap <: S := IsoS PositiveMap NIsoPositive.
