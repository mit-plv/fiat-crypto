Require Import Coq.PArith.PArith Coq.ZArith.ZArith Coq.NArith.NArith.
Require Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Structures.Orders.Option.
Require Import Crypto.Util.Structures.Orders.Sum.
Require Import Crypto.Util.Structures.Orders.Flip.
Require Import Crypto.Util.Tactics.BreakMatch.

Module OptionPositiveOrderedTypeBits <: UsualOrderedType := OptionUsualOrderedType PositiveOrderedTypeBits.
Module OptionPositiveOrderedTypeBitsOrig <: UsualOrderedTypeOrig := OptionUsualOrderedTypeOrig OrderedTypeEx.PositiveOrderedTypeBits.

Module NIsoOptionPositiveCommon.
  Definition t := N.
  Include HasUsualEq.
  Include UsualIsEq.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := N.eq_dec.
  Definition to_ (x : t) : option positive
    := match x with
       | N0 => None
       | Npos p => Some p
       end.
  Definition of_ (x : option positive) : t
    := match x with
       | None => N0
       | Some p => Npos p
       end.
  Lemma Proper_to_ : Proper (eq ==> OptionPositiveOrderedTypeBits.eq) to_.
  Proof. cbv [eq]; repeat intro; subst; reflexivity. Qed.
  Lemma Proper_of_ : Proper (OptionPositiveOrderedTypeBits.eq ==> eq) of_.
  Proof. cbv [OptionPositiveOrderedTypeBits.eq]; repeat intro; subst; reflexivity. Qed.
  Lemma of_to : forall x : t, eq (of_ (to_ x)) x.
  Proof. cbv [eq of_ to_]; intros; break_innermost_match; reflexivity. Qed.
  Lemma to_of : forall x : option positive, OptionPositiveOrderedTypeBits.eq (to_ (of_ x)) x.
  Proof.
    intros [|]; reflexivity.
  Qed.
  Definition lt (x y : t) : Prop := OptionPositiveOrderedTypeBits.lt (to_ x) (to_ y).
  Global Instance lt_strorder : StrictOrder lt | 100.
  Proof.
    split; hnf; cbv [lt complement]; intros *;
      apply OptionPositiveOrderedTypeBits.lt_strorder.
  Qed.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt := _.
  Global Instance Proper_to_lt : Proper (lt ==> OptionPositiveOrderedTypeBits.lt) to_ | 100.
  Proof. cbv [lt Proper respectful]; trivial. Qed.
  Global Instance Proper_of_lt : Proper (OptionPositiveOrderedTypeBits.lt ==> lt) of_ | 100.
  Proof. cbv [lt Proper respectful]; intros *; rewrite !to_of; trivial. Qed.
  Include BackportEq.
  Include BackportStrOrder.
End NIsoOptionPositiveCommon.

Module NIsoOptionPositive <: IsoOrderedType OptionPositiveOrderedTypeBits.
  Include NIsoOptionPositiveCommon.
  Definition compare (x y : t) : comparison := OptionPositiveOrderedTypeBits.compare (to_ x) (to_ y).
  Lemma compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    cbv [eq].
    destruct (OptionPositiveOrderedTypeBits.compare_spec (to_ x) (to_ y) : CompareSpec _ (lt _ _) (lt _ _) (compare _ _)); constructor; trivial.
    rewrite <- (of_to x), <- (of_to y); congruence.
  Qed.
End NIsoOptionPositive.

Module NIsoOptionPositiveOrig <: IsoOrderedTypeOrig OptionPositiveOrderedTypeBitsOrig.
  Import Structures.OrderedType.
  Include NIsoOptionPositiveCommon.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    refine match OptionPositiveOrderedTypeBitsOrig.compare (to_ x) (to_ y) with
           | LT pf => LT _
           | EQ pf => EQ (Logic.eq_trans (Logic.eq_sym (of_to _)) (Logic.eq_trans (f_equal _ (_ pf)) (of_to _)))
           | GT pf => GT _
           end;
      try assumption.
    { cbv [OptionPositiveOrderedTypeBitsOrig.eq Option.option_eq].
      clear.
      abstract now do 2 destruct to_; intuition congruence. }
  Defined.
End NIsoOptionPositiveOrig.

Module NOrderedTypeBits <: UsualOrderedType := NIsoOptionPositive.
Module NOrderedTypeBitsOrig <: UsualOrderedTypeOrig := NIsoOptionPositiveOrig.

Module NegativeOrderedTypeBits <: UsualOrderedType := FlipUsualOrderedType PositiveOrderedTypeBits.
Module NegativeOrderedTypeBitsOrig <: UsualOrderedTypeOrig := FlipUsualOrderedTypeOrig OrderedTypeEx.PositiveOrderedTypeBits.

Module SumNegNOrderedTypeBits <: UsualOrderedType := SumUsualOrderedType NegativeOrderedTypeBits NOrderedTypeBits.
Module SumNegNOrderedTypeBitsOrig <: UsualOrderedTypeOrig := SumUsualOrderedTypeOrig NegativeOrderedTypeBitsOrig NOrderedTypeBitsOrig.

Module ZIsoSumNegNCommon.
  Definition t := Z.
  Include HasUsualEq.
  Include UsualIsEq.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := Z.eq_dec.
  Definition to_ (x : t) : positive + N
    := match x with
       | Zneg p => inl p
       | Z0 => inr N0
       | Zpos p => inr (Npos p)
       end.
  Definition of_ (x : positive + N) : t
    := match x with
       | inl p => Zneg p
       | inr N0 => Z0
       | inr (Npos p) => Zpos p
       end.
  Lemma Proper_to_ : Proper (eq ==> SumNegNOrderedTypeBits.eq) to_.
  Proof. cbv [eq]; repeat intro; subst; reflexivity. Qed.
  Lemma Proper_of_ : Proper (SumNegNOrderedTypeBits.eq ==> eq) of_.
  Proof. cbv [SumNegNOrderedTypeBits.eq]; repeat intro; subst; reflexivity. Qed.
  Lemma of_to : forall x : t, eq (of_ (to_ x)) x.
  Proof. cbv [eq of_ to_]; intros; break_innermost_match; reflexivity. Qed.
  Lemma to_of : forall x : positive + N, SumNegNOrderedTypeBits.eq (to_ (of_ x)) x.
  Proof.
    intros [|[|]]; cbn; reflexivity.
  Qed.
  Definition lt (x y : t) : Prop := SumNegNOrderedTypeBits.lt (to_ x) (to_ y).
  Global Instance lt_strorder : StrictOrder lt | 100.
  Proof.
    split; hnf; cbv [lt complement]; intros *;
      apply SumNegNOrderedTypeBits.lt_strorder.
  Qed.
  Definition lt_compat : Proper (eq ==> eq ==> iff) lt := _.
  Global Instance Proper_to_lt : Proper (lt ==> SumNegNOrderedTypeBits.lt) to_ | 100.
  Proof. cbv [lt Proper respectful]; trivial. Qed.
  Global Instance Proper_of_lt : Proper (SumNegNOrderedTypeBits.lt ==> lt) of_ | 100.
  Proof. cbv [lt Proper respectful]; intros *; rewrite !to_of; trivial. Qed.
  Include BackportEq.
  Include BackportStrOrder.
End ZIsoSumNegNCommon.

Module ZIsoSumNegN <: IsoOrderedType SumNegNOrderedTypeBits.
  Include ZIsoSumNegNCommon.
  Definition compare (x y : t) : comparison := SumNegNOrderedTypeBits.compare (to_ x) (to_ y).
  Lemma compare_spec (x y : t) : CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    cbv [eq].
    destruct (SumNegNOrderedTypeBits.compare_spec (to_ x) (to_ y) : CompareSpec _ (lt _ _) (lt _ _) (compare _ _)); constructor; trivial.
    rewrite <- (of_to x), <- (of_to y); congruence.
  Qed.
End ZIsoSumNegN.

Module ZIsoSumNegNOrig <: IsoOrderedTypeOrig SumNegNOrderedTypeBitsOrig.
  Import Structures.OrderedType.
  Include ZIsoSumNegNCommon.
  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    refine match SumNegNOrderedTypeBitsOrig.compare (to_ x) (to_ y) with
           | LT pf => LT _
           | EQ pf => EQ (Logic.eq_trans (Logic.eq_sym (of_to _)) (Logic.eq_trans (f_equal _ (_ pf)) (of_to _)))
           | GT pf => GT _
           end;
      try assumption.
    { cbv [SumNegNOrderedTypeBitsOrig.eq Option.option_eq].
      clear.
      abstract now do 2 destruct to_; intuition congruence. }
  Defined.
End ZIsoSumNegNOrig.

Module ZOrderedTypeBits <: UsualOrderedType := ZIsoSumNegN.
Module ZOrderedTypeBitsOrig <: UsualOrderedTypeOrig := ZIsoSumNegNOrig.
