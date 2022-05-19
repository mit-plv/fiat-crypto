Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Structures.Equalities.

Local Set Implicit Arguments.

Module SumTyp (E1 : Typ) (E2 : Typ) <: Typ.
  Definition t := (E1.t + E2.t)%type.
End SumTyp.

Module SumHasEq (E1 : Eq) (E2 : Eq).
  Definition eq : relation (E1.t + E2.t) := sumwise E1.eq E2.eq.
End SumHasEq.

Module SumIsEq (E1 : EqualityType) (E2 : EqualityType).
  Local Notation eq := (sumwise E1.eq E2.eq).
  Global Instance eq_equiv : Equivalence eq | 5.
  Proof.
    constructor; exact _.
  Defined.
End SumIsEq.

Module SumIsEqOrig (E1 : EqualityTypeOrig) (E2 : EqualityTypeOrig).
  Local Notation eq := (sumwise E1.eq E2.eq).
  Definition eq_refl : Reflexive eq.
  Proof. repeat intro; destruct_head'_sum; (apply E1.eq_refl + apply E2.eq_refl). Defined.
  Definition eq_sym : Symmetric eq.
  Proof. repeat intro; destruct_head'_sum; (apply E1.eq_sym + apply E2.eq_sym + idtac); eassumption. Defined.
  Definition eq_trans : Transitive eq.
  Proof. repeat intro; destruct_head'_sum; cbv [eq] in *; (eapply E1.eq_trans + eapply E2.eq_trans + idtac + exfalso); eassumption. Defined.
End SumIsEqOrig.

Module SumHasEqDec (E1 : Eq) (E2 : Eq) (E1Dec : HasEqDec E1) (E2Dec : HasEqDec E2).
  Local Notation eq := (sumwise E1.eq E2.eq).
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    pose proof E1Dec.eq_dec; pose proof E2Dec.eq_dec.
    unshelve eapply dec_sumwise; eauto.
  Defined.
End SumHasEqDec.

Module SumHasEqb (E1 : Typ) (E2 : Typ) (E1b : HasEqb E1) (E2b : HasEqb E2).
  Definition eqb := sum_beq _ _ E1b.eqb E2b.eqb.
End SumHasEqb.

Module SumEqbNotation (E1 : Typ) (E2 : Typ) (E1s : HasEqb E1) (E2s : HasEqb E2).
  Module Import _SumEqbNotation.
    Module T := SumTyp E1 E2.
    Module E := SumHasEqb E1 E2 E1s E2s.
  End _SumEqbNotation.
  Include EqbNotation T E.
End SumEqbNotation.

Module SumEqbSpec (E1 : Typ) (E2 : Typ) (E1e : HasEq E1) (E2e : HasEq E2) (E1b : HasEqb E1) (E2b : HasEqb E2) (E1s : EqbSpec E1 E1e E1b) (E2s : EqbSpec E2 E2e E2b).
  Local Notation eq := (sumwise E1e.eq E2e.eq).
  Local Notation eqb := (sum_beq _ _ E1b.eqb E2b.eqb).
  Lemma eqb_eq x y : eqb x y = true <-> eq x y.
  Proof.
    destruct x as [x|x], y as [y|y]; cbv [sumwise sum_beq];
      try apply E1s.eqb_eq;
      try apply E2s.eqb_eq;
      intuition congruence.
  Qed.
End SumEqbSpec.

Module SumHasEqBool (E1 : Eq) (E2 : Eq) (E1s : HasEqBool E1) (E2s : HasEqBool E2) := SumHasEqb E1 E2 E1s E2s <+ SumEqbSpec E1 E2 E1 E2 E1s E2s E1s E2s.

Module SumUsualHasEqDec (E1 : UsualEq) (E2 : UsualEq) (E1Dec : HasEqDec E1) (E2Dec : HasEqDec E2).
  Definition eq_dec (x y : E1.t + E2.t) : {eq x y} + {~eq x y}.
  Proof.
    destruct x as [x|x], y as [y|y];
      [ destruct (E1Dec.eq_dec x y); [ left | right ]
      | right
      | right
      | destruct (E2Dec.eq_dec x y); [ left | right ] ];
      repeat first [ apply f_equal
                   | assumption
                   | intro
                   | progress inversion_sum
                   | solve [ auto with nocore ] ].
  Defined.
End SumUsualHasEqDec.

Module SumUsualEqbSpec (E1 : UsualBoolEq) (E2 : UsualBoolEq).
  Lemma eqb_eq x y : @sum_beq _ _ E1.eqb E2.eqb x y = true <-> eq x y.
  Proof.
    destruct x as [x|x], y as [y|y]; cbn;
      rewrite ?E1.eqb_eq, ?E2.eqb_eq;
      intuition congruence.
  Qed.
End SumUsualEqbSpec.

Module SumHasUsualEq (E1 : UsualEq) (E2 : UsualEq).
  Module Import _SumHasUsualEq.
    Module E' := SumTyp E1 E2.
  End _SumHasUsualEq.
  Include HasUsualEq E'.
End SumHasUsualEq.

Module SumUsualEq (E1 : UsualEq) (E2 : UsualEq) <: UsualEq := SumTyp E1 E2 <+ HasUsualEq.

Module SumUsualIsEq (E1 : UsualEq) (E2 : UsualEq).
  Module Import _SumUsualIsEq.
    Module E' := SumUsualEq E1 E2.
  End _SumUsualIsEq.
  Include UsualIsEq E'.
End SumUsualIsEq.

Module SumUsualIsEqOrig (E1 : UsualEq) (E2 : UsualEq).
  Module Import _SumUsualIsEqOrig.
    Module E' := SumUsualEq E1 E2.
  End _SumUsualIsEqOrig.
  Include UsualIsEqOrig E'.
End SumUsualIsEqOrig.

Module SumMiniDecidableType (E1 : MiniDecidableType) (E2 : MiniDecidableType) <: MiniDecidableType.
  Include SumTyp E1 E2.
  Module Import _SumMiniDecidableType.
    Module E1' := Make_UDT E1.
    Module E2' := Make_UDT E2.
  End _SumMiniDecidableType.
  Include SumUsualHasEqDec E1' E2' E1' E2'.
End SumMiniDecidableType.

Local Coercion is_true : bool >-> Sortclass.
Module SumIsEqb (E1 : EqbType) (E2 : EqbType).
  Global Instance eqb_equiv : Equivalence (sum_beq _ _ E1.eqb E2.eqb) | 5.
  Proof.
    destruct E1.eqb_equiv, E2.eqb_equiv.
    split; repeat intros [|]; cbv in *; try congruence; eauto.
  Qed.
End SumIsEqb.

Module SumUsualHasEqBool (E1 : UsualBoolEq) (E2 : UsualBoolEq) := SumHasEqb E1 E2 E1 E2 <+ SumUsualEqbSpec E1 E2.

Module SumEq (E1 : Eq) (E2 : Eq) <: Eq := SumTyp E1 E2 <+ SumHasEq E1 E2.
Module SumEqualityType (E1 : EqualityType) (E2 : EqualityType) <: EqualityType := SumEq E1 E2 <+ SumIsEq E1 E2.
Module SumEqualityTypeOrig (E1 : EqualityTypeOrig) (E2 : EqualityTypeOrig) <: EqualityTypeOrig := SumEq E1 E2 <+ SumIsEqOrig E1 E2.
Module SumEqualityTypeBoth (E1 : EqualityTypeBoth) (E2 : EqualityTypeBoth) <: EqualityTypeBoth := SumEq E1 E2 <+ SumIsEq E1 E2 <+ SumIsEqOrig E1 E2.
Module SumDecidableType (E1 : DecidableType) (E2 : DecidableType) <: EqualityType := SumEqualityType E1 E2 <+ SumHasEqDec E1 E2 E1 E2.
Module SumDecidableTypeOrig (E1 : DecidableTypeOrig) (E2 : DecidableTypeOrig) <: EqualityTypeOrig := SumEqualityTypeOrig E1 E2 <+ SumHasEqDec E1 E2 E1 E2.
Module SumDecidableTypeBoth (E1 : DecidableTypeBoth) (E2 : DecidableTypeBoth) <: EqualityTypeBoth := SumEqualityTypeBoth E1 E2 <+ SumHasEqDec E1 E2 E1 E2.
Module SumBooleanEqualityType (E1 : BooleanEqualityType) (E2 : BooleanEqualityType) <: BooleanEqualityType := SumEqualityType E1 E2 <+ SumHasEqb E1 E2 E1 E2 <+ SumEqbSpec E1 E2 E1 E2 E1 E2 E1 E2.
Module SumBooleanDecidableType (E1 : BooleanDecidableType) (E2 : BooleanDecidableType) <: BooleanDecidableType := SumBooleanEqualityType E1 E2 <+ SumHasEqDec E1 E2 E1 E2.
Module SumDecidableTypeFull (E1 : DecidableTypeFull) (E2 : DecidableTypeFull) <: DecidableTypeFull := SumEq E1 E2 <+ SumIsEq E1 E2 <+ SumIsEqOrig E1 E2 <+ SumHasEqDec E1 E2 E1 E2 <+ SumHasEqBool E1 E2 E1 E2.

Module SumEq' (E1 : Eq) (E2 : Eq) := SumEq E1 E2 <+ EqNotation.
Module SumEqualityType' (E1 : EqualityType) (E2 : EqualityType) := SumEqualityType E1 E2 <+ EqNotation.
Module SumEqualityTypeOrig' (E1 : EqualityTypeOrig) (E2 : EqualityTypeOrig) := SumEqualityTypeOrig E1 E2 <+ EqNotation.
Module SumEqualityTypeBoth' (E1 : EqualityTypeBoth) (E2 : EqualityTypeBoth) := SumEqualityTypeBoth E1 E2 <+ EqNotation.
Module SumDecidableType' (E1 : DecidableType) (E2 : DecidableType) := SumDecidableType E1 E2 <+ EqNotation.
Module SumDecidableTypeOrig' (E1 : DecidableTypeOrig) (E2 : DecidableTypeOrig) := SumDecidableTypeOrig E1 E2 <+ EqNotation.
Module SumDecidableTypeBoth' (E1 : DecidableTypeBoth) (E2 : DecidableTypeBoth) := SumDecidableTypeBoth E1 E2 <+ EqNotation.
Module SumBooleanEqualityType' (E1 : BooleanEqualityType) (E2 : BooleanEqualityType) := SumBooleanEqualityType E1 E2 <+ EqNotation <+ EqbNotation.
Module SumBooleanDecidableType' (E1 : BooleanDecidableType) (E2 : BooleanDecidableType) := SumBooleanDecidableType E1 E2 <+ EqNotation <+ EqbNotation.
Module SumDecidableTypeFull' (E1 : DecidableTypeFull) (E2 : DecidableTypeFull) := SumDecidableTypeFull E1 E2 <+ EqNotation.

Module SumUsualEqualityType (E1 : UsualEq) (E2 : UsualEq) <: UsualEqualityType := SumUsualEq E1 E2 <+ UsualIsEq.
Module SumUsualEqualityTypeOrig (E1 : UsualEq) (E2 : UsualEq) <: UsualEqualityTypeOrig := SumUsualEq E1 E2 <+ UsualIsEqOrig.
Module SumUsualEqualityTypeBoth (E1 : UsualEq) (E2 : UsualEq) <: UsualEqualityTypeBoth := SumUsualEq E1 E2 <+ UsualIsEq <+ UsualIsEqOrig.

Module SumUsualDecidableType (E1 : UsualDecidableType) (E2 : UsualDecidableType) <: UsualDecidableType
:= SumUsualEq E1 E2 <+ UsualIsEq <+ SumUsualHasEqDec E1 E2 E1 E2.
Module SumUsualDecidableTypeOrig (E1 : UsualDecidableTypeOrig) (E2 : UsualDecidableTypeOrig) <: UsualDecidableTypeOrig
:= SumUsualEq E1 E2 <+ UsualIsEqOrig <+ SumUsualHasEqDec E1 E2 E1 E2.
Module SumUsualDecidableTypeBoth (E1 : UsualDecidableTypeBoth) (E2 : UsualDecidableTypeBoth) <: UsualDecidableTypeBoth
 := SumUsualDecidableType E1 E2 <+ UsualIsEqOrig.
Module SumUsualBoolEq (E1 : UsualBoolEq) (E2 : UsualBoolEq) <: UsualBoolEq
:= SumUsualEq E1 E2 <+ SumUsualHasEqBool E1 E2.
Module SumUsualDecidableTypeFull (E1 : UsualDecidableTypeFull) (E2 : UsualDecidableTypeFull) <: UsualDecidableTypeFull
 := SumUsualEq E1 E2 <+ UsualIsEq <+ UsualIsEqOrig <+ SumUsualHasEqDec E1 E2 E1 E2 <+ SumUsualHasEqBool E1 E2.

Module SumEqbType (E1 : EqbType) (E2 : EqbType) <: EqbType := SumTyp E1 E2 <+ SumHasEqb E1 E2 E1 E2 <+ SumIsEqb E1 E2.
