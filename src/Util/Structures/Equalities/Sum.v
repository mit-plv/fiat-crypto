Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Sum.
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

Module SumHasEqDec (E1 : Equalities.DecidableType) (E2 : Equalities.DecidableType).
  Local Notation eq := (sumwise E1.eq E2.eq).
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    pose proof E1.eq_dec; pose proof E2.eq_dec.
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

Module SumUsualHasEqDec (E1 : UsualDecidableType) (E2 : UsualDecidableType).
  Definition eq_dec (x y : E1.t + E2.t) : {eq x y} + {~eq x y}.
  Proof.
    destruct x as [x|x], y as [y|y];
      [ destruct (E1.eq_dec x y); [ left | right ]
      | right
      | right
      | destruct (E2.eq_dec x y); [ left | right ] ];
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
  Module E := SumTyp E1 E2.
  Include HasUsualEq E.
End SumHasUsualEq.

Module SumUsualEq (E1 : UsualEq) (E2 : UsualEq) <: UsualEq := SumTyp E1 E2 <+ HasUsualEq.

Module SumUsualIsEq (E1 : UsualEq) (E2 : UsualEq).
  Module E := SumUsualEq E1 E2.
  Include UsualIsEq E.
End SumUsualIsEq.

Module SumUsualIsEqOrig (E1 : UsualEq) (E2 : UsualEq).
  Module E := SumUsualEq E1 E2.
  Include UsualIsEqOrig E.
End SumUsualIsEqOrig.

Module SumMiniDecidableType (E1 : MiniDecidableType) (E2 : MiniDecidableType) <: MiniDecidableType.
  Include SumTyp E1 E2.
  Module E1' := Make_UDT E1.
  Module E2' := Make_UDT E2.
  Include SumUsualHasEqDec E1' E2'.
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
Module SumDecidableType (E1 : DecidableType) (E2 : DecidableType) <: EqualityType := SumEqualityType E1 E2 <+ SumHasEqDec E1 E2.
Module SumBooleanEqualityType (E1 : BooleanEqualityType) (E2 : BooleanEqualityType) <: BooleanEqualityType := SumEqualityType E1 E2 <+ SumHasEqb E1 E2 E1 E2 <+ SumEqbSpec E1 E2 E1 E2 E1 E2 E1 E2.
Module SumBooleanDecidableType (E1 : BooleanDecidableType) (E2 : BooleanDecidableType) <: BooleanDecidableType := SumBooleanEqualityType E1 E2 <+ SumHasEqDec E1 E2.

Module SumEq' (E1 : Eq) (E2 : Eq) := SumEq E1 E2 <+ EqNotation.
Module SumEqualityType' (E1 : EqualityType) (E2 : EqualityType) := SumEqualityType E1 E2 <+ EqNotation.
Module SumDecidableType' (E1 : DecidableType) (E2 : DecidableType) := SumDecidableType E1 E2 <+ EqNotation.
Module SumBooleanEqualityType' (E1 : BooleanEqualityType) (E2 : BooleanEqualityType) := SumBooleanEqualityType E1 E2 <+ EqNotation <+ EqbNotation.
Module SumBooleanDecidableType' (E1 : BooleanDecidableType) (E2 : BooleanDecidableType) := SumBooleanDecidableType E1 E2 <+ EqNotation <+ EqbNotation.

Module SumUsualEqualityType (E1 : UsualEqualityType) (E2 : UsualEqualityType) <: UsualEqualityType := SumUsualEq E1 E2 <+ UsualIsEq.

Module SumUsualDecidableType (E1 : UsualDecidableType) (E2 : UsualDecidableType) <: UsualDecidableType
:= SumUsualEq E1 E2 <+ UsualIsEq <+ SumUsualHasEqDec E1 E2.
Module SumUsualDecidableTypeOrig (E1 : UsualDecidableType) (E2 : UsualDecidableType) <: UsualDecidableTypeOrig
:= SumUsualEq E1 E2 <+ UsualIsEqOrig <+ SumUsualHasEqDec E1 E2.
Module SumUsualDecidableTypeBoth (E1 : UsualDecidableType) (E2 : UsualDecidableType) <: UsualDecidableTypeBoth
 := SumUsualDecidableType E1 E2 <+ UsualIsEqOrig.
Module SumUsualBoolEq (E1 : UsualBoolEq) (E2 : UsualBoolEq) <: UsualBoolEq
:= SumUsualEq E1 E2 <+ SumUsualHasEqBool E1 E2.
Module SumUsualDecidableTypeFull (E1 : UsualDecidableTypeFull) (E2 : UsualDecidableTypeFull) <: UsualDecidableTypeFull
 := SumUsualEq E1 E2 <+ UsualIsEq <+ UsualIsEqOrig <+ SumUsualHasEqDec E1 E2 <+ SumUsualHasEqBool E1 E2.

Module SumEqbType (E1 : EqbType) (E2 : EqbType) <: EqbType := SumTyp E1 E2 <+ SumHasEqb E1 E2 E1 E2 <+ SumIsEqb E1 E2.
