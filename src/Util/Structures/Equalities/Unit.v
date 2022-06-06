Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Unit.

Local Set Implicit Arguments.

Module UnitTyp <: Typ.
  Definition t := unit.
End UnitTyp.

Module UnitHasEq.
  Definition eq : relation unit := Logic.eq.
End UnitHasEq.

Module UnitIsEq.
  Global Instance eq_equiv : Equivalence (@eq unit) | 5.
  Proof. exact _. Defined.
End UnitIsEq.

Module UnitIsEqOrig.
  Definition eq_refl : Reflexive (@eq unit) := _.
  Definition eq_sym : Symmetric (@eq unit) := _.
  Definition eq_trans : Transitive (@eq unit) := _.
End UnitIsEqOrig.

Module UnitHasEqDec.
  Definition eq_dec x y : {@eq unit x y} + {~@eq unit x y}.
  Proof. left; destruct x, y; constructor. Defined.
End UnitHasEqDec.

Module UnitHasEqb.
  Definition eqb : unit -> unit -> bool := fun _ _ => true.
End UnitHasEqb.

Module UnitEqbNotation := Nop <+ EqbNotation UnitTyp UnitHasEqb.

Module UnitEqbSpec.
  Lemma eqb_eq x y : true = true <-> @eq unit x y.
  Proof. destruct x, y; cbv; repeat constructor. Qed.
End UnitEqbSpec.

Local Coercion is_true : bool >-> Sortclass.
Module UnitIsEqb <: IsEqb UnitTyp UnitHasEqb.
  Global Instance eqb_equiv : Equivalence UnitHasEqb.eqb | 5.
  Proof.
    split; cbv; repeat intros []; constructor.
  Qed.
End UnitIsEqb.

Module UnitHasEqBool := UnitHasEqb <+ UnitEqbSpec.

Module UnitUsualHasEqDec := UnitHasEqDec.
Module UnitUsualEqbSpec := UnitEqbSpec.

Module UnitHasUsualEq := Nop <+ HasUsualEq UnitTyp.
Module UnitUsualEq <: UsualEq := UnitTyp <+ HasUsualEq.
Module UnitUsualIsEq := Nop <+ UsualIsEq UnitUsualEq.
Module UnitUsualIsEqOrig := Nop <+ UsualIsEqOrig UnitUsualEq.
Module UnitMiniDecidableType <: MiniDecidableType := UnitTyp <+ UnitUsualHasEqDec.
Module UnitUsualHasEqBool := UnitHasEqb <+ UnitUsualEqbSpec.
Module UnitEq <: Eq := UnitTyp <+ UnitHasEq.
Module UnitEqualityType <: EqualityType := UnitEq <+ UnitIsEq.
Module UnitEqualityTypeOrig <: EqualityTypeOrig := UnitEq <+ UnitIsEqOrig.
Module UnitEqualityTypeBoth <: EqualityTypeBoth := UnitEq <+ UnitIsEq <+ UnitIsEqOrig.
Module UnitDecidableType <: EqualityType := UnitEqualityType <+ UnitHasEqDec.
Module UnitDecidableTypeOrig <: EqualityTypeOrig := UnitEqualityTypeOrig <+ UnitHasEqDec.
Module UnitDecidableTypeBoth <: EqualityTypeBoth := UnitEqualityTypeBoth <+ UnitHasEqDec.
Module UnitBooleanEqualityType <: BooleanEqualityType := UnitEqualityType <+ UnitHasEqb <+ UnitEqbSpec.
Module UnitBooleanDecidableType <: BooleanDecidableType := UnitBooleanEqualityType <+ UnitHasEqDec.
Module UnitDecidableTypeFull <: DecidableTypeFull := UnitEq <+ UnitIsEq <+ UnitIsEqOrig <+ UnitHasEqDec <+ UnitHasEqBool.

Module UnitEq' := UnitEq <+ EqNotation.
Module UnitEqualityType' := UnitEqualityType <+ EqNotation.
Module UnitEqualityTypeOrig' := UnitEqualityTypeOrig <+ EqNotation.
Module UnitEqualityTypeBoth' := UnitEqualityTypeBoth <+ EqNotation.
Module UnitDecidableType' := UnitDecidableType <+ EqNotation.
Module UnitDecidableTypeOrig' := UnitDecidableTypeOrig <+ EqNotation.
Module UnitDecidableTypeBoth' := UnitDecidableTypeBoth <+ EqNotation.
Module UnitBooleanEqualityType' := UnitBooleanEqualityType <+ EqNotation <+ EqbNotation.
Module UnitBooleanDecidableType' := UnitBooleanDecidableType <+ EqNotation <+ EqbNotation.
Module UnitDecidableTypeFull' := UnitDecidableTypeFull <+ EqNotation.

Module UnitUsualEqualityType <: UsualEqualityType := UnitUsualEq <+ UsualIsEq.
Module UnitUsualEqualityTypeOrig <: UsualEqualityTypeOrig := UnitUsualEq <+ UsualIsEqOrig.
Module UnitUsualEqualityTypeBoth <: UsualEqualityTypeBoth := UnitUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

Module UnitUsualDecidableType <: UsualDecidableType
:= UnitUsualEq <+ UsualIsEq <+ UnitUsualHasEqDec.
Module UnitUsualDecidableTypeOrig <: UsualDecidableTypeOrig
:= UnitUsualEq <+ UsualIsEqOrig <+ UnitUsualHasEqDec.
Module UnitUsualDecidableTypeBoth <: UsualDecidableTypeBoth
 := UnitUsualDecidableType <+ UsualIsEqOrig.
Module UnitUsualBoolEq <: UsualBoolEq
:= UnitUsualEq <+ UnitUsualHasEqBool.
Module UnitUsualDecidableTypeFull <: UsualDecidableTypeFull
 := UnitUsualEq <+ UsualIsEq <+ UsualIsEqOrig <+ UnitUsualHasEqDec <+ UnitUsualHasEqBool.

Module UnitEqbType <: EqbType := UnitTyp <+ UnitHasEqb <+ UnitIsEqb.

Module UnitBoolEqualityFacts := BoolEqualityFacts UnitBooleanEqualityType.
