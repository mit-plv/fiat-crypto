Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
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
Module UnitDecidableType <: EqualityType := UnitEqualityType <+ UnitHasEqDec.
Module UnitBooleanEqualityType <: BooleanEqualityType := UnitEqualityType <+ UnitHasEqb <+ UnitEqbSpec.
Module UnitBooleanDecidableType <: BooleanDecidableType := UnitBooleanEqualityType <+ UnitHasEqDec.

Module UnitEq' := UnitEq <+ EqNotation.
Module UnitEqualityType' := UnitEqualityType <+ EqNotation.
Module UnitDecidableType' := UnitDecidableType <+ EqNotation.
Module UnitBooleanEqualityType' := UnitBooleanEqualityType <+ EqNotation <+ EqbNotation.
Module UnitBooleanDecidableType' := UnitBooleanDecidableType <+ EqNotation <+ EqbNotation.

Module UnitUsualEqualityType <: UsualEqualityType := UnitUsualEq <+ UsualIsEq.

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
