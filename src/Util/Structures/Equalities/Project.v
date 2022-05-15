Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.

Local Set Implicit Arguments.

(* Workaround COQBUG(https://github.com/coq/coq/issues/16024) *)
Module ProjectTyp (E : Typ) <: Typ.
  Definition t := E.t.
End ProjectTyp.
Module ProjectHasEq (E : Eq) <: HasEq E.
  Definition eq := E.eq.
End ProjectHasEq.
Module ProjectIsEq (E : EqualityType).
  Definition eq_equiv := E.eq_equiv.
End ProjectIsEq.
Module ProjectHasEqDec (E : Equalities.DecidableType).
  Definition eq_dec := E.eq_dec.
End ProjectHasEqDec.
Module ProjectHasEqb (E : Typ) (Eb : HasEqb E).
  Definition eqb := Eb.eqb.
End ProjectHasEqb.
Module ProjectEqbSpec (E : Typ) (Ee : HasEq E) (Eb : HasEqb E) (Es : EqbSpec E Ee Eb).
  Definition eqb_eq := Es.eqb_eq.
End ProjectEqbSpec.
Module ProjectHasEqBool (E : Eq) (Es : HasEqBool E) := Es.
Module ProjectUsualHasEqDec (E : UsualDecidableType) := ProjectHasEqDec E.
Module ProjectUsualEqbSpec (E : UsualBoolEq).
  Definition eqb_eq := E.eqb_eq.
End ProjectUsualEqbSpec.
Module ProjectHasUsualEq (E : UsualEq) := Nop <+ HasUsualEq E.
Module ProjectUsualEq (E : UsualEq) <: UsualEq := ProjectTyp E <+ HasUsualEq.
Module ProjectUsualIsEq (E : UsualEq) := Nop <+ UsualIsEq E.
Module ProjectUsualIsEqOrig (E : UsualEq) := Nop <+ UsualIsEqOrig E.
Module ProjectMiniDecidableType (E : MiniDecidableType) <: MiniDecidableType := E.
Module ProjectIsEqb (E : EqbType).
  Definition eqb_equiv := E.eqb_equiv.
End ProjectIsEqb.

Module ProjectUsualHasEqBool (E : UsualBoolEq) := ProjectHasEqb E E <+ ProjectUsualEqbSpec E.

Module ProjectEq (E : Eq) <: Eq := ProjectTyp E <+ ProjectHasEq E.
Module ProjectEqualityType (E : EqualityType) <: EqualityType := ProjectEq E <+ ProjectIsEq E.
Module ProjectDecidableType (E : DecidableType) <: EqualityType := ProjectEqualityType E <+ ProjectHasEqDec E.
Module ProjectBooleanEqualityType (E : BooleanEqualityType) <: BooleanEqualityType := ProjectEqualityType E <+ ProjectHasEqb E E <+ ProjectEqbSpec E E E E.
Module ProjectBooleanDecidableType (E : BooleanDecidableType) <: BooleanDecidableType := ProjectBooleanEqualityType E <+ ProjectHasEqDec E.

Module ProjectEq' (E : Eq) := ProjectEq E <+ EqNotation.
Module ProjectEqualityType' (E : EqualityType) := ProjectEqualityType E <+ EqNotation.
Module ProjectDecidableType' (E : DecidableType) := ProjectDecidableType E <+ EqNotation.
Module ProjectBooleanEqualityType' (E : BooleanEqualityType) := ProjectBooleanEqualityType E <+ EqNotation <+ EqbNotation.
Module ProjectBooleanDecidableType' (E : BooleanDecidableType) := ProjectBooleanDecidableType E <+ EqNotation <+ EqbNotation.

Module ProjectUsualEqualityType (E : UsualEqualityType) <: UsualEqualityType := ProjectUsualEq E <+ UsualIsEq.

Module ProjectUsualDecidableType (E : UsualDecidableType) <: UsualDecidableType
:= ProjectUsualEq E <+ UsualIsEq <+ ProjectUsualHasEqDec E.
Module ProjectUsualDecidableTypeOrig (E : UsualDecidableType) <: UsualDecidableTypeOrig
:= ProjectUsualEq E <+ UsualIsEqOrig <+ ProjectUsualHasEqDec E.
Module ProjectUsualDecidableTypeBoth (E : UsualDecidableType) <: UsualDecidableTypeBoth
 := ProjectUsualDecidableType E <+ UsualIsEqOrig.
Module ProjectUsualBoolEq (E : UsualBoolEq) <: UsualBoolEq
:= ProjectUsualEq E <+ ProjectUsualHasEqBool E.
Module ProjectUsualDecidableTypeFull (E : UsualDecidableTypeFull) <: UsualDecidableTypeFull
 := ProjectUsualEq E <+ UsualIsEq <+ UsualIsEqOrig <+ ProjectUsualHasEqDec E <+ ProjectUsualHasEqBool E.

Module ProjectEqbType (E : EqbType) <: EqbType := ProjectTyp E <+ ProjectHasEqb E E <+ ProjectIsEqb E.
