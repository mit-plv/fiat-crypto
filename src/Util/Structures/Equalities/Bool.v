Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Bool.

Local Set Implicit Arguments.

Module BoolTyp <: Typ.
  Definition t := bool.
End BoolTyp.

Module BoolHasEq.
  Definition eq : relation bool := Logic.eq.
End BoolHasEq.

Module BoolIsEq.
  Global Instance eq_equiv : Equivalence (@eq bool) | 5.
  Proof. exact _. Defined.
End BoolIsEq.

Module BoolHasEqDec.
  Definition eq_dec x y : {@eq bool x y} + {~@eq bool x y} := Bool.bool_dec x y.
End BoolHasEqDec.

Module BoolHasEqb.
  Definition eqb : bool -> bool -> bool := Bool.eqb.
End BoolHasEqb.

Module BoolEqbNotation := Nop <+ EqbNotation BoolTyp BoolHasEqb.

Module BoolEqbSpec.
  Lemma eqb_eq x y : Bool.eqb x y = true <-> @eq bool x y.
  Proof. destruct x, y; cbv; repeat constructor; congruence. Qed.
End BoolEqbSpec.

Module BoolHasEqBool := BoolHasEqb <+ BoolEqbSpec.

Module BoolUsualHasEqDec := BoolHasEqDec.
Module BoolUsualEqbSpec := BoolEqbSpec.

Module BoolHasUsualEq := Nop <+ HasUsualEq BoolTyp.
Module BoolUsualEq <: UsualEq := BoolTyp <+ HasUsualEq.
Module BoolUsualIsEq := Nop <+ UsualIsEq BoolUsualEq.
Module BoolUsualIsEqOrig := Nop <+ UsualIsEqOrig BoolUsualEq.
Module BoolMiniDecidableType <: MiniDecidableType := BoolTyp <+ BoolUsualHasEqDec.
Module BoolUsualHasEqBool := BoolHasEqb <+ BoolUsualEqbSpec.
Module BoolEq <: Eq := BoolTyp <+ BoolHasEq.
Module BoolEqualityType <: EqualityType := BoolEq <+ BoolIsEq.
Module BoolDecidableType <: EqualityType := BoolEqualityType <+ BoolHasEqDec.
Module BoolBooleanEqualityType <: BooleanEqualityType := BoolEqualityType <+ BoolHasEqb <+ BoolEqbSpec.
Module BoolBooleanDecidableType <: BooleanDecidableType := BoolBooleanEqualityType <+ BoolHasEqDec.

Module BoolEq' := BoolEq <+ EqNotation.
Module BoolEqualityType' := BoolEqualityType <+ EqNotation.
Module BoolDecidableType' := BoolDecidableType <+ EqNotation.
Module BoolBooleanEqualityType' := BoolBooleanEqualityType <+ EqNotation <+ EqbNotation.
Module BoolBooleanDecidableType' := BoolBooleanDecidableType <+ EqNotation <+ EqbNotation.

Module BoolUsualEqualityType <: UsualEqualityType := BoolUsualEq <+ UsualIsEq.

Module BoolUsualDecidableType <: UsualDecidableType
:= BoolUsualEq <+ UsualIsEq <+ BoolUsualHasEqDec.
Module BoolUsualDecidableTypeOrig <: UsualDecidableTypeOrig
:= BoolUsualEq <+ UsualIsEqOrig <+ BoolUsualHasEqDec.
Module BoolUsualDecidableTypeBoth <: UsualDecidableTypeBoth
 := BoolUsualDecidableType <+ UsualIsEqOrig.
Module BoolUsualBoolEq <: UsualBoolEq
:= BoolUsualEq <+ BoolUsualHasEqBool.
Module BoolUsualDecidableTypeFull <: UsualDecidableTypeFull
 := BoolUsualEq <+ UsualIsEq <+ UsualIsEqOrig <+ BoolUsualHasEqDec <+ BoolUsualHasEqBool.
