Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.
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

Module BoolIsEqOrig.
  Definition eq_refl : Reflexive (@eq bool) := _.
  Definition eq_sym : Symmetric (@eq bool) := _.
  Definition eq_trans : Transitive (@eq bool) := _.
End BoolIsEqOrig.

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
Module BoolEqualityTypeOrig <: EqualityTypeOrig := BoolEq <+ BoolIsEqOrig.
Module BoolEqualityTypeBoth <: EqualityTypeBoth := BoolEq <+ BoolIsEq <+ BoolIsEqOrig.
Module BoolDecidableType <: EqualityType := BoolEqualityType <+ BoolHasEqDec.
Module BoolDecidableTypeOrig <: EqualityTypeOrig := BoolEqualityTypeOrig <+ BoolHasEqDec.
Module BoolDecidableTypeBoth <: EqualityTypeBoth := BoolEqualityTypeBoth <+ BoolHasEqDec.
Module BoolBooleanEqualityType <: BooleanEqualityType := BoolEqualityType <+ BoolHasEqb <+ BoolEqbSpec.
Module BoolBooleanDecidableType <: BooleanDecidableType := BoolBooleanEqualityType <+ BoolHasEqDec.
Module BoolDecidableTypeFull <: DecidableTypeFull := BoolEq <+ BoolIsEq <+ BoolIsEqOrig <+ BoolHasEqDec <+ BoolHasEqBool.

Module BoolEq' := BoolEq <+ EqNotation.
Module BoolEqualityType' := BoolEqualityType <+ EqNotation.
Module BoolEqualityTypeOrig' := BoolEqualityTypeOrig <+ EqNotation.
Module BoolEqualityTypeBoth' := BoolEqualityTypeBoth <+ EqNotation.
Module BoolDecidableType' := BoolDecidableType <+ EqNotation.
Module BoolDecidableTypeOrig' := BoolDecidableTypeOrig <+ EqNotation.
Module BoolDecidableTypeBoth' := BoolDecidableTypeBoth <+ EqNotation.
Module BoolBooleanEqualityType' := BoolBooleanEqualityType <+ EqNotation <+ EqbNotation.
Module BoolBooleanDecidableType' := BoolBooleanDecidableType <+ EqNotation <+ EqbNotation.
Module BoolDecidableTypeFull' := BoolDecidableTypeFull <+ EqNotation.

Module BoolUsualEqualityType <: UsualEqualityType := BoolUsualEq <+ UsualIsEq.
Module BoolUsualEqualityTypeOrig <: UsualEqualityTypeOrig := BoolUsualEq <+ UsualIsEqOrig.
Module BoolUsualEqualityTypeBoth <: UsualEqualityTypeBoth := BoolUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

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
Local Coercion is_true : bool >-> Sortclass.
Module BoolIsEqb <: IsEqb BoolTyp BoolHasEqb.
  Global Instance eqb_equiv : Equivalence Bool.eqb | 5.
  Proof.
    split; cbv; repeat intros []; constructor.
  Qed.
End BoolIsEqb.

Module BoolEqbType <: EqbType := BoolTyp <+ BoolHasEqb <+ BoolIsEqb.

Module BoolBoolEqualityFacts := BoolEqualityFacts BoolBooleanEqualityType.
