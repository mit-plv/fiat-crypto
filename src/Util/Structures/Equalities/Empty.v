Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.

Local Set Implicit Arguments.

Module EmptyTyp <: Typ.
  Definition t := Empty_set.
End EmptyTyp.

Module EmptyHasEq.
  Definition eq : relation Empty_set := Logic.eq.
End EmptyHasEq.

Module EmptyIsEq.
  Global Instance eq_equiv : Equivalence (@eq Empty_set) | 5.
  Proof. exact _. Defined.
End EmptyIsEq.

Module EmptyIsEqOrig.
  Definition eq_refl : Reflexive (@eq Empty_set) := _.
  Definition eq_sym : Symmetric (@eq Empty_set) := _.
  Definition eq_trans : Transitive (@eq Empty_set) := _.
End EmptyIsEqOrig.

Module EmptyHasEqDec.
  Definition eq_dec x y : {@eq Empty_set x y} + {~@eq Empty_set x y}.
  Proof. left; destruct x, y; constructor. Defined.
End EmptyHasEqDec.

Module EmptyHasEqb.
  Definition eqb : Empty_set -> Empty_set -> bool := fun _ _ => true.
End EmptyHasEqb.

Module EmptyEqbNotation := Nop <+ EqbNotation EmptyTyp EmptyHasEqb.

Module EmptyEqbSpec.
  Lemma eqb_eq x y : true = true <-> @eq Empty_set x y.
  Proof. destruct x, y; cbv; repeat constructor. Qed.
End EmptyEqbSpec.

Local Coercion is_true : bool >-> Sortclass.
Module EmptyIsEqb <: IsEqb EmptyTyp EmptyHasEqb.
  Global Instance eqb_equiv : Equivalence EmptyHasEqb.eqb | 5.
  Proof.
    split; cbv; repeat intros []; constructor.
  Qed.
End EmptyIsEqb.

Module EmptyHasEqBool := EmptyHasEqb <+ EmptyEqbSpec.

Module EmptyUsualHasEqDec := EmptyHasEqDec.
Module EmptyUsualEqbSpec := EmptyEqbSpec.

Module EmptyHasUsualEq := Nop <+ HasUsualEq EmptyTyp.
Module EmptyUsualEq <: UsualEq := EmptyTyp <+ HasUsualEq.
Module EmptyUsualIsEq := Nop <+ UsualIsEq EmptyUsualEq.
Module EmptyUsualIsEqOrig := Nop <+ UsualIsEqOrig EmptyUsualEq.
Module EmptyMiniDecidableType <: MiniDecidableType := EmptyTyp <+ EmptyUsualHasEqDec.
Module EmptyUsualHasEqBool := EmptyHasEqb <+ EmptyUsualEqbSpec.
Module EmptyEq <: Eq := EmptyTyp <+ EmptyHasEq.
Module EmptyEqualityType <: EqualityType := EmptyEq <+ EmptyIsEq.
Module EmptyEqualityTypeOrig <: EqualityTypeOrig := EmptyEq <+ EmptyIsEqOrig.
Module EmptyEqualityTypeBoth <: EqualityTypeBoth := EmptyEq <+ EmptyIsEq <+ EmptyIsEqOrig.
Module EmptyDecidableType <: EqualityType := EmptyEqualityType <+ EmptyHasEqDec.
Module EmptyDecidableTypeOrig <: EqualityTypeOrig := EmptyEqualityTypeOrig <+ EmptyHasEqDec.
Module EmptyDecidableTypeBoth <: EqualityTypeBoth := EmptyEqualityTypeBoth <+ EmptyHasEqDec.
Module EmptyBooleanEqualityType <: BooleanEqualityType := EmptyEqualityType <+ EmptyHasEqb <+ EmptyEqbSpec.
Module EmptyBooleanDecidableType <: BooleanDecidableType := EmptyBooleanEqualityType <+ EmptyHasEqDec.
Module EmptyDecidableTypeFull <: DecidableTypeFull := EmptyEq <+ EmptyIsEq <+ EmptyIsEqOrig <+ EmptyHasEqDec <+ EmptyHasEqBool.

Module EmptyEq' := EmptyEq <+ EqNotation.
Module EmptyEqualityType' := EmptyEqualityType <+ EqNotation.
Module EmptyEqualityTypeOrig' := EmptyEqualityTypeOrig <+ EqNotation.
Module EmptyEqualityTypeBoth' := EmptyEqualityTypeBoth <+ EqNotation.
Module EmptyDecidableType' := EmptyDecidableType <+ EqNotation.
Module EmptyDecidableTypeOrig' := EmptyDecidableTypeOrig <+ EqNotation.
Module EmptyDecidableTypeBoth' := EmptyDecidableTypeBoth <+ EqNotation.
Module EmptyBooleanEqualityType' := EmptyBooleanEqualityType <+ EqNotation <+ EqbNotation.
Module EmptyBooleanDecidableType' := EmptyBooleanDecidableType <+ EqNotation <+ EqbNotation.
Module EmptyDecidableTypeFull' := EmptyDecidableTypeFull <+ EqNotation.

Module EmptyUsualEqualityType <: UsualEqualityType := EmptyUsualEq <+ UsualIsEq.
Module EmptyUsualEqualityTypeOrig <: UsualEqualityTypeOrig := EmptyUsualEq <+ UsualIsEqOrig.
Module EmptyUsualEqualityTypeBoth <: UsualEqualityTypeBoth := EmptyUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

Module EmptyUsualDecidableType <: UsualDecidableType
:= EmptyUsualEq <+ UsualIsEq <+ EmptyUsualHasEqDec.
Module EmptyUsualDecidableTypeOrig <: UsualDecidableTypeOrig
:= EmptyUsualEq <+ UsualIsEqOrig <+ EmptyUsualHasEqDec.
Module EmptyUsualDecidableTypeBoth <: UsualDecidableTypeBoth
 := EmptyUsualDecidableType <+ UsualIsEqOrig.
Module EmptyUsualBoolEq <: UsualBoolEq
:= EmptyUsualEq <+ EmptyUsualHasEqBool.
Module EmptyUsualDecidableTypeFull <: UsualDecidableTypeFull
 := EmptyUsualEq <+ UsualIsEq <+ UsualIsEqOrig <+ EmptyUsualHasEqDec <+ EmptyUsualHasEqBool.

Module EmptyEqbType <: EqbType := EmptyTyp <+ EmptyHasEqb <+ EmptyIsEqb.

Module EmptyBoolEqualityFacts := BoolEqualityFacts EmptyBooleanEqualityType.
