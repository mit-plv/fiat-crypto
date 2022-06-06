Require Import Coq.Classes.Morphisms.
Require Import Coq.Structures.Equalities.
Require Export Crypto.Util.FixCoqMistakes.

Module Type UsualEqualityTypeOrig <: EqualityTypeOrig
 := UsualEq <+ UsualIsEqOrig.
Module Type UsualEqualityTypeBoth <: EqualityTypeBoth
 := UsualEq <+ UsualIsEq <+ UsualIsEqOrig.

Local Coercion is_true : bool >-> Sortclass.
Module Type IsEqb (Import E : Typ) (Import Eb:HasEqb E).
#[global]
  Declare Instance eqb_equiv : Equivalence eqb.
End IsEqb.

Module IsEqbFacts (Import E : Typ) (Import Eb:HasEqb E) (Import E' : IsEqb E Eb).
  #[global]
   Instance eqb_Proper : Proper (eqb ==> eqb ==> eq) eqb | 10.
  Proof.
    intros x x' Hx y y' Hy; destruct (eqb x y) eqn:Hxy, (eqb x' y') eqn:Hxy'; try reflexivity;
      (rewrite <- Hxy + rewrite <- Hxy'); (idtac + symmetry);
      (change (is_true (eqb x' y')) + change (is_true (eqb x y))).
    all: etransitivity; (idtac + symmetry); (idtac + etransitivity); eassumption.
  Qed.
End IsEqbFacts.

Module Type EqbType := Typ <+ HasEqb <+ IsEqb.
Module Type EqbType' := Typ <+ HasEqb <+ IsEqb <+ EqbNotation.
