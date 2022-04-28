Require Import Coq.Classes.RelationPairs.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Prod.

Local Set Implicit Arguments.

Module ProdTyp (E1 : Typ) (E2 : Typ) <: Typ.
  Definition t := (E1.t * E2.t)%type.
End ProdTyp.

Module ProdHasEq (E1 : Eq) (E2 : Eq).
  Definition eq : relation (E1.t * E2.t) := RelProd E1.eq E2.eq.
End ProdHasEq.

Module ProdIsEq (E1 : EqualityType) (E2 : EqualityType).
  Local Notation eq := (RelProd E1.eq E2.eq).
  Global Instance eq_equiv : Equivalence eq | 5.
  Proof.
    constructor; exact _.
  Defined.
End ProdIsEq.

Module ProdHasEqDec (E1 : Equalities.DecidableType) (E2 : Equalities.DecidableType).
  Local Notation eq := (RelProd E1.eq E2.eq).
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    destruct (E1.eq_dec (fst x) (fst y)); [ destruct (E2.eq_dec (snd x) (snd y)); [ left; split | right; intros [? ?] ] | right; intros [? ?] ]; auto with nocore.
  Defined.
End ProdHasEqDec.

Module ProdHasEqb (E1 : Typ) (E2 : Typ) (E1b : HasEqb E1) (E2b : HasEqb E2).
  Definition eqb := prod_beq _ _ E1b.eqb E2b.eqb.
End ProdHasEqb.

Module ProdEqbNotation (E1 : Typ) (E2 : Typ) (E1s : HasEqb E1) (E2s : HasEqb E2).
  Module Import _ProdEqbNotation.
    Module T := ProdTyp E1 E2.
    Module E := ProdHasEqb E1 E2 E1s E2s.
  End _ProdEqbNotation.
  Include EqbNotation T E.
End ProdEqbNotation.

Module ProdEqbSpec (E1 : Typ) (E2 : Typ) (E1e : HasEq E1) (E2e : HasEq E2) (E1b : HasEqb E1) (E2b : HasEqb E2) (E1s : EqbSpec E1 E1e E1b) (E2s : EqbSpec E2 E2e E2b).
  Local Notation eq := (RelProd E1e.eq E2e.eq).
  Local Notation eqb := (prod_beq _ _ E1b.eqb E2b.eqb).
  Lemma eqb_eq x y : eqb x y = true <-> eq x y.
  Proof.
    destruct x as [x1 x2], y as [y1 y2]; cbv [eqb];
      rewrite Bool.andb_true_iff, E1s.eqb_eq, E2s.eqb_eq; reflexivity.
  Qed.
End ProdEqbSpec.

Module ProdHasEqBool (E1 : Eq) (E2 : Eq) (E1s : HasEqBool E1) (E2s : HasEqBool E2) := ProdHasEqb E1 E2 E1s E2s <+ ProdEqbSpec E1 E2 E1 E2 E1s E2s E1s E2s.

Module ProdUsualHasEqDec (E1 : UsualDecidableType) (E2 : UsualDecidableType).
  Definition eq_dec (x y : E1.t * E2.t) : {eq x y} + {~eq x y}.
  Proof.
    destruct (E1.eq_dec (fst x) (fst y)); [ destruct (E2.eq_dec (snd x) (snd y)); [ left; destruct x, y | right; intro; subst y; destruct x ] | right; intro; subst y; destruct x ]; cbn in *; subst; try reflexivity; eauto using eq_refl with nocore.
  Defined.
End ProdUsualHasEqDec.

Module ProdUsualEqbSpec (E1 : UsualBoolEq) (E2 : UsualBoolEq).
  Lemma eqb_eq x y : @prod_beq _ _ E1.eqb E2.eqb x y = true <-> eq x y.
  Proof.
    destruct x as [x1 x2], y as [y1 y2]; cbv [prod_beq].
    rewrite Bool.andb_true_iff, E1.eqb_eq, E2.eqb_eq;
      intuition congruence.
  Qed.
End ProdUsualEqbSpec.

Module ProdHasUsualEq (E1 : UsualEq) (E2 : UsualEq).
  Module E := ProdTyp E1 E2.
  Include HasUsualEq E.
End ProdHasUsualEq.

Module ProdUsualEq (E1 : UsualEq) (E2 : UsualEq) <: UsualEq := ProdTyp E1 E2 <+ HasUsualEq.

Module ProdUsualIsEq (E1 : UsualEq) (E2 : UsualEq).
  Module E := ProdUsualEq E1 E2.
  Include UsualIsEq E.
End ProdUsualIsEq.

Module ProdUsualIsEqOrig (E1 : UsualEq) (E2 : UsualEq).
  Module E := ProdUsualEq E1 E2.
  Include UsualIsEqOrig E.
End ProdUsualIsEqOrig.

Module ProdMiniDecidableType (E1 : MiniDecidableType) (E2 : MiniDecidableType) <: MiniDecidableType.
  Include ProdTyp E1 E2.
  Module E1' := Make_UDT E1.
  Module E2' := Make_UDT E2.
  Include ProdUsualHasEqDec E1' E2'.
End ProdMiniDecidableType.

Module ProdUsualHasEqBool (E1 : UsualBoolEq) (E2 : UsualBoolEq) := ProdHasEqb E1 E2 E1 E2 <+ ProdUsualEqbSpec E1 E2.

Module ProdEq (E1 : Eq) (E2 : Eq) <: Eq := ProdTyp E1 E2 <+ ProdHasEq E1 E2.
Module ProdEqualityType (E1 : EqualityType) (E2 : EqualityType) <: EqualityType := ProdEq E1 E2 <+ ProdIsEq E1 E2.
Module ProdDecidableType (E1 : DecidableType) (E2 : DecidableType) <: EqualityType := ProdEqualityType E1 E2 <+ ProdHasEqDec E1 E2.
Module ProdBooleanEqualityType (E1 : BooleanEqualityType) (E2 : BooleanEqualityType) <: BooleanEqualityType := ProdEqualityType E1 E2 <+ ProdHasEqb E1 E2 E1 E2 <+ ProdEqbSpec E1 E2 E1 E2 E1 E2 E1 E2.
Module ProdBooleanDecidableType (E1 : BooleanDecidableType) (E2 : BooleanDecidableType) <: BooleanDecidableType := ProdBooleanEqualityType E1 E2 <+ ProdHasEqDec E1 E2.

Module ProdEq' (E1 : Eq) (E2 : Eq) := ProdEq E1 E2 <+ EqNotation.
Module ProdEqualityType' (E1 : EqualityType) (E2 : EqualityType) := ProdEqualityType E1 E2 <+ EqNotation.
Module ProdDecidableType' (E1 : DecidableType) (E2 : DecidableType) := ProdDecidableType E1 E2 <+ EqNotation.
Module ProdBooleanEqualityType' (E1 : BooleanEqualityType) (E2 : BooleanEqualityType) := ProdBooleanEqualityType E1 E2 <+ EqNotation <+ EqbNotation.
Module ProdBooleanDecidableType' (E1 : BooleanDecidableType) (E2 : BooleanDecidableType) := ProdBooleanDecidableType E1 E2 <+ EqNotation <+ EqbNotation.

Module ProdUsualEqualityType (E1 : UsualEqualityType) (E2 : UsualEqualityType) <: UsualEqualityType := ProdUsualEq E1 E2 <+ UsualIsEq.

Module ProdUsualDecidableType (E1 : UsualDecidableType) (E2 : UsualDecidableType) <: UsualDecidableType
:= ProdUsualEq E1 E2 <+ UsualIsEq <+ ProdUsualHasEqDec E1 E2.
Module ProdUsualDecidableTypeOrig (E1 : UsualDecidableType) (E2 : UsualDecidableType) <: UsualDecidableTypeOrig
:= ProdUsualEq E1 E2 <+ UsualIsEqOrig <+ ProdUsualHasEqDec E1 E2.
Module ProdUsualDecidableTypeBoth (E1 : UsualDecidableType) (E2 : UsualDecidableType) <: UsualDecidableTypeBoth
 := ProdUsualDecidableType E1 E2 <+ UsualIsEqOrig.
Module ProdUsualBoolEq (E1 : UsualBoolEq) (E2 : UsualBoolEq) <: UsualBoolEq
:= ProdUsualEq E1 E2 <+ ProdUsualHasEqBool E1 E2.
Module ProdUsualDecidableTypeFull (E1 : UsualDecidableTypeFull) (E2 : UsualDecidableTypeFull) <: UsualDecidableTypeFull
 := ProdUsualEq E1 E2 <+ UsualIsEq <+ UsualIsEqOrig <+ ProdUsualHasEqDec E1 E2 <+ ProdUsualHasEqBool E1 E2.
