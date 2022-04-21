Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.ListUtil.

Local Set Implicit Arguments.

Module ListTyp (E : Typ) <: Typ.
  Definition t := list E.t.
End ListTyp.

Module ListHasEq (E : Eq).
  Search list relation.
  Definition eq : relation (list E.t) := eqlistA E.eq.
End ListHasEq.

Module ListIsEq (E : EqualityType).
  Local Notation eq := (eqlistA E.eq).
  Global Instance eq_equiv : Equivalence eq | 5.
  Proof.
    constructor; exact _.
  Defined.
End ListIsEq.

Module ListHasEqDec (E : Equalities.DecidableType).
  Local Notation eq := (eqlistA E.eq).
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    revert y; induction x as [|x xs IH], y as [|y ys]; try destruct (IH ys), (E.eq_dec x y).
    all: try solve [ constructor; repeat (constructor + assumption) ].
    all: try (right; abstract (inversion 1; subst; eauto)).
  Defined.
End ListHasEqDec.

Module ListHasEqb (E : Typ) (Eb : HasEqb E).
  Definition eqb := list_beq _ Eb.eqb.
End ListHasEqb.

Module ListEqbNotation (E : Typ) (Es : HasEqb E).
  Module Import _ListEqbNotation.
    Module T := ListTyp E.
    Module E := ListHasEqb E Es.
  End _ListEqbNotation.
  Include EqbNotation T _ListEqbNotation.E.
End ListEqbNotation.

Module ListEqbSpec (E : Typ) (Ee : HasEq E) (Eb : HasEqb E) (Es : EqbSpec E Ee Eb).
  Local Notation eq := (eqlistA Ee.eq).
  Local Notation eqb := (list_beq _ Eb.eqb).
  Lemma eqb_eq x y : eqb x y = true <-> eq x y.
  Proof.
    split; first [ apply eqlistA_lb | apply eqlistA_bl ].
    all: apply Es.eqb_eq.
  Qed.
End ListEqbSpec.

Module ListHasEqBool (E : Eq) (Es : HasEqBool E) := ListHasEqb E Es <+ ListEqbSpec E E Es Es.

Module ListUsualHasEqDec (E : UsualDecidableType).
  Definition eq_dec (x y : list E.t) : {eq x y} + {~eq x y}
    := List.list_eq_dec E.eq_dec x y.
End ListUsualHasEqDec.

Module ListUsualEqbSpec (E : UsualBoolEq).
  Lemma eqb_eq x y : @list_beq _ E.eqb x y = true <-> eq x y.
  Proof.
    split; first [ apply internal_list_dec_lb | apply internal_list_dec_bl ].
    all: apply E.eqb_eq.
  Qed.
End ListUsualEqbSpec.

Module ListHasUsualEq (E : UsualEq).
  Module E := ListTyp E.
  Include HasUsualEq E.
End ListHasUsualEq.

Module ListUsualEq (E : UsualEq) <: UsualEq := ListTyp E <+ HasUsualEq.

Module ListUsualIsEq (E : UsualEq).
  Module E := ListUsualEq E.
  Include UsualIsEq E.
End ListUsualIsEq.

Module ListUsualIsEqOrig (E : UsualEq).
  Module E := ListUsualEq E.
  Include UsualIsEqOrig E.
End ListUsualIsEqOrig.

Module ListMiniDecidableType (E : MiniDecidableType) <: MiniDecidableType.
  Include ListTyp E.
  Module E' := Make_UDT E.
  Include ListUsualHasEqDec E'.
End ListMiniDecidableType.

Module ListUsualHasEqBool (E : UsualBoolEq) := ListHasEqb E E <+ ListUsualEqbSpec E.

Module ListEq (E : Eq) <: Eq := ListTyp E <+ ListHasEq E.
Module ListEqualityType (E : EqualityType) <: EqualityType := ListEq E <+ ListIsEq E.
Module ListDecidableType (E : DecidableType) <: EqualityType := ListEqualityType E <+ ListHasEqDec E.
Module ListBooleanEqualityType (E : BooleanEqualityType) <: BooleanEqualityType := ListEqualityType E <+ ListHasEqb E E <+ ListEqbSpec E E E E.
Module ListBooleanDecidableType (E : BooleanDecidableType) <: BooleanDecidableType := ListBooleanEqualityType E <+ ListHasEqDec E.

Module ListEq' (E : Eq) := ListEq E <+ EqNotation.
Module ListEqualityType' (E : EqualityType) := ListEqualityType E <+ EqNotation.
Module ListDecidableType' (E : DecidableType) := ListDecidableType E <+ EqNotation.
Module ListBooleanEqualityType' (E : BooleanEqualityType) := ListBooleanEqualityType E <+ EqNotation <+ EqbNotation.
Module ListBooleanDecidableType' (E : BooleanDecidableType) := ListBooleanDecidableType E <+ EqNotation <+ EqbNotation.

Module ListUsualEqualityType (E : UsualEqualityType) <: UsualEqualityType := ListUsualEq E <+ UsualIsEq.

Module ListUsualDecidableType (E : UsualDecidableType) <: UsualDecidableType
:= ListUsualEq E <+ UsualIsEq <+ ListUsualHasEqDec E.
Module ListUsualDecidableTypeOrig (E : UsualDecidableType) <: UsualDecidableTypeOrig
:= ListUsualEq E <+ UsualIsEqOrig <+ ListUsualHasEqDec E.
Module ListUsualDecidableTypeBoth (E : UsualDecidableType) <: UsualDecidableTypeBoth
 := ListUsualDecidableType E <+ UsualIsEqOrig.
Module ListUsualBoolEq (E : UsualBoolEq) <: UsualBoolEq
:= ListUsualEq E <+ ListUsualHasEqBool E.
Module ListUsualDecidableTypeFull (E : UsualDecidableTypeFull) <: UsualDecidableTypeFull
 := ListUsualEq E <+ UsualIsEq <+ UsualIsEqOrig <+ ListUsualHasEqDec E <+ ListUsualHasEqBool E.
