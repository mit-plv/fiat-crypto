Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.ListUtil.

Local Set Implicit Arguments.

Module ListTyp (E : Typ) <: Typ.
  Definition t := list E.t.
End ListTyp.

Module ListHasEq (E : Eq).
  Definition eq : relation (list E.t) := eqlistA E.eq.
End ListHasEq.

Module ListIsEq (E : EqualityType).
  Local Notation eq := (eqlistA E.eq).
  Global Instance eq_equiv : Equivalence eq | 5.
  Proof.
    constructor; exact _.
  Defined.
End ListIsEq.

Module ListIsEqOrig (E : EqualityTypeOrig).
  Local Notation eq := (eqlistA E.eq).
  Lemma eq_refl : Reflexive eq.
  Proof. apply eqlistA_equiv; split; first [ exact E.eq_refl | exact E.eq_sym | exact E.eq_trans ]. Qed.
  Lemma eq_sym : Symmetric eq.
  Proof. apply eqlistA_equiv; split; first [ exact E.eq_refl | exact E.eq_sym | exact E.eq_trans ]. Qed.
  Lemma eq_trans : Transitive eq.
  Proof. apply eqlistA_equiv; split; first [ exact E.eq_refl | exact E.eq_sym | exact E.eq_trans ]. Qed.
End ListIsEqOrig.

Module ListHasEqDec (E : Eq) (EDec : HasEqDec E).
  Local Notation eq := (eqlistA E.eq).
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    revert y; induction x as [|x xs IH], y as [|y ys]; try destruct (IH ys), (EDec.eq_dec x y).
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

Module ListUsualHasEqDec (E : UsualEq) (EDec : HasEqDec E).
  Definition eq_dec (x y : list E.t) : {eq x y} + {~eq x y}
    := List.list_eq_dec EDec.eq_dec x y.
End ListUsualHasEqDec.

Module ListUsualEqbSpec (E : UsualBoolEq).
  Lemma eqb_eq x y : @list_beq _ E.eqb x y = true <-> eq x y.
  Proof.
    split; first [ apply internal_list_dec_lb | apply internal_list_dec_bl ].
    all: apply E.eqb_eq.
  Qed.
End ListUsualEqbSpec.

Module ListHasUsualEq (E : UsualEq).
  Module Import _ListHasUsualEq.
    Module E' := ListTyp E.
  End _ListHasUsualEq.
  Include HasUsualEq E'.
End ListHasUsualEq.

Module ListUsualEq (E : UsualEq) <: UsualEq := ListTyp E <+ HasUsualEq.

Module ListUsualIsEq (E : UsualEq).
  Module Import _ListUsualIsEq.
    Module E' := ListUsualEq E.
  End _ListUsualIsEq.
  Include UsualIsEq E'.
End ListUsualIsEq.

Module ListUsualIsEqOrig (E : UsualEq).
  Module Import _ListUsualIsEqOrig.
    Module E' := ListUsualEq E.
  End _ListUsualIsEqOrig.
  Include UsualIsEqOrig E'.
End ListUsualIsEqOrig.

Module ListMiniDecidableType (E : MiniDecidableType) <: MiniDecidableType.
  Include ListTyp E.
  Module Import _ListMiniDecidableType.
    Module E' := Make_UDT E.
  End _ListMiniDecidableType.
  Include ListUsualHasEqDec E' E'.
End ListMiniDecidableType.

Module ListUsualHasEqBool (E : UsualBoolEq) := ListHasEqb E E <+ ListUsualEqbSpec E.

Module ListEq (E : Eq) <: Eq := ListTyp E <+ ListHasEq E.
Module ListEqualityType (E : EqualityType) <: EqualityType := ListEq E <+ ListIsEq E.
Module ListEqualityTypeOrig (E : EqualityTypeOrig) <: EqualityTypeOrig := ListEq E <+ ListIsEqOrig E.
Module ListEqualityTypeBoth (E : EqualityTypeBoth) <: EqualityTypeBoth := ListEq E <+ ListIsEq E <+ ListIsEqOrig E.
Module ListDecidableType (E : DecidableType) <: EqualityType := ListEqualityType E <+ ListHasEqDec E E.
Module ListDecidableTypeOrig (E : DecidableTypeOrig) <: DecidableTypeOrig := ListEqualityTypeOrig E <+ ListHasEqDec E E.
Module ListDecidableTypeBoth (E : DecidableTypeBoth) <: DecidableTypeBoth := ListEqualityTypeBoth E <+ ListHasEqDec E E.
Module ListBooleanEqualityType (E : BooleanEqualityType) <: BooleanEqualityType := ListEqualityType E <+ ListHasEqb E E <+ ListEqbSpec E E E E.
Module ListBooleanDecidableType (E : BooleanDecidableType) <: BooleanDecidableType := ListBooleanEqualityType E <+ ListHasEqDec E E.
Module ListDecidableTypeFull (E : DecidableTypeFull) <: DecidableTypeFull := ListEq E <+ ListIsEq E <+ ListIsEqOrig E <+ ListHasEqDec E E <+ ListHasEqBool E E.

Module ListEq' (E : Eq) := ListEq E <+ EqNotation.
Module ListEqualityType' (E : EqualityType) := ListEqualityType E <+ EqNotation.
Module ListEqualityTypeOrig' (E : EqualityTypeOrig) := ListEqualityTypeOrig E <+ EqNotation.
Module ListEqualityTypeBoth' (E : EqualityTypeBoth) := ListEqualityTypeBoth E <+ EqNotation.
Module ListDecidableType' (E : DecidableType) := ListDecidableType E <+ EqNotation.
Module ListDecidableTypeOrig' (E : DecidableTypeOrig) := ListDecidableTypeOrig E <+ EqNotation.
Module ListDecidableTypeBoth' (E : DecidableTypeBoth) := ListDecidableTypeBoth E <+ EqNotation.
Module ListBooleanEqualityType' (E : BooleanEqualityType) := ListBooleanEqualityType E <+ EqNotation <+ EqbNotation.
Module ListBooleanDecidableType' (E : BooleanDecidableType) := ListBooleanDecidableType E <+ EqNotation <+ EqbNotation.
Module ListDecidableTypeFull' (E : DecidableTypeFull) := ListDecidableTypeFull E <+ EqNotation.

Module ListUsualEqualityType (E : UsualEqualityType) <: UsualEqualityType := ListUsualEq E <+ UsualIsEq.
Module ListUsualEqualityTypeOrig (E : UsualEqualityTypeOrig) <: UsualEqualityTypeOrig := ListUsualEq E <+ UsualIsEqOrig.
Module ListUsualEqualityTypeBoth (E : UsualEqualityTypeBoth) <: UsualEqualityTypeBoth := ListUsualEq E <+ UsualIsEq <+ UsualIsEqOrig.

Module ListUsualDecidableType (E : UsualDecidableType) <: UsualDecidableType
:= ListUsualEq E <+ UsualIsEq <+ ListUsualHasEqDec E E.
Module ListUsualDecidableTypeOrig (E : UsualDecidableTypeOrig) <: UsualDecidableTypeOrig
:= ListUsualEq E <+ UsualIsEqOrig <+ ListUsualHasEqDec E E.
Module ListUsualDecidableTypeBoth (E : UsualDecidableTypeBoth) <: UsualDecidableTypeBoth
 := ListUsualDecidableType E <+ UsualIsEqOrig.
Module ListUsualBoolEq (E : UsualBoolEq) <: UsualBoolEq
:= ListUsualEq E <+ ListUsualHasEqBool E.
Module ListUsualDecidableTypeFull (E : UsualDecidableTypeFull) <: UsualDecidableTypeFull
 := ListUsualEq E <+ UsualIsEq <+ UsualIsEqOrig <+ ListUsualHasEqDec E E <+ ListUsualHasEqBool E.

Local Coercion is_true : bool >-> Sortclass.
Module ListIsEqb (E : EqbType).
  Global Instance eqb_equiv : Equivalence (list_beq _ E.eqb) | 5.
  Proof.
    split; hnf;
      [ induction x as [|x xs IH];
        try pose proof ((_ : Reflexive E.eqb) x)
      | induction x as [|x xs IH], y as [|y ys];
        try (specialize (IH ys); pose proof ((_ : Symmetric E.eqb) x y))
      | induction x as [|x xs IH], y as [|y ys], z as [|z zs];
        try (specialize (IH ys zs); pose proof ((_ : Transitive E.eqb) x y z)) ];
      cbn in *; cbv [is_true] in *;
      rewrite ?Bool.andb_true_iff; intuition (congruence + eauto).
  Qed.
End ListIsEqb.

Module ListEqbType (E : EqbType) <: EqbType := ListTyp E <+ ListHasEqb E E <+ ListIsEqb E.
