Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Structures.Equalities.

Local Set Implicit Arguments.

Module OptionTyp (E : Typ) <: Typ.
  Definition t := option E.t.
End OptionTyp.

Module OptionHasEq (E : Eq).
  Definition eq : relation (option E.t) := option_eq E.eq.
End OptionHasEq.

Module OptionIsEq (E : EqualityType).
  Local Notation eq := (option_eq E.eq).
  Global Instance eq_equiv : Equivalence eq | 5.
  Proof.
    constructor; exact _.
  Defined.
End OptionIsEq.

Module OptionIsEqOrig (E : EqualityTypeOrig).
  Local Notation eq := (option_eq E.eq).
  Definition eq_refl : Reflexive eq.
  Proof. repeat intro; destruct_head' option; (reflexivity + apply E.eq_refl). Defined.
  Definition eq_sym : Symmetric eq.
  Proof. repeat intro; destruct_head' option; cbv [eq] in *; (assumption + apply E.eq_sym + idtac + exfalso + inversion_option); assumption. Defined.
  Definition eq_trans : Transitive eq.
  Proof. repeat intro; destruct_head' option; cbv [eq] in *; try ((assumption + eapply E.eq_trans + idtac + exfalso + inversion_option); eassumption). Defined.
End OptionIsEqOrig.

Module OptionHasEqDec (E : Eq) (EDec : HasEqDec E).
  Local Notation eq := (option_eq E.eq).
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    destruct x as [x|], y as [y|]; [ destruct (EDec.eq_dec x y); [ left | right ] | right | right | left ];
      cbv [option_eq]; try assumption; try reflexivity; try solve [ intros [] ]; congruence.
  Defined.
End OptionHasEqDec.

Module OptionHasEqb (E : Typ) (Eb : HasEqb E).
  Definition eqb := option_beq Eb.eqb.
End OptionHasEqb.

Module OptionEqbNotation (E : Typ) (Es : HasEqb E).
  Module Import _OptionEqbNotation.
    Module T := OptionTyp E.
    Module E := OptionHasEqb E Es.
  End _OptionEqbNotation.
  Include EqbNotation T _OptionEqbNotation.E.
End OptionEqbNotation.

Module OptionEqbSpec (E : Typ) (Ee : HasEq E) (Eb : HasEqb E) (Es : EqbSpec E Ee Eb).
  Local Notation eq := (option_eq Ee.eq).
  Local Notation eqb := (option_beq Eb.eqb).
  Lemma eqb_eq x y : eqb x y = true <-> eq x y.
  Proof.
    destruct x as [x|], y as [y|]; cbv [option_eq option_beq];
      try apply Es.eqb_eq;
      intuition congruence.
  Qed.
End OptionEqbSpec.

Module OptionHasEqBool (E : Eq) (Es : HasEqBool E) := OptionHasEqb E Es <+ OptionEqbSpec E E Es Es.

Module OptionUsualHasEqDec (E : UsualEq) (EDec : HasEqDec E).
  Definition eq_dec (x y : option E.t) : {eq x y} + {~eq x y}.
  Proof.
    destruct x as [x|], y as [y|];
      [ destruct (EDec.eq_dec x y); [ left | right ]
      | right
      | right
      | left ];
      repeat first [ assumption
                   | reflexivity
                   | apply f_equal
                   | intro
                   | progress inversion_option
                   | solve [ auto with nocore ] ].
  Defined.
End OptionUsualHasEqDec.

Module OptionUsualEqbSpec (E : UsualBoolEq).
  Lemma eqb_eq x y : @option_beq _ E.eqb x y = true <-> eq x y.
  Proof.
    destruct x as [x|], y as [y|]; cbn;
      rewrite ?E.eqb_eq;
      intuition congruence.
  Qed.
End OptionUsualEqbSpec.

Module OptionHasUsualEq (E : UsualEq).
  Module Import _OptionHasUsualEq.
    Module E' := OptionTyp E.
  End _OptionHasUsualEq.
  Include HasUsualEq E'.
End OptionHasUsualEq.

Module OptionUsualEq (E : UsualEq) <: UsualEq := OptionTyp E <+ HasUsualEq.

Module OptionUsualIsEq (E : UsualEq).
  Module Import _OptionUsualIsEq.
    Module E' := OptionUsualEq E.
  End _OptionUsualIsEq.
  Include UsualIsEq E'.
End OptionUsualIsEq.

Module OptionUsualIsEqOrig (E : UsualEq).
  Module Import _OptionUsualIsEqOrig.
    Module E' := OptionUsualEq E.
  End _OptionUsualIsEqOrig.
  Include UsualIsEqOrig E'.
End OptionUsualIsEqOrig.

Module OptionMiniDecidableType (E : MiniDecidableType) <: MiniDecidableType.
  Include OptionTyp E.
  Module Import _OptionMiniDecidableType.
    Module E' := Make_UDT E.
  End _OptionMiniDecidableType.
  Include OptionUsualHasEqDec E' E'.
End OptionMiniDecidableType.

Local Coercion is_true : bool >-> Sortclass.
Module OptionIsEqb (E : EqbType).
  Global Instance eqb_equiv : Equivalence (option_beq E.eqb) | 5.
  Proof.
    destruct E.eqb_equiv.
    split; repeat intros [|]; cbv in *; try congruence; eauto.
  Qed.
End OptionIsEqb.

Module OptionUsualHasEqBool (E : UsualBoolEq) := OptionHasEqb E E <+ OptionUsualEqbSpec E.

Module OptionEq (E : Eq) <: Eq := OptionTyp E <+ OptionHasEq E.
Module OptionEqualityType (E : EqualityType) <: EqualityType := OptionEq E <+ OptionIsEq E.
Module OptionEqualityTypeOrig (E : EqualityTypeOrig) <: EqualityTypeOrig := OptionEq E <+ OptionIsEqOrig E.
Module OptionEqualityTypeBoth (E : EqualityTypeBoth) <: EqualityTypeBoth := OptionEq E <+ OptionIsEq E <+ OptionIsEqOrig E.
Module OptionDecidableType (E : DecidableType) <: EqualityType := OptionEqualityType E <+ OptionHasEqDec E E.
Module OptionDecidableTypeOrig (E : DecidableTypeOrig) <: EqualityTypeOrig := OptionEqualityTypeOrig E <+ OptionHasEqDec E E.
Module OptionDecidableTypeBoth (E : DecidableTypeBoth) <: EqualityTypeBoth := OptionEqualityTypeBoth E <+ OptionHasEqDec E E.
Module OptionBooleanEqualityType (E : BooleanEqualityType) <: BooleanEqualityType := OptionEqualityType E <+ OptionHasEqb E E <+ OptionEqbSpec E E E E.
Module OptionBooleanDecidableType (E : BooleanDecidableType) <: BooleanDecidableType := OptionBooleanEqualityType E <+ OptionHasEqDec E E.
Module OptionDecidableTypeFull (E : DecidableTypeFull) <: DecidableTypeFull := OptionEq E <+ OptionIsEq E <+ OptionIsEqOrig E <+ OptionHasEqDec E E <+ OptionHasEqBool E E.

Module OptionEq' (E : Eq) := OptionEq E <+ EqNotation.
Module OptionEqualityType' (E : EqualityType) := OptionEqualityType E <+ EqNotation.
Module OptionEqualityTypeOrig' (E : EqualityTypeOrig) := OptionEqualityTypeOrig E <+ EqNotation.
Module OptionEqualityTypeBoth' (E : EqualityTypeBoth) := OptionEqualityTypeBoth E <+ EqNotation.
Module OptionDecidableType' (E : DecidableType) := OptionDecidableType E <+ EqNotation.
Module OptionDecidableTypeOrig' (E : DecidableTypeOrig) := OptionDecidableTypeOrig E <+ EqNotation.
Module OptionDecidableTypeBoth' (E : DecidableTypeBoth) := OptionDecidableTypeBoth E <+ EqNotation.
Module OptionBooleanEqualityType' (E : BooleanEqualityType) := OptionBooleanEqualityType E <+ EqNotation <+ EqbNotation.
Module OptionBooleanDecidableType' (E : BooleanDecidableType) := OptionBooleanDecidableType E <+ EqNotation <+ EqbNotation.
Module OptionDecidableTypeFull' (E : DecidableTypeFull) := OptionDecidableTypeFull E <+ EqNotation.

Module OptionUsualEqualityType (E : UsualEqualityType) <: UsualEqualityType := OptionUsualEq E <+ UsualIsEq.
Module OptionUsualEqualityTypeOrig (E : UsualEqualityTypeOrig) <: UsualEqualityTypeOrig := OptionUsualEq E <+ UsualIsEqOrig.
Module OptionUsualEqualityTypeBoth (E : UsualEqualityTypeBoth) <: UsualEqualityTypeBoth := OptionUsualEq E <+ UsualIsEq <+ UsualIsEqOrig.

Module OptionUsualDecidableType (E : UsualDecidableType) <: UsualDecidableType
:= OptionUsualEq E <+ UsualIsEq <+ OptionUsualHasEqDec E E.
Module OptionUsualDecidableTypeOrig (E : UsualDecidableTypeOrig) <: UsualDecidableTypeOrig
:= OptionUsualEq E <+ UsualIsEqOrig <+ OptionUsualHasEqDec E E.
Module OptionUsualDecidableTypeBoth (E : UsualDecidableTypeBoth) <: UsualDecidableTypeBoth
 := OptionUsualDecidableType E <+ UsualIsEqOrig.
Module OptionUsualBoolEq (E : UsualBoolEq) <: UsualBoolEq
:= OptionUsualEq E <+ OptionUsualHasEqBool E.
Module OptionUsualDecidableTypeFull (E : UsualDecidableTypeFull) <: UsualDecidableTypeFull
 := OptionUsualEq E <+ UsualIsEq <+ UsualIsEqOrig <+ OptionUsualHasEqDec E E <+ OptionUsualHasEqBool E.

Module OptionEqbType (E : EqbType) <: EqbType := OptionTyp E <+ OptionHasEqb E E <+ OptionIsEqb E.
