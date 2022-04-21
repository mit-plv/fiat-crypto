Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.FixCoqMistakes.

Local Set Implicit Arguments.

Module Type HasIso (E : Typ) (Import T:Typ).
  Parameter to_ : t -> E.t.
  Parameter of_ : E.t -> t.
End HasIso.

Module Type IsProperIso (E : Eq) (Import T:Eq) (Import I : HasIso E T).
  Axiom Proper_to_ : Proper (eq ==> E.eq) to_.
  Axiom Proper_of_ : Proper (E.eq ==> eq) of_.
  Global Existing Instance Proper_to_ | 5.
  Global Existing Instance Proper_of_ | 5.
End IsProperIso.

Module Type IsoIsSect (E : Eq) (Import T:Eq) (Import I : HasIso E T).
  Axiom of_to : forall x, eq (of_ (to_ x)) x.
End IsoIsSect.

Module Type IsoIsRetr (E : Eq) (Import T:Eq) (Import I : HasIso E T).
  Axiom to_of : forall x, E.eq (to_ (of_ x)) x.
End IsoIsRetr.

Module Type IsSect (E : Eq) (T:Eq) (I : HasIso E T) := IsProperIso E T I <+ IsoIsSect E T I.
Module Type IsRetr (E : Eq) (T:Eq) (I : HasIso E T) := IsProperIso E T I <+ IsoIsRetr E T I.
Module Type IsIso (E : Eq) (T:Eq) (I : HasIso E T) := IsProperIso E T I <+ IsoIsSect E T I <+ IsoIsRetr E T I.

Module Type Iso (E : Eq) := Typ <+ HasIso E.
Module Type IsoEq (E : Eq) := Eq <+ HasIso E.
Module Type IsoEqualityType (E : Eq) := EqualityType <+ HasIso E <+ IsIso E.
Module Type IsoEqualityTypeOrig (E : Eq) := EqualityTypeOrig <+ HasIso E <+ IsIso E.
Module Type IsoEqualityTypeBoth (E : Eq) := EqualityTypeBoth <+ HasIso E <+ IsIso E.
Module Type IsoDecidableType (E : Eq) := DecidableType <+ HasIso E <+ IsIso E.
Module Type IsoDecidableTypeOrig (E : Eq) := DecidableTypeOrig <+ HasIso E <+ IsIso E.
Module Type IsoDecidableTypeBoth (E : Eq) := DecidableTypeBoth <+ HasIso E <+ IsIso E.
Module Type IsoBooleanEqualityType (E : Eq) := BooleanEqualityType <+ HasIso E <+ IsIso E.
Module Type IsoBooleanDecidableType (E : Eq) := BooleanDecidableType <+ HasIso E <+ IsIso E.
Module Type IsoDecidableTypeFull (E : Eq) := DecidableTypeFull <+ HasIso E <+ IsIso E.
Module Type IsoEqualityType' (E : Eq) := EqualityType' <+ HasIso E <+ IsIso E.
Module Type IsoEqualityTypeOrig' (E : Eq) := EqualityTypeOrig' <+ HasIso E <+ IsIso E.
Module Type IsoEqualityTypeBoth' (E : Eq) := EqualityTypeBoth' <+ HasIso E <+ IsIso E.
Module Type IsoDecidableType' (E : Eq) := DecidableType' <+ HasIso E <+ IsIso E.
Module Type IsoDecidableTypeOrig' (E : Eq) := DecidableTypeOrig' <+ HasIso E <+ IsIso E.
Module Type IsoDecidableTypeBoth' (E : Eq) := DecidableTypeBoth' <+ HasIso E <+ IsIso E.
Module Type IsoBooleanEqualityType' (E : Eq) := BooleanEqualityType' <+ HasIso E <+ IsIso E.
Module Type IsoBooleanDecidableType' (E : Eq) := BooleanDecidableType' <+ HasIso E <+ IsIso E.
Module Type IsoDecidableTypeFull' (E : Eq) := DecidableTypeFull' <+ HasIso E <+ IsIso E.

Module LiftIsoHasEq (E : Eq) (Import I : Iso E) <: HasEq I.
  Definition eq : relation t := fun x y => E.eq (to_ x) (to_ y).
End LiftIsoHasEq.

Module LiftIsoEq (E : Eq) (I : Iso E) <: IsoEq E := I <+ LiftIsoHasEq E I.

Module LiftIsoIsEq (E : EqualityType) (Import I : Iso E).
  Module Import I' := LiftIsoEq E I.
  Instance eq_equiv : Equivalence eq | 5.
  Proof.
    cbv [eq]; split; repeat intro.
    { reflexivity. }
    { symmetry; assumption. }
    { etransitivity; eassumption. }
  Defined.
End LiftIsoIsEq.

Module LiftIsoHasEqDec (E : DecidableType) (Import I : IsoEqualityType E) <: HasEqDec I.
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    destruct (E.eq_dec (to_ x) (to_ y)) as [H|H]; [ left | right ];
      [ | abstract (intro H'; apply H; clear H; f_equiv; assumption) ].
    etransitivity; [ symmetry; apply of_to | ];
      etransitivity; [ | apply of_to ];
        f_equiv; assumption.
  Defined.
End LiftIsoHasEqDec.

Module Type Sect (E : Eq) := Typ <+ HasIso E.
Module Type SectEq (E : Eq) := Eq <+ HasIso E.
Module Type SectEqualityType (E : Eq) := EqualityType <+ HasIso E <+ IsSect E.
Module Type SectEqualityTypeOrig (E : Eq) := EqualityTypeOrig <+ HasIso E <+ IsSect E.
Module Type SectEqualityTypeBoth (E : Eq) := EqualityTypeBoth <+ HasIso E <+ IsSect E.
Module Type SectDecidableType (E : Eq) := DecidableType <+ HasIso E <+ IsSect E.
Module Type SectDecidableTypeOrig (E : Eq) := DecidableTypeOrig <+ HasIso E <+ IsSect E.
Module Type SectDecidableTypeBoth (E : Eq) := DecidableTypeBoth <+ HasIso E <+ IsSect E.
Module Type SectBooleanEqualityType (E : Eq) := BooleanEqualityType <+ HasIso E <+ IsSect E.
Module Type SectBooleanDecidableType (E : Eq) := BooleanDecidableType <+ HasIso E <+ IsSect E.
Module Type SectDecidableTypeFull (E : Eq) := DecidableTypeFull <+ HasIso E <+ IsSect E.
Module Type SectEqualityType' (E : Eq) := EqualityType' <+ HasIso E <+ IsSect E.
Module Type SectEqualityTypeOrig' (E : Eq) := EqualityTypeOrig' <+ HasIso E <+ IsSect E.
Module Type SectEqualityTypeBoth' (E : Eq) := EqualityTypeBoth' <+ HasIso E <+ IsSect E.
Module Type SectDecidableType' (E : Eq) := DecidableType' <+ HasIso E <+ IsSect E.
Module Type SectDecidableTypeOrig' (E : Eq) := DecidableTypeOrig' <+ HasIso E <+ IsSect E.
Module Type SectDecidableTypeBoth' (E : Eq) := DecidableTypeBoth' <+ HasIso E <+ IsSect E.
Module Type SectBooleanEqualityType' (E : Eq) := BooleanEqualityType' <+ HasIso E <+ IsSect E.
Module Type SectBooleanDecidableType' (E : Eq) := BooleanDecidableType' <+ HasIso E <+ IsSect E.
Module Type SectDecidableTypeFull' (E : Eq) := DecidableTypeFull' <+ HasIso E <+ IsSect E.

Module LiftSectHasEq (E : Eq) (I : Sect E) <: HasEq I := LiftIsoHasEq E I.
Module LiftSectEq (E : Eq) (I : Sect E) <: SectEq E := I <+ LiftSectHasEq E I.
Module LiftSectIsEq (E : EqualityType) (I : Sect E) := LiftIsoIsEq E I.
Module LiftSectHasEqDec (E : DecidableType) (Import I : SectEqualityType E) <: HasEqDec I.
  Definition eq_dec x y : {eq x y} + {~eq x y}.
  Proof.
    destruct (E.eq_dec (to_ x) (to_ y)) as [H|H]; [ left | right ];
      [ | abstract (intro H'; apply H; clear H; f_equiv; assumption) ].
    etransitivity; [ symmetry; apply of_to | ];
      etransitivity; [ | apply of_to ];
        f_equiv; assumption.
  Defined.
End LiftSectHasEqDec.

Module Type Retr (E : Eq) := Typ <+ HasIso E.
Module Type RetrEq (E : Eq) := Eq <+ HasIso E.
Module Type RetrEqualityType (E : Eq) := EqualityType <+ HasIso E <+ IsRetr E.
Module Type RetrEqualityTypeOrig (E : Eq) := EqualityTypeOrig <+ HasIso E <+ IsRetr E.
Module Type RetrEqualityTypeBoth (E : Eq) := EqualityTypeBoth <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableType (E : Eq) := DecidableType <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableTypeOrig (E : Eq) := DecidableTypeOrig <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableTypeBoth (E : Eq) := DecidableTypeBoth <+ HasIso E <+ IsRetr E.
Module Type RetrBooleanEqualityType (E : Eq) := BooleanEqualityType <+ HasIso E <+ IsRetr E.
Module Type RetrBooleanDecidableType (E : Eq) := BooleanDecidableType <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableTypeFull (E : Eq) := DecidableTypeFull <+ HasIso E <+ IsRetr E.
Module Type RetrEqualityType' (E : Eq) := EqualityType' <+ HasIso E <+ IsRetr E.
Module Type RetrEqualityTypeOrig' (E : Eq) := EqualityTypeOrig' <+ HasIso E <+ IsRetr E.
Module Type RetrEqualityTypeBoth' (E : Eq) := EqualityTypeBoth' <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableType' (E : Eq) := DecidableType' <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableTypeOrig' (E : Eq) := DecidableTypeOrig' <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableTypeBoth' (E : Eq) := DecidableTypeBoth' <+ HasIso E <+ IsRetr E.
Module Type RetrBooleanEqualityType' (E : Eq) := BooleanEqualityType' <+ HasIso E <+ IsRetr E.
Module Type RetrBooleanDecidableType' (E : Eq) := BooleanDecidableType' <+ HasIso E <+ IsRetr E.
Module Type RetrDecidableTypeFull' (E : Eq) := DecidableTypeFull' <+ HasIso E <+ IsRetr E.

Module LiftRetrHasEq (E : Eq) (I : Retr E) <: HasEq I := LiftIsoHasEq E I.
Module LiftRetrEq (E : Eq) (I : Retr E) <: RetrEq E := I <+ LiftRetrHasEq E I.
Module LiftRetrIsEq (E : EqualityType) (I : Retr E) := LiftIsoIsEq E I.
