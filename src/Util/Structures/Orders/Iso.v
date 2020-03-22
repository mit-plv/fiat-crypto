Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.FixCoqMistakes.

Local Set Implicit Arguments.

Module Type IsIsoLt (E : EqLt) (Import T:EqLt) (Import I : HasIso E T).
  Axiom Proper_to_lt : Proper (lt ==> E.lt) to_.
  Axiom Proper_of_lt : Proper (E.lt ==> lt) of_.
End IsIsoLt.

Module Type IsIsoLe (E : EqLe) (Import T:EqLe) (Import I : HasIso E T).
  Axiom Proper_to_le : Proper (le ==> E.le) to_.
  Axiom Proper_of_le : Proper (E.le ==> le) of_.
End IsIsoLe.

Module Type IsoEqLt (E : EqLt) := EqLt <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoEqLe (E : EqLe) := EqLe <+ HasIso E <+ IsIso E <+ IsIsoLe E.
Module Type IsoEqLtLe (E : EqLtLe) := EqLtLe <+ HasIso E <+ IsIso E <+ IsIsoLt E <+ IsIsoLe E.
Module Type IsoEqLt' (E : EqLt) := EqLt' <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoEqLe' (E : EqLe) := EqLe' <+ HasIso E <+ IsIso E <+ IsIsoLe E.
Module Type IsoEqLtLe' (E : EqLtLe) := EqLtLe' <+ HasIso E <+ IsIso E <+ IsIsoLt E <+ IsIsoLe E.
Module Type IsoStrOrder (E : EqLt) := StrOrder <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoStrOrder' (E : EqLt) := StrOrder' <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoDecStrOrder (E : EqLt) := DecStrOrder <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoDecStrOrder' (E : EqLt) := DecStrOrder' <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoOrderedType (E : EqLt) := OrderedType <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoOrderedType' (E : EqLt) := OrderedType' <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoOrderedTypeFull (E : EqLt) := OrderedTypeFull <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoOrderedTypeFull' (E : EqLt) := OrderedTypeFull' <+ HasIso E <+ IsIso E <+ IsIsoLt E.
