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

Module Type SectEqLt (E : EqLt) := EqLt <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectEqLe (E : EqLe) := EqLe <+ HasIso E <+ IsSect E <+ IsIsoLe E.
Module Type SectEqLtLe (E : EqLtLe) := EqLtLe <+ HasIso E <+ IsSect E <+ IsIsoLt E <+ IsIsoLe E.
Module Type SectEqLt' (E : EqLt) := EqLt' <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectEqLe' (E : EqLe) := EqLe' <+ HasIso E <+ IsSect E <+ IsIsoLe E.
Module Type SectEqLtLe' (E : EqLtLe) := EqLtLe' <+ HasIso E <+ IsSect E <+ IsIsoLt E <+ IsIsoLe E.
Module Type SectStrOrder (E : EqLt) := StrOrder <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectStrOrder' (E : EqLt) := StrOrder' <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectDecStrOrder (E : EqLt) := DecStrOrder <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectDecStrOrder' (E : EqLt) := DecStrOrder' <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectOrderedType (E : EqLt) := OrderedType <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectOrderedType' (E : EqLt) := OrderedType' <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectOrderedTypeFull (E : EqLt) := OrderedTypeFull <+ HasIso E <+ IsSect E <+ IsIsoLt E.
Module Type SectOrderedTypeFull' (E : EqLt) := OrderedTypeFull' <+ HasIso E <+ IsSect E <+ IsIsoLt E.

Module Type RetrEqLt (E : EqLt) := EqLt <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrEqLe (E : EqLe) := EqLe <+ HasIso E <+ IsRetr E <+ IsIsoLe E.
Module Type RetrEqLtLe (E : EqLtLe) := EqLtLe <+ HasIso E <+ IsRetr E <+ IsIsoLt E <+ IsIsoLe E.
Module Type RetrEqLt' (E : EqLt) := EqLt' <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrEqLe' (E : EqLe) := EqLe' <+ HasIso E <+ IsRetr E <+ IsIsoLe E.
Module Type RetrEqLtLe' (E : EqLtLe) := EqLtLe' <+ HasIso E <+ IsRetr E <+ IsIsoLt E <+ IsIsoLe E.
Module Type RetrStrOrder (E : EqLt) := StrOrder <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrStrOrder' (E : EqLt) := StrOrder' <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrDecStrOrder (E : EqLt) := DecStrOrder <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrDecStrOrder' (E : EqLt) := DecStrOrder' <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrOrderedType (E : EqLt) := OrderedType <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrOrderedType' (E : EqLt) := OrderedType' <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrOrderedTypeFull (E : EqLt) := OrderedTypeFull <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
Module Type RetrOrderedTypeFull' (E : EqLt) := OrderedTypeFull' <+ HasIso E <+ IsRetr E <+ IsIsoLt E.
