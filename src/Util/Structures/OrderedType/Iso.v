Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Import Crypto.Util.Structures.Orders.Iso.
Require Import Crypto.Util.Structures.Equalities.Iso.
Require Import Coq.Structures.OrderedType.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.FixCoqMistakes.

Local Set Implicit Arguments.
(** NB: This file is here only for compatibility with earlier version of
     [FSets] and [FMap]. Please use [Structures/Orders.v] directly now. *)
Module Type IsoMiniOrderedType (E : Orders.EqLt) := MiniOrderedType <+ HasIso E <+ IsIso E <+ IsIsoLt E.
Module Type IsoOrderedType (E : Orders.EqLt) := OrderedType.OrderedType <+ HasIso E <+ IsIso E <+ IsIsoLt E.
