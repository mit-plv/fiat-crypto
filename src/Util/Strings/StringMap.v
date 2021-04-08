Require Import Coq.FSets.FMapList.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Strings.String.
Require Import Crypto.Util.Strings.String_as_OT_old.

Module StringMap := FMapList.Make String_as_OT.
