From Coq Require Import FMapList.
From Coq Require Import OrderedType.
From Coq Require Import String.
Require Import Crypto.Util.Strings.String_as_OT_old.

Module StringMap := FMapList.Make String_as_OT.
