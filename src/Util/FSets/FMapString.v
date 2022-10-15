Require Import Coq.Strings.String.
Require Import Coq.FSets.FMapFullAVL.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Structures.OrderedTypeEx.
Require Export Crypto.Util.FixCoqMistakes.
(* TODO: use tries instead? *)

Module StringMap <: S := FMapFullAVL.Make String_as_OT.
