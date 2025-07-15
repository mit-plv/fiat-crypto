From Coq Require Import String.
From Coq Require Import FMapFullAVL.
From Coq Require Import FMapInterface.
From Coq Require Import OrderedTypeEx.
Require Export Crypto.Util.FixCoqMistakes.
(* TODO: use tries instead? *)

Module StringMap <: S := FMapFullAVL.Make String_as_OT.
