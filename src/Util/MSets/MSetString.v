From Coq Require Import String.
From Coq Require Import MSetAVL.
From Coq Require Import MSetFacts.
From Coq Require Import MSetInterface.
From Coq Require Import OrdersEx.
Require Export Crypto.Util.FixCoqMistakes.
(* TODO: use tries instead? *)

Module StringSet <: S := MSetAVL.Make String_as_OT.
Module StringSetFacts := Facts StringSet.
