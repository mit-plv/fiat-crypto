Require Import Coq.Strings.String.
Require Import Coq.MSets.MSetAVL.
Require Import Coq.MSets.MSetFacts.
Require Import Coq.MSets.MSetInterface.
Require Import Coq.Structures.OrdersEx.
Require Export Crypto.Util.FixCoqMistakes.
(* TODO: use tries instead? *)

Module StringSet <: S := MSetAVL.Make String_as_OT.
Module StringSetFacts := Facts StringSet.
