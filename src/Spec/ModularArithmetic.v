From Coq Require Import BinIntDef.
From Coq Require Import BinNatDef.
From Coq Require Import BinPosDef.
From Coq Require Import Zmod.

Global Coercion BinInt.Z.pos : BinPos.positive >-> BinInt.Z.
Global Coercion BinInt.Z.of_N : BinNums.N >-> BinInt.Z.
Global Coercion Zmod.unsigned : Zmod.Zmod >-> BinInt.Z.
Global Set Printing Coercions.

Notation F := Zmod.Zmod (only parsing).
Module F.
  Notation of_Z := Zmod.of_Z (only parsing).
  Notation to_Z := Zmod.unsigned (only parsing).
  Notation zero := Zmod.zero (only parsing).
  Notation one := Zmod.one (only parsing).
  Notation add := Zmod.add (only parsing).
  Notation sub := Zmod.sub (only parsing).
  Notation mul := Zmod.mul (only parsing).
  Notation opp := Zmod.opp (only parsing).
  Notation inv := Zmod.inv (only parsing).
  Notation div := Zmod.mdiv (only parsing).
  Notation pow := Zmod.pow (only parsing).

  Definition of_nat m (n:nat) := F.of_Z m (BinInt.Z.of_nat n).
  Definition to_nat {m} (x:F m) := BinInt.Z.to_nat (F.to_Z x).
  Notation nat_mod := of_nat (only parsing).

  Definition of_N m n := F.of_Z m (BinInt.Z.of_N n).
  Definition to_N {m} (x:F m) := BinInt.Z.to_N (F.to_Z x).
  Notation N_mod := of_N (only parsing).

  Notation Z_mod := of_Z (only parsing).
End F.

Declare Scope F_scope.
Delimit Scope F_scope with F.
Bind Scope F_scope with Zmod.Zmod.
Infix "+" := F.add : F_scope.
Infix "*" := F.mul : F_scope.
Infix "-" := F.sub : F_scope.
Infix "/" := F.div : F_scope.
Infix "^" := F.pow : F_scope.
Notation "0" := F.zero : F_scope.
Notation "1" := F.one : F_scope.
