From Coq Require Import BinIntDef.
From Coq Require Import BinNatDef.
From Coq Require Import BinPosDef.
From Coq Require Export Zmod.

Global Coercion BinInt.Z.pos : BinPos.positive >-> BinInt.Z.
Global Coercion BinInt.Z.of_N : BinNums.N >-> BinInt.Z.
Global Coercion Zmod.unsigned : Zmod.Zmod >-> BinInt.Z.
Global Set Printing Coercions.

Infix "/" := Zmod.mdiv : Zmod_scope.

Module Zmod.
  Definition of_nat m (n:nat) := Zmod.of_Z m (BinInt.Z.of_nat n).
  Definition to_nat {m} (x:Zmod m) := BinInt.Z.to_nat (Zmod.unsigned x).

  Definition of_N m n := Zmod.of_Z m (BinInt.Z.of_N n).
  Definition to_N {m} (x:Zmod m) := BinInt.Z.to_N (Zmod.unsigned x).
End Zmod.
