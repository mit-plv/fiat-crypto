
Require Import Pseudo Qhasm AlmostQhasm Conversion Language.
Require Import PseudoConversion AlmostConversion StringConversion.

Module P64 := Pseudo PseudoUnary64.
Module C64 := PseudoConversion PseudoUnary64.

Import P64.

Definition prog0: P64.Pseudo 1 1.
  refine (P64.PBin 1 P64.Wplus
      (P64.PVar 1 (exist _ 0 _))
      (P64.PConst 1 (natToWord _ 1)));
    abstract intuition.
Defined.

Definition prog1: option AlmostQhasm.Program.
  refine (C64.Conv.convertProgram (convert prog0 _)); admit.
Defined.

Definition prog2: option Qhasm.Program :=
  match prog1 with
  | Some p => AlmostConversion.convertProgram p
  | None => None
  end.

Definition prog3: option string :=
  match prog2 with
  | Some p => StringConversion.convertProgram p
  | None => None
  end.

Eval vm_compute in prog3.




