
Require Import Pseudo Qhasm AlmostQhasm Medial Conversion Language.
Require Import PseudoMedialConversion AlmostConversion StringConversion.

Extraction Language Ocaml.
Require Import ExtrOcamlString ExtrOcamlBasic.
Require Import Coq.Strings.String.

Module Progs.
  Module Arch := PseudoUnary64.
  Module C64 := PseudoMedialConversion Arch.

  Import C64.P.

  Definition omap {A B} (f: A -> option B) (x: option A): option B :=
    match x with
    | Some v => f v
    | None => None
    end.

  Definition prog0: C64.P.Program.
    refine
      (PBin _ IPlus (PComb _ _ _
        (PVar 1 (exist _ 0 _))
        (PConst _ (natToWord _ 1)))); abstract intuition.
  Defined.

  Definition prog1: option C64.M.Program :=
    C64.PseudoConversion.convertProgram prog0.

  Definition prog2: option AlmostQhasm.Program :=
    omap C64.MedialConversion.convertProgram prog1.

  Definition prog3: option Qhasm.Program :=
    omap AlmostConversion.convertProgram prog2.

  Definition prog4: option string :=
    omap StringConversion.convertProgram prog3.

  Definition result: option string.
    let res := eval vm_compute in prog4 in exact res.
  Defined.

  Open Scope string_scope.
  Print result.
End Progs.

(* Extraction "Progs.ml" Progs. *)
