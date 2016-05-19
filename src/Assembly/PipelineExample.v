
Require Import Pseudo Qhasm AlmostQhasm Medial Conversion Language.
Require Import PseudoMedialConversion AlmostConversion StringConversion.

Extraction Language Ocaml.
Require Import ExtrOcamlString ExtrOcamlBasic.
Require Import Coq.Strings.String.

Module Progs.
  Module Arch := PseudoUnary64.
  Module C64 := PseudoMedialConversion Arch.

  Import C64.P.

  Definition prog0: C64.P.Program.
    refine
      (PBin _ IPlus (PComb _ _ _
        (PVar 1 (exist _ 0 _))
        (PConst _ (natToWord _ 1)))); abstract intuition.
  Defined.

  Definition prog1: option C64.M.Program :=
    C64.PseudoConversion.convertProgram prog0.

  Definition prog2: option AlmostQhasm.Program :=
    match prog1 with
    | Some p => C64.MedialConversion.convertProgram p
    | None => None
    end.

  Definition prog3: option Qhasm.Program :=
    match prog2 with
    | Some p => AlmostConversion.convertProgram p
    | None => None
    end.

  Definition prog4: string :=
    match prog3 with
    | Some p =>
        match (StringConversion.convertProgram p) with
        | Some s => s
        | None => EmptyString
        end
    | None => EmptyString
    end.

  Definition result: string.
    let res := eval vm_compute in prog4 in exact res.
  Defined.

  Open Scope string_scope.
  Print result.
End Progs.

(* Extraction "Progs.ml" Progs. *)
