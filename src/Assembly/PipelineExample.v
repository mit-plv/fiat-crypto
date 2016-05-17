
Require Import Pseudo Qhasm AlmostQhasm Conversion Language.
Require Import PseudoConversion AlmostConversion StringConversion.

Extraction Language Ocaml.
Require Import ExtrOcamlString ExtrOcamlBasic.
Require Import Coq.Strings.String.

Module Progs.
  Module P64 := Pseudo PseudoUnary64.
  Module C64 := PseudoConversion PseudoUnary64.

  Import C64.P.

  Definition prog0: Pseudo 1 1.
    refine (PBin _ Wplus
        (PVar 1 (exist _ 0 _))
        (PConst _ (natToWord _ 1)));
        abstract intuition.
  Defined.

  Definition prog1: option AlmostQhasm.Program :=
    C64.Conv.convertProgram prog0.

  Definition prog2: option Qhasm.Program :=
    match prog1 with
    | Some p => AlmostConversion.convertProgram p
    | None => None
    end.

  Definition prog3: string :=
    match prog2 with
    | Some p =>
        match (StringConversion.convertProgram p) with
        | Some s => s
        | None => EmptyString
        end
    | None => EmptyString
    end.

  Definition result: string.
    let res := eval vm_compute in prog3 in exact res.
  Defined.

  Open Scope string_scope.
  Print result.
End Progs.

(* Extraction "Progs.ml" Progs. *)
