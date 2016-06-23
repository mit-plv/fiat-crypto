Require Import QhasmCommon QhasmEvalCommon.
Require Import Pseudo Qhasm AlmostQhasm Conversion Language.
Require Import PseudoConversion AlmostConversion StringConversion.
Require Import Wordize Vectorize Pseudize.

Module Pipeline.
  Export AlmostQhasm Qhasm QhasmString.
  Export Pseudo.

  Transparent Pseudo.Program AlmostQhasm.Program Qhasm.Program QhasmString.Program.
  Transparent Pseudo.Params AlmostQhasm.Params Qhasm.Params QhasmString.Params.

  Definition toAlmost {w s n m} (p: @Pseudo w s n m) : option AlmostProgram :=
    PseudoConversion.convertProgram (mkParams w s n m) tt p.

  Definition toQhasm {w s n m} (p: @Pseudo w s n m) : option (list QhasmStatement) :=
    omap (toAlmost p) (AlmostConversion.convertProgram tt tt).

  Definition toString {w s n m} (p: @Pseudo w s n m) : option string :=
    omap (toQhasm p) (StringConversion.convertProgram tt tt).
End Pipeline.

Module PipelineExample.
  Import Pipeline.

  Local Notation "v [[ i ]]" := (nth i v (wzero _)) (at level 40).
  Local Notation "$$ v" := (natToWord _ v) (at level 40).

  Definition example: @pseudeq 32 W32 1 1 (fun v =>
      Let_In ($$ 1) (fun a =>
        Let_In (v[[0]]) (fun b => [
          a ^& b
      ]))).

    pseudo_solve.
  Defined.

  Definition exStr := Pipeline.toString example.

  (* Eval vm_compute in exStr. *)
End PipelineExample.
