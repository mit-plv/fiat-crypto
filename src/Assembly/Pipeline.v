
Require Import QhasmCommon QhasmEvalCommon.
Require Import Pseudo Qhasm AlmostQhasm Conversion Language.
Require Import PseudoConversion AlmostConversion StringConversion.

Module Pipeline.
  Export Pseudo Util.

  Definition toAlmost (p: Pseudo inVars outVars): option AlmostQhasm.Program :=
    PseudoConversion.convertProgram p.

  Definition toQhasm (p: Pseudo inVars outVars): option Qhasm.Program :=
    omap (toAlmost p) AlmostConversion.convertProgram.

  Definition toString (p: Pseudo inVars outVars): option string :=
    omap (toQhasm p) StringConversion.convertProgram.
End Pipeline.

Module PipelineExample.
  Import Pipeline.

  Program Definition asdf: Program Unary32 := ($0 :+: $0)%p.

  Definition exStr := Pipeline.toString ex.
    | Some x => x
    | None => EmptyString
    end.
  Defined.

Open Scope string_scope.
Print Result.

Extraction "Result.ml" Result.
