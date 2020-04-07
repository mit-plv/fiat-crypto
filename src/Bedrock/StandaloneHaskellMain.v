Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.CLI.
Require Export Crypto.StandaloneHaskellMain.
Require Import Crypto.Bedrock.Stringification.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** N.B. We put bedrock2 first so that the default for these binaries
    is bedrock2 *)
Local Instance bedrock2_supported_languages : ForExtraction.supported_languagesT
  := [("bedrock2", OutputBedrock2API)]
       ++ ForExtraction.default_supported_languages.

Module UnsaturatedSolinas.
  Definition main : IO_unit
    := main_gen ForExtraction.UnsaturatedSolinas.PipelineMain.
End UnsaturatedSolinas.

Module WordByWordMontgomery.
  Definition main : IO_unit
    := main_gen ForExtraction.WordByWordMontgomery.PipelineMain.
End WordByWordMontgomery.

Module SaturatedSolinas.
  Definition main : IO_unit
    := main_gen ForExtraction.SaturatedSolinas.PipelineMain.
End SaturatedSolinas.

Module BaseConversion.
  Definition main : IO_unit
    := main_gen ForExtraction.BaseConversion.PipelineMain.
End BaseConversion.
