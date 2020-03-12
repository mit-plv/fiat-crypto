Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.CLI.
Require Export Crypto.StandaloneOCamlMain.
Require Import Crypto.Bedrock.Stringification.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Local Instance bedrock2_supported_languages : ForExtraction.supported_languagesT
  := ForExtraction.default_supported_languages
       ++ [("bedrock2", OutputBedrock2API)].

Module UnsaturatedSolinas.
  Definition main : unit
    := main_gen ForExtraction.UnsaturatedSolinas.PipelineMain.
End UnsaturatedSolinas.

Module WordByWordMontgomery.
  Definition main : unit
    := main_gen ForExtraction.WordByWordMontgomery.PipelineMain.
End WordByWordMontgomery.

Module SaturatedSolinas.
  Definition main : unit
    := main_gen ForExtraction.SaturatedSolinas.PipelineMain.
End SaturatedSolinas.

Module BaseConversion.
  Definition main : unit
    := main_gen ForExtraction.BaseConversion.PipelineMain.
End BaseConversion.
