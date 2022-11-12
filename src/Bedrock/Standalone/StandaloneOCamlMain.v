Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Crypto.CLI.
Require Export Crypto.StandaloneOCamlMain.
Require Import Crypto.Bedrock.Field.Stringification.Stringification.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

(** Needed to work around COQBUG(https://github.com/coq/coq/issues/4875) *)
Extraction Inline coqutil.Map.SortedListString.map.

Module Bedrock2First.
  (** N.B. We put bedrock2 first so that the default for these binaries
      is bedrock2 *)
  Local Instance bedrock2_supported_languages : ForExtraction.supported_languagesT
    := [("bedrock2", OutputBedrock2API)]
         ++ ForExtraction.default_supported_languages.

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

  Module SolinasReduction.
    Definition main : unit
      := main_gen ForExtraction.SolinasReduction.PipelineMain.
  End SolinasReduction.

  Module BaseConversion.
    Definition main : unit
      := main_gen ForExtraction.BaseConversion.PipelineMain.
  End BaseConversion.
End Bedrock2First.

Module Bedrock2Later.
  Local Instance bedrock2_supported_languages : ForExtraction.supported_languagesT
    := let bedrock2 := ("bedrock2", OutputBedrock2API) in
       match ForExtraction.default_supported_languages with
       | l :: ls => l :: bedrock2 :: ls
       | ls => bedrock2 :: ls
       end.

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

  Module SolinasReduction.
    Definition main : unit
      := main_gen ForExtraction.SolinasReduction.PipelineMain.
  End SolinasReduction.

  Module BaseConversion.
    Definition main : unit
      := main_gen ForExtraction.BaseConversion.PipelineMain.
  End BaseConversion.
End Bedrock2Later.
