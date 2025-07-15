From Coq Require Import List.
From Coq Require Import String.
Require Import Crypto.CLI.
Require Export Crypto.StandaloneJsOfOCamlMain.
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

  Module FiatCrypto.
    Definition main : unit
      := main_gen ForExtraction.FiatCrypto.PipelineMain.
  End FiatCrypto.
End Bedrock2First.

Module Bedrock2Later.
  Local Instance bedrock2_supported_languages : ForExtraction.supported_languagesT
    := let bedrock2 := ("bedrock2", OutputBedrock2API) in
       match ForExtraction.default_supported_languages with
       | l :: ls => l :: bedrock2 :: ls
       | ls => bedrock2 :: ls
       end.

  Module FiatCrypto.
    Definition main : unit
      := main_gen ForExtraction.FiatCrypto.PipelineMain.
  End FiatCrypto.
End Bedrock2Later.
