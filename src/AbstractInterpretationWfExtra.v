Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.Identifier.
Require Import Crypto.IdentifierExtra.
Require Import Crypto.LanguageWfExtra.
Require Import Crypto.AbstractInterpretationWf.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import Identifier.Compilers.
  Import IdentifierExtra.Compilers.
  Import LanguageWfExtra.Compilers.
  Import AbstractInterpretationWf.Compilers.
  Import Compilers.defaults.

  Import AbstractInterpretationWf.Compilers.partial.

  Hint Resolve Wf_Eval Wf_EvalWithBound Wf_EtaExpandWithBound Wf_EtaExpandWithListInfoFromBound : wf_extra.

  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf_extra.

  Hint Resolve Wf_PartialEvaluateWithBounds : wf_extra.
End Compilers.
