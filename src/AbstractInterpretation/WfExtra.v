Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.API.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.AbstractInterpretation.Wf.

Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import Language.API.Compilers.
  Import Language.WfExtra.Compilers.
  Import AbstractInterpretation.Wf.Compilers.
  Import Compilers.API.

  Import AbstractInterpretation.Wf.Compilers.partial.

  Hint Resolve Wf_Eval Wf_EvalWithBound Wf_EtaExpandWithBound Wf_EtaExpandWithListInfoFromBound : wf_extra.

  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf_extra.

  Hint Resolve Wf_PartialEvaluateWithBounds : wf_extra.
End Compilers.
