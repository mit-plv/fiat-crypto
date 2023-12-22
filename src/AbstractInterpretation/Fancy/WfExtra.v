Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.API.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.AbstractInterpretation.Fancy.AbstractInterpretation.
Require Import Crypto.AbstractInterpretation.Fancy.Wf.

Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import Language.API.Compilers.
  Import Language.WfExtra.Compilers.
  Import AbstractInterpretation.Fancy.AbstractInterpretation.Compilers.
  Import AbstractInterpretation.Fancy.Wf.Compilers.
  Import Compilers.API.

  Import AbstractInterpretation.Fancy.AbstractInterpretation.Compilers.partial.
  Import AbstractInterpretation.Fancy.Wf.Compilers.partial.

#[global]
  Hint Resolve Wf_Eval Wf_EvalWithBound Wf_EtaExpandWithBound Wf_EtaExpandWithListInfoFromBound Wf_StripAnnotations Wf_StripAllAnnotations : wf_extra.
#[global]
  Hint Opaque partial.Eval EvalWithBound EtaExpandWithBound EtaExpandWithListInfoFromBound StripAnnotations StripAllAnnotations : wf_extra interp_extra.

#[global]
  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf_extra.
#[global]
  Hint Opaque PartialEvaluateWithListInfoFromBounds : wf_extra interp_extra.

#[global]
  Hint Resolve Wf_PartialEvaluateWithBounds : wf_extra.
#[global]
  Hint Opaque PartialEvaluateWithBounds : wf_extra interp_extra.
End Compilers.
