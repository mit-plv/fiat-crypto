Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.API.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.AbstractInterpretation.Wf.
Require Import Crypto.AbstractInterpretation.Fancy.WfExtra.
Require Import Crypto.AbstractInterpretation.Bottomify.WfExtra.

Module Compilers.
  Export AbstractInterpretation.Fancy.WfExtra.Compilers.
  Export AbstractInterpretation.Bottomify.WfExtra.Compilers.
  Import AbstractInterpretation.AbstractInterpretation.Compilers.
  Import AbstractInterpretation.Wf.Compilers.
  Import Compilers.API.

  (*
  Import AbstractInterpretation.AbstractInterpretation.Compilers.partial.
  Import AbstractInterpretation.Wf.Compilers.partial.
   *)

  (*
#[global]
  Hint Resolve Wf_Eval Wf_EvalWithBound Wf_EtaExpandWithBound Wf_EtaExpandWithListInfoFromBound Wf_StripAnnotations Wf_StripAllAnnotations : wf_extra.
#[global]
  Hint Opaque partial.Eval EvalWithBound EtaExpandWithBound EtaExpandWithListInfoFromBound StripAnnotations StripAllAnnotations : wf_extra interp_extra.
*)
#[global]
  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf_extra.
#[global]
  Hint Opaque PartialEvaluateWithListInfoFromBounds : wf_extra interp_extra.

#[global]
  Hint Resolve Wf_PartialEvaluateWithBounds : wf_extra.
#[global]
  Hint Opaque PartialEvaluateWithBounds : wf_extra interp_extra.
End Compilers.
