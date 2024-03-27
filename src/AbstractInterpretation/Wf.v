Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Wf.
Require Crypto.AbstractInterpretation.Fancy.Wf.
Require Crypto.AbstractInterpretation.Bottomify.Wf.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.

Module Compilers.
  Import Language.Compilers.
  Import AbstractInterpretation.AbstractInterpretation.Compilers.
  Import Language.Wf.Compilers.
  Import API.

  Export AbstractInterpretation.Fancy.Wf.Compilers (partial.abstract_domain_R).
  Import AbstractInterpretation.Fancy.Wf.Compilers.partial (abstract_domain_R).

  Lemma Wf_PartialEvaluateWithListInfoFromBounds
        {opts : AbstractInterpretation.Options}
        {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithListInfoFromBounds E b_in).
  Proof. cbv [PartialEvaluateWithListInfoFromBounds]; break_innermost_match; eauto with wf. Qed.
#[global]
  Hint Resolve Wf_PartialEvaluateWithListInfoFromBounds : wf.
#[global]
  Hint Opaque PartialEvaluateWithListInfoFromBounds : wf interp rewrite.

  Lemma Wf_PartialEvaluateWithBounds
        {opts : AbstractInterpretation.Options}
        {relax_zrange} {assume_cast_truncates : bool} {skip_annotations_under : forall t, ident t -> bool} {strip_preexisting_annotations : bool} {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R base.type ZRange.type.base.option.interp (fun t0 : base.type => eq))) b_in}
    : Wf (PartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in).
  Proof. cbv [PartialEvaluateWithBounds]; break_innermost_match; eauto with wf. Qed.
#[global]
  Hint Resolve Wf_PartialEvaluateWithBounds : wf.
#[global]
  Hint Opaque PartialEvaluateWithBounds : wf interp rewrite.
End Compilers.
