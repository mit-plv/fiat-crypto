Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.API.
Require Import Crypto.AbstractInterpretation.AbstractInterpretation.
Require Import Crypto.AbstractInterpretation.Wf.
Require Crypto.AbstractInterpretation.Fancy.Proofs.
Require Crypto.AbstractInterpretation.Bottomify.Proofs.

Module Compilers.
  Import Language.Compilers.
  Import AbstractInterpretation.Compilers.
  Import Language.Wf.Compilers.
  Import Language.API.Compilers.
  Import AbstractInterpretation.Wf.Compilers.
  Import AbstractInterpretation.ZRangeProofs.Compilers.
  (*Import AbstractInterpretation.Wf.Compilers.partial.*)
  Import invert_expr.

  Import API.

  Lemma Interp_PartialEvaluateWithBounds
        {opts : AbstractInterpretation.Options}
        relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations
        (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                 -> relax_zrange r = Some r'
                                 -> is_tighter_than_bool z r' = true)
        {t} (E : Expr t)
        (Hwf : Wf E)
        (Ht : type.is_not_higher_order t = true) (* only needed for bottomify version *)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (expr.Interp (@ident.interp) (PartialEvaluateWithBounds relax_zrange skip_annotations_under strip_preexisting_annotations assume_cast_truncates E b_in)) arg1
      = type.app_curried (expr.Interp (@ident.interp) E) arg2.
  Proof.
    cbv [PartialEvaluateWithBounds].
    break_innermost_match.
    all: first [ eapply @Fancy.Proofs.Compilers.Interp_PartialEvaluateWithBounds
               | eapply @Bottomify.Proofs.Compilers.Interp_PartialEvaluateWithBounds ].
    all: assumption.
  Qed.

  Lemma Interp_PartialEvaluateWithBounds_bounded
        {opts : AbstractInterpretation.Options}
        relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations
        (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                 -> relax_zrange r = Some r'
                                 -> is_tighter_than_bool z r' = true)
        {t} (E : Expr t)
        (Hwf : Wf E)
        (Ht : type.is_not_higher_order t = true)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1
             (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1)
             (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      ZRange.type.base.option.is_bounded_by
        (partial.Extract assume_cast_truncates E b_in)
        (type.app_curried (expr.Interp (@ident.interp) (PartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in)) arg1)
      = true.
  Proof.
    cbv [PartialEvaluateWithBounds partial.Extract].
    cbv [fancy_and_powerful_but_exponentially_slow_bounds_analysis AbstractInterpretation.fancy_and_powerful_but_exponentially_slow_bounds_analysis]; destruct opts.
    break_innermost_match.
    all: first [ eapply @Fancy.Proofs.Compilers.Interp_PartialEvaluateWithBounds_bounded
               | eapply @Bottomify.Proofs.Compilers.Interp_PartialEvaluateWithBounds_bounded ].
    all: assumption.
  Qed.

  Lemma Interp_PartialEvaluateWithListInfoFromBounds
        {opts : AbstractInterpretation.Options}
        {t} (E : Expr t)
        (Hwf : Wf E)
        (Ht : type.is_not_higher_order t = true)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds E b_in)) arg1 = type.app_curried (Interp E) arg2.
  Proof.
    cbv [PartialEvaluateWithListInfoFromBounds].
    break_innermost_match.
    all: first [ eapply @Fancy.Proofs.Compilers.Interp_PartialEvaluateWithListInfoFromBounds
               | eapply @Bottomify.Proofs.Compilers.Interp_PartialEvaluateWithListInfoFromBounds ].
    all: assumption.
  Qed.

  Theorem CheckedPartialEvaluateWithBounds_Correct
          {opts : AbstractInterpretation.Options}
          (relax_zrange : zrange -> option zrange)
          (assume_cast_truncates : bool)
          (skip_annotations_under : forall t, ident t -> bool)
          (strip_preexisting_annotations : bool)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {t} (E : Expr t)
          (Hwf : Wf E)
          (Ht : type.is_not_higher_order t = true)
          (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
          (b_out : ZRange.type.base.option.interp (type.final_codomain t))
          rv (Hrv : CheckedPartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in b_out = inl rv)
    : (forall arg1 arg2
              (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
              (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          ZRange.type.base.option.is_bounded_by b_out (type.app_curried (Interp rv) arg1) = true
          /\ type.app_curried (Interp rv) arg1 = type.app_curried (Interp E) arg2)
      /\ Wf rv.
  Proof.
    cbv [CheckedPartialEvaluateWithBounds] in *.
    break_innermost_match_hyps.
    all: first [ eapply @Fancy.Proofs.Compilers.CheckedPartialEvaluateWithBounds_Correct_first_order; eassumption
               | eapply @Bottomify.Proofs.Compilers.CheckedPartialEvaluateWithBounds_Correct; eassumption ].
  Qed.
End Compilers.
