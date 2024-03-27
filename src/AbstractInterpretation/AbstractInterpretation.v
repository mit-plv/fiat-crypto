Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Crypto.AbstractInterpretation.Fancy.AbstractInterpretation.
Require Crypto.AbstractInterpretation.Bottomify.AbstractInterpretation.

Module Compilers.
  Export Language.Compilers.
  Export UnderLets.Compilers.
  Export Language.API.Compilers.
  Export AbstractInterpretation.ZRange.Compilers.
  Export Fancy.AbstractInterpretation.Compilers.
  Export Bottomify.AbstractInterpretation.Compilers.

  Module partial.
    Definition Extract {opts : AbstractInterpretation.Options} (assume_cast_truncates : bool) {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow _ t)
    := if fancy_and_powerful_but_exponentially_slow_bounds_analysis
       then     Fancy.AbstractInterpretation.Compilers.partial.Extract assume_cast_truncates e bound
       else Bottomify.AbstractInterpretation.Compilers.partial.Extract assume_cast_truncates e bound.
  End partial.

  Import API.
  Definition PartialEvaluateWithBounds
    {fancy_and_powerful_but_exponentially_slow_bounds_analysis : fancy_and_powerful_but_exponentially_slow_bounds_analysis_opt}
    {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
    (relax_zrange : zrange -> option zrange)
    (assume_cast_truncates : bool)
    (skip_annotations_under : forall t, ident t -> bool)
    (strip_preexisting_annotations : bool)
    {t} (e : Expr t)
    (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := if fancy_and_powerful_but_exponentially_slow_bounds_analysis
       then     Fancy.AbstractInterpretation.Compilers.PartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e bound
       else Bottomify.AbstractInterpretation.Compilers.PartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations e bound.

  Definition PartialEvaluateWithListInfoFromBounds
    {fancy_and_powerful_but_exponentially_slow_bounds_analysis : fancy_and_powerful_but_exponentially_slow_bounds_analysis_opt}
    {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
    {t} (e : Expr t)
    (bound : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : Expr t
    := if fancy_and_powerful_but_exponentially_slow_bounds_analysis
       then     Fancy.AbstractInterpretation.Compilers.PartialEvaluateWithListInfoFromBounds e bound
       else Bottomify.AbstractInterpretation.Compilers.PartialEvaluateWithListInfoFromBounds e bound.

  Definition CheckedPartialEvaluateWithBounds
    {fancy_and_powerful_but_exponentially_slow_bounds_analysis : fancy_and_powerful_but_exponentially_slow_bounds_analysis_opt}
    {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
    (relax_zrange : zrange -> option zrange)
    (assume_cast_truncates : bool)
    (skip_annotations_under : forall t, ident t -> bool)
    (strip_preexisting_annotations : bool)
    {t} (E : Expr t)
    (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    (b_out : ZRange.type.base.option.interp (type.final_codomain t))
    : Expr t + (ZRange.type.base.option.interp (type.final_codomain t) * Expr t + list { t : _ & forall var, @expr var t })
    := if fancy_and_powerful_but_exponentially_slow_bounds_analysis
       then     Fancy.AbstractInterpretation.Compilers.CheckedPartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in b_out
       else Bottomify.AbstractInterpretation.Compilers.CheckedPartialEvaluateWithBounds relax_zrange assume_cast_truncates skip_annotations_under strip_preexisting_annotations E b_in b_out.
End Compilers.
