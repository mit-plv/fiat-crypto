Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.AbstractInterpretation.
Local Open Scope Z_scope.

Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.
  Import AbstractInterpretation.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import invert_expr.
  Import defaults.

  Module Import partial.
    Import AbstractInterpretation.Compilers.partial.
    Section with_var2.
      Context {var1 var2 : type -> Type}.

      Lemma wf_eta_expand_with_bound G {t} e1 e2 b_in (Hwf : @expr.wf _ _ var1 var2 G t e1 e2)
        : expr.wf G (eta_expand_with_bound e1 b_in) (eta_expand_with_bound e2 b_in).
      Proof.
        cbv [eta_expand_with_bound ident.eta_expand_with_bound eta_expand_with_bound'].
      Admitted.
    End with_var2.

    Lemma Wf_EtaExpandWithBound {t} (E : Expr t) b_in (Hwf : Wf E)
      : Wf (EtaExpandWithBound E b_in).
    Proof. repeat intro; apply wf_eta_expand_with_bound, Hwf. Qed.
  End partial.

  Axiom admit_pf : False.
  Local Notation admit := (match admit_pf with end).

  Lemma Wf_PartialEvaluateWithListInfoFromBounds
        {t} (E : Expr t)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        (Hwf : Wf E)
    : Wf (PartialEvaluateWithListInfoFromBounds E b_in).
  Proof. apply Wf_EtaExpandWithBound, Hwf. Qed.

  Lemma Interp_PartialEvaluateWithListInfoFromBounds
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv _ _) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds E b_in)) arg1 = type.app_curried (Interp E) arg2.
  Proof.
  Admitted.

  Hint Resolve Wf_EtaExpandWithBound Wf_PartialEvaluateWithListInfoFromBounds : wf.

  Theorem CheckedPartialEvaluateWithBounds_Correct
          (relax_zrange : zrange -> option zrange)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {t} (E : Expr t)
          (Hwf : Wf E)
          (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
          (b_out : ZRange.type.base.option.interp (type.final_codomain t))
          rv (Hrv : CheckedPartialEvaluateWithBounds relax_zrange E b_in b_out = inl rv)
    : forall arg1 arg2
             (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv _ _) arg1 arg2)
             (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      ZRange.type.base.option.is_bounded_by b_out (type.app_curried (Interp rv) arg1) = true
      /\ forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) rv) arg1
                                       = type.app_curried (Interp E) arg2.
  Proof.
    cbv [CheckedPartialEvaluateWithBounds CheckPartialEvaluateWithBounds Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    intros arg1 arg2 Harg12 Harg1.
    split.
    { eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; [ eassumption | ].
      clear dependent arg2.
      revert Harg1.
      exact admit. (* boundedness *) }
    { intro cast_outside_of_range; revert cast_outside_of_range Harg12.
      exact admit. (* correctness of interp *) }
  Qed.
End Compilers.
