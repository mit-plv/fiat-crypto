Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Experiments.NewPipeline.RewriterWf1.
Require Import Crypto.Experiments.NewPipeline.RewriterWf2.
Require Import Crypto.Experiments.NewPipeline.RewriterInterpProofs1.
Require Import Crypto.Experiments.NewPipeline.RewriterRulesGood.
Require Import Crypto.Experiments.NewPipeline.RewriterRulesInterpGood.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Import ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import GENERATEDIdentifiersWithoutTypesProofs.Compilers.
  Import Rewriter.Compilers.
  Import RewriterWf1.Compilers.
  Import RewriterWf2.Compilers.
  Import RewriterInterpProofs1.Compilers.
  Import RewriterRulesGood.Compilers.
  Import RewriterRulesInterpGood.Compilers.
  Import expr.Notations.
  Import defaults.
  Import Rewriter.Compilers.RewriteRules.
  Import RewriterWf1.Compilers.RewriteRules.
  Import RewriterWf2.Compilers.RewriteRules.
  Import RewriterInterpProofs1.Compilers.RewriteRules.
  Import RewriterRulesGood.Compilers.RewriteRules.
  Import RewriterRulesInterpGood.Compilers.RewriteRules.

  Module Import RewriteRules.

    Local Ltac start_Wf_or_interp_proof rewrite_head_eq all_rewrite_rules_eq rewrite_head0 :=
      let Rewrite := lazymatch goal with
                     | [ |- Wf ?e ] => head e
                     | [ |- expr.Interp _ ?e == _ ] => head e
                     end in
      cbv [Rewrite]; rewrite rewrite_head_eq; cbv [rewrite_head0]; rewrite all_rewrite_rules_eq.
    Local Ltac start_Wf_proof rewrite_head_eq all_rewrite_rules_eq rewrite_head0 :=
      start_Wf_or_interp_proof rewrite_head_eq all_rewrite_rules_eq rewrite_head0;
      apply Compile.Wf_Rewrite; [ | assumption ];
      let wf_do_again := fresh "wf_do_again" in
      (intros ? ? ? ? wf_do_again ? ?);
      eapply @Compile.wf_assemble_identifier_rewriters;
      eauto using
            pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct
        with nocore;
      try reflexivity.
    Local Ltac start_Interp_proof rewrite_head_eq all_rewrite_rules_eq rewrite_head0 :=
      start_Wf_or_interp_proof rewrite_head_eq all_rewrite_rules_eq rewrite_head0;
      eapply Compile.InterpRewrite; [ | assumption ];
      intros; eapply Compile.interp_assemble_identifier_rewriters with (pident_to_typed:=@pattern.ident.to_typed);
      eauto using
            pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct, pattern.ident.unify_to_typed,
      @ident.gen_interp_Proper, eq_refl
        with nocore.

    Lemma Wf_RewriteNBE {t} e (Hwf : Wf e) : Wf (@RewriteNBE t e).
    Proof.
      start_Wf_proof nbe_rewrite_head_eq nbe_all_rewrite_rules_eq (@nbe_rewrite_head0).
      apply nbe_rewrite_rules_good.
    Qed.
    Lemma Wf_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e) : Wf (@RewriteArith max_const_val t e).
    Proof.
      start_Wf_proof arith_rewrite_head_eq arith_all_rewrite_rules_eq (@arith_rewrite_head0).
      apply arith_rewrite_rules_good.
    Qed.
    Lemma Wf_RewriteArithWithCasts {t} e (Hwf : Wf e) : Wf (@RewriteArithWithCasts t e).
    Proof.
      start_Wf_proof arith_with_casts_rewrite_head_eq arith_with_casts_all_rewrite_rules_eq (@arith_with_casts_rewrite_head0).
      apply arith_with_casts_rewrite_rules_good.
    Qed.
    Lemma Wf_RewriteToFancy (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
            {t} e (Hwf : Wf e) : Wf (@RewriteToFancy invert_low invert_high t e).
    Proof.
      start_Wf_proof fancy_rewrite_head_eq fancy_all_rewrite_rules_eq (@fancy_rewrite_head0).
      eapply fancy_rewrite_rules_good; eassumption.
    Qed.

    Lemma Wf_RewriteToFancyWithCasts (invert_low invert_high : Z -> Z -> option Z)
            (value_range flag_range : ZRange.zrange)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
            {t} e (Hwf : Wf e) : Wf (@RewriteToFancyWithCasts invert_low invert_high value_range flag_range t e).
    Proof.
      start_Wf_proof fancy_with_casts_rewrite_head_eq fancy_with_casts_all_rewrite_rules_eq (@fancy_with_casts_rewrite_head0).
      eapply fancy_with_casts_rewrite_rules_good; eassumption.
    Qed.

    Lemma Interp_gen_RewriteNBE {cast_outside_of_range t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteNBE t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof.
      start_Interp_proof nbe_rewrite_head_eq nbe_all_rewrite_rules_eq (@nbe_rewrite_head0).
      apply nbe_rewrite_rules_interp_good.
    Qed.
    Lemma Interp_gen_RewriteArith {cast_outside_of_range} (max_const_val : Z) {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteArith max_const_val t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof.
      start_Interp_proof arith_rewrite_head_eq arith_all_rewrite_rules_eq (@arith_rewrite_head0).
      apply arith_rewrite_rules_interp_good.
    Qed.

    Lemma Interp_gen_RewriteArithWithCasts {cast_outside_of_range} {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteArithWithCasts t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof.
      start_Interp_proof arith_with_casts_rewrite_head_eq arith_with_casts_all_rewrite_rules_eq (@arith_with_casts_rewrite_head0).
      apply arith_with_casts_rewrite_rules_interp_good.
    Qed.

    Lemma Interp_gen_RewriteToFancy {cast_outside_of_range} (invert_low invert_high : Z -> Z -> option Z)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteToFancy invert_low invert_high t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof.
      start_Interp_proof fancy_rewrite_head_eq fancy_all_rewrite_rules_eq (@fancy_rewrite_head0).
      eapply fancy_rewrite_rules_interp_good; eassumption.
    Qed.

    Lemma Interp_gen_RewriteToFancyWithCasts {cast_outside_of_range} (invert_low invert_high : Z -> Z -> option Z)
          (value_range flag_range : ZRange.zrange)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteToFancyWithCasts invert_low invert_high value_range flag_range t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof.
      start_Interp_proof fancy_with_casts_rewrite_head_eq fancy_with_casts_all_rewrite_rules_eq (@fancy_with_casts_rewrite_head0).
      eapply fancy_with_casts_rewrite_rules_interp_good; eassumption.
    Qed.

    Lemma Interp_RewriteNBE {t} e (Hwf : Wf e) : Interp (@RewriteNBE t e) == Interp e.
    Proof. apply Interp_gen_RewriteNBE; assumption. Qed.
    Lemma Interp_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e)
      : Interp (@RewriteArith max_const_val t e) == Interp e.
    Proof. apply Interp_gen_RewriteArith; assumption. Qed.
    Lemma Interp_RewriteArithWithCasts {t} e (Hwf : Wf e)
      : Interp (@RewriteArithWithCasts t e) == Interp e.
    Proof. apply Interp_gen_RewriteArithWithCasts; assumption. Qed.
    Lemma Interp_RewriteToFancy (invert_low invert_high : Z -> Z -> option Z)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : Interp (@RewriteToFancy invert_low invert_high t e) == Interp e.
    Proof. apply Interp_gen_RewriteToFancy; assumption. Qed.
    Lemma Interp_RewriteToFancyWithCasts (invert_low invert_high : Z -> Z -> option Z)
          (value_range flag_range : ZRange.zrange)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : Interp (@RewriteToFancyWithCasts invert_low invert_high value_range flag_range t e) == Interp e.
    Proof. apply Interp_gen_RewriteToFancyWithCasts; assumption. Qed.
  End RewriteRules.

  Lemma Wf_PartialEvaluate {t} e (Hwf : Wf e) : Wf (@PartialEvaluate t e).
  Proof. apply Wf_RewriteNBE, Hwf. Qed.

  Lemma Interp_gen_PartialEvaluate {cast_outside_of_range} {t} e (Hwf : Wf e)
    : expr.Interp (@ident.gen_interp cast_outside_of_range) (@PartialEvaluate t e) == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
  Proof. apply Interp_gen_RewriteNBE, Hwf. Qed.

  Lemma Interp_PartialEvaluate {t} e (Hwf : Wf e)
    : Interp (@PartialEvaluate t e) == Interp e.
  Proof. apply Interp_gen_PartialEvaluate; assumption. Qed.

  Hint Resolve Wf_PartialEvaluate Wf_RewriteArith Wf_RewriteNBE Wf_RewriteToFancy Wf_RewriteArithWithCasts Wf_RewriteToFancyWithCasts : wf.
  Hint Rewrite @Interp_gen_PartialEvaluate @Interp_gen_RewriteArith @Interp_gen_RewriteNBE @Interp_gen_RewriteToFancy @Interp_gen_RewriteArithWithCasts @Interp_gen_RewriteToFancyWithCasts @Interp_PartialEvaluate @Interp_RewriteArith @Interp_RewriteNBE @Interp_RewriteToFancy @Interp_RewriteArithWithCasts @Interp_RewriteToFancyWithCasts : interp.
End Compilers.
