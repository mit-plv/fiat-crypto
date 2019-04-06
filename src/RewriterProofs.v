Require Import Coq.ZArith.ZArith.
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.LanguageWf.
Require Import Crypto.UnderLetsProofs.
Require Import Crypto.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Rewriter.
Require Import Crypto.RewriterFull.
Require Import Crypto.RewriterWf1.
Require Import Crypto.RewriterWf2.
Require Import Crypto.RewriterInterpProofs1.
Require Import Crypto.RewriterRulesProofs.
Require Import Crypto.RewriterRulesGood.
Require Import Crypto.RewriterRulesInterpGood.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import GENERATEDIdentifiersWithoutTypesProofs.Compilers.
  Import Rewriter.Compilers.
  Import RewriterFull.Compilers.
  Import RewriterWf1.Compilers.
  Import RewriterWf2.Compilers.
  Import RewriterInterpProofs1.Compilers.
  Import RewriterRulesGood.Compilers.
  Import RewriterRulesInterpGood.Compilers.
  Import expr.Notations.
  Import defaults.
  Import Rewriter.Compilers.RewriteRules.
  Import RewriterFull.Compilers.RewriteRules.
  Import RewriterWf1.Compilers.RewriteRules.
  Import RewriterWf2.Compilers.RewriteRules.
  Import RewriterInterpProofs1.Compilers.RewriteRules.
  Import RewriterRulesGood.Compilers.RewriteRules.
  Import RewriterRulesInterpGood.Compilers.RewriteRules.
  Import RewriterWf1.Compilers.RewriteRules.GoalType.
  Import RewriterWf1.Compilers.RewriteRules.WfTactics.GoalType.
  Import RewriterWf1.Compilers.RewriteRules.InterpTactics.GoalType.
  Import RewriterWf1.Compilers.RewriteRules.GoalType.
  Import RewriterWf1.Compilers.RewriteRules.WfTactics.Tactic.
  Import RewriterWf1.Compilers.RewriteRules.InterpTactics.Tactic.

  Module Import RewriteRules.
    Module Export Tactics.
      Definition VerifiedRewriter_of_Rewriter
                 (R : RewriterT)
                 (RWf : Wf_GoalT R)
                 (RInterp : Interp_GoalT R)
                 (RProofs : PrimitiveHList.hlist
                              (@snd bool Prop)
                              (List.skipn (dummy_count (Rewriter_data R)) (rewrite_rules_specs (Rewriter_data R))))
      : VerifiedRewriter.
      Proof.
        simple refine
               (let HWf := _ in
                let HInterp_gen := _ in
                @Build_VerifiedRewriter R RWf RInterp HWf HInterp_gen (HInterp_gen _));
          [ | clear HWf ]; intros.
        all: abstract (
                 rewrite Rewrite_eq; cbv [Make.Rewrite]; rewrite rewrite_head_eq, all_rewrite_rules_eq;
                 first [ apply Compile.Wf_Rewrite; [ | assumption ];
                         let wf_do_again := fresh "wf_do_again" in
                         (intros ? ? ? ? wf_do_again ? ?);
                         eapply @Compile.wf_assemble_identifier_rewriters;
                         eauto using
                               pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct
                           with nocore;
                         try reflexivity
                       | eapply Compile.InterpRewrite; [ | assumption ];
                         intros; eapply Compile.interp_assemble_identifier_rewriters with (pident_to_typed:=@pattern.ident.to_typed);
                         eauto using
                               pattern.Raw.ident.to_typed_invert_bind_args, pattern.ident.eta_ident_cps_correct, pattern.ident.unify_to_typed,
                         @ident.gen_interp_Proper, eq_refl
                           with nocore ]).
      Defined.
    End Tactics.

    Definition VerifiedRewriterNBE : VerifiedRewriter
      := @VerifiedRewriter_of_Rewriter RewriterNBE RewriterRulesNBEWf RewriterRulesNBEInterp nbe_rewrite_rules_proofs.
    Definition VerifiedRewriterArith (max_const_val : Z) : VerifiedRewriter
      := @VerifiedRewriter_of_Rewriter (RewriterArith max_const_val) (RewriterRulesArithWf max_const_val) (RewriterRulesArithInterp max_const_val) (arith_rewrite_rules_proofs max_const_val).
    Definition VerifiedRewriterArithWithCasts : VerifiedRewriter
      := @VerifiedRewriter_of_Rewriter RewriterArithWithCasts RewriterRulesArithWithCastsWf RewriterRulesArithWithCastsInterp arith_with_casts_rewrite_rules_proofs.
    Definition VerifiedRewriterStripLiteralCasts : VerifiedRewriter
      := @VerifiedRewriter_of_Rewriter RewriterStripLiteralCasts RewriterRulesStripLiteralCastsWf RewriterRulesStripLiteralCastsInterp strip_literal_casts_rewrite_rules_proofs.
    Definition VerifiedRewriterToFancy (invert_low invert_high : Z -> Z -> option Z)
               (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
               (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
      : VerifiedRewriter
      := @VerifiedRewriter_of_Rewriter (RewriterToFancy invert_low invert_high) (RewriterRulesToFancyWf invert_low invert_high Hlow Hhigh) (RewriterRulesToFancyInterp invert_low invert_high Hlow Hhigh) fancy_rewrite_rules_proofs.
    Definition VerifiedRewriterToFancyWithCasts (invert_low invert_high : Z -> Z -> option Z)
               (value_range flag_range : ZRange.zrange)
               (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
               (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
      : VerifiedRewriter
      := @VerifiedRewriter_of_Rewriter (RewriterToFancyWithCasts invert_low invert_high value_range flag_range) (RewriterRulesToFancyWithCastsWf invert_low invert_high value_range flag_range Hlow Hhigh) (RewriterRulesToFancyWithCastsInterp invert_low invert_high value_range flag_range Hlow Hhigh) (fancy_with_casts_rewrite_rules_proofs invert_low invert_high value_range flag_range Hlow Hhigh).

    Lemma Wf_RewriteNBE {t} e (Hwf : Wf e) : Wf (@RewriteNBE t e).
    Proof. now apply VerifiedRewriterNBE. Qed.
    Lemma Wf_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e) : Wf (@RewriteArith max_const_val t e).
    Proof. now apply VerifiedRewriterArith. Qed.
    Lemma Wf_RewriteArithWithCasts {t} e (Hwf : Wf e) : Wf (@RewriteArithWithCasts t e).
    Proof. now apply VerifiedRewriterArithWithCasts. Qed.
    Lemma Wf_RewriteStripLiteralCasts {t} e (Hwf : Wf e) : Wf (@RewriteStripLiteralCasts t e).
    Proof. now apply VerifiedRewriterStripLiteralCasts. Qed.
    Lemma Wf_RewriteToFancy (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
            {t} e (Hwf : Wf e) : Wf (@RewriteToFancy invert_low invert_high t e).
    Proof. unshelve eapply VerifiedRewriterToFancy; multimatch goal with H : _ |- _ => refine H end. Qed.
    Lemma Wf_RewriteToFancyWithCasts (invert_low invert_high : Z -> Z -> option Z)
            (value_range flag_range : ZRange.zrange)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
            {t} e (Hwf : Wf e) : Wf (@RewriteToFancyWithCasts invert_low invert_high value_range flag_range t e).
    Proof. now unshelve eapply VerifiedRewriterToFancyWithCasts. Qed.

    Lemma Interp_gen_RewriteNBE {cast_outside_of_range t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteNBE t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof. now apply VerifiedRewriterNBE. Qed.
    Lemma Interp_gen_RewriteArith {cast_outside_of_range} (max_const_val : Z) {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteArith max_const_val t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof. now apply VerifiedRewriterArith. Qed.
    Lemma Interp_gen_RewriteArithWithCasts {cast_outside_of_range} {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteArithWithCasts t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof. now apply VerifiedRewriterArithWithCasts. Qed.
    Lemma Interp_gen_RewriteStripLiteralCasts {cast_outside_of_range} {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteStripLiteralCasts t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof. now apply VerifiedRewriterStripLiteralCasts. Qed.
    Lemma Interp_gen_RewriteToFancy {cast_outside_of_range} (invert_low invert_high : Z -> Z -> option Z)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteToFancy invert_low invert_high t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof. unshelve eapply VerifiedRewriterToFancy; multimatch goal with H : _ |- _ => refine H end. Qed.
    Lemma Interp_gen_RewriteToFancyWithCasts {cast_outside_of_range} (invert_low invert_high : Z -> Z -> option Z)
          (value_range flag_range : ZRange.zrange)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteToFancyWithCasts invert_low invert_high value_range flag_range t e)
        == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
    Proof. now unshelve eapply VerifiedRewriterToFancyWithCasts. Qed.

    Lemma Interp_RewriteNBE {t} e (Hwf : Wf e) : Interp (@RewriteNBE t e) == Interp e.
    Proof. apply Interp_gen_RewriteNBE; assumption. Qed.
    Lemma Interp_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e)
      : Interp (@RewriteArith max_const_val t e) == Interp e.
    Proof. apply Interp_gen_RewriteArith; assumption. Qed.
    Lemma Interp_RewriteArithWithCasts {t} e (Hwf : Wf e)
      : Interp (@RewriteArithWithCasts t e) == Interp e.
    Proof. apply Interp_gen_RewriteArithWithCasts; assumption. Qed.
    Lemma Interp_RewriteStripLiteralCasts {t} e (Hwf : Wf e)
      : Interp (@RewriteStripLiteralCasts t e) == Interp e.
    Proof. apply Interp_gen_RewriteStripLiteralCasts; assumption. Qed.
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

  Hint Resolve Wf_PartialEvaluate Wf_RewriteArith Wf_RewriteNBE Wf_RewriteToFancy Wf_RewriteArithWithCasts Wf_RewriteStripLiteralCasts Wf_RewriteToFancyWithCasts : wf.
  Hint Rewrite @Interp_gen_PartialEvaluate @Interp_gen_RewriteArith @Interp_gen_RewriteNBE @Interp_gen_RewriteToFancy @Interp_gen_RewriteArithWithCasts @Interp_gen_RewriteStripLiteralCasts @Interp_gen_RewriteToFancyWithCasts @Interp_PartialEvaluate @Interp_RewriteArith @Interp_RewriteNBE @Interp_RewriteToFancy @Interp_RewriteArithWithCasts @Interp_RewriteStripLiteralCasts @Interp_RewriteToFancyWithCasts : interp.
End Compilers.
