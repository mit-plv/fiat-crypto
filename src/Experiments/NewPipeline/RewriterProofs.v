Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Import ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import Rewriter.Compilers.
  Import expr.Notations.
  Import defaults.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    Lemma Wf_RewriteNBE {t} e (Hwf : Wf e) : Wf (@RewriteNBE t e).
    Admitted.
    Lemma Wf_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e) : Wf (@RewriteArith max_const_val t e).
    Admitted.
    Lemma Wf_RewriteToFancy (invert_low invert_high : Z -> Z -> option Z) {t} e (Hwf : Wf e) : Wf (@RewriteToFancy invert_low invert_high t e).
    Admitted.

    Lemma Interp_RewriteNBE {t} e (Hwf : Wf e) : Interp (@RewriteNBE t e) == Interp e.
    Admitted.
    Lemma Interp_RewriteArith (max_const_val : Z) {t} e (Hwf : Wf e) : Interp (@RewriteArith max_const_val t e) == Interp e.
    Admitted.

    Lemma Interp_RewriteToFancy (invert_low invert_high : Z -> Z -> option Z)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
          {t} e (Hwf : Wf e)
      : Interp (@RewriteToFancy invert_low invert_high t e) == Interp e.
    Admitted.
  End RewriteRules.

  Lemma Wf_PartialEvaluate {t} e (Hwf : Wf e) : Wf (@PartialEvaluate t e).
  Proof. apply Wf_RewriteNBE, Hwf. Qed.

  Lemma Interp_PartialEvaluate {t} e (Hwf : Wf e) : Interp (@PartialEvaluate t e) == Interp e.
  Proof. apply Interp_RewriteNBE, Hwf. Qed.


  Hint Resolve Wf_PartialEvaluate Wf_RewriteArith Wf_RewriteNBE Wf_RewriteToFancy : wf.
  Hint Rewrite @Interp_PartialEvaluate @Interp_RewriteArith @Interp_RewriteNBE @Interp_RewriteToFancy : interp.
End Compilers.
