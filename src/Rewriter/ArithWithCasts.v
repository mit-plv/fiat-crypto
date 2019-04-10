Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.RewriterProofsTactics.
Require Import Crypto.RewriterRulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.Compilers.defaults.
  Import LanguageWf.Compilers.
  Import RewriterProofsTactics.Compilers.RewriteRules.GoalType.
  Import RewriterProofsTactics.Compilers.RewriteRules.Tactic.

  Module Import RewriteRules.
    Section __.
      Definition VerifiedRewriterArithWithCasts : VerifiedRewriter.
      Proof using All. make_rewriter false arith_with_casts_rewrite_rules_proofs. Defined.

      Definition RewriteArithWithCasts {t} := Eval hnf in @Rewrite VerifiedRewriterArithWithCasts t.

      Lemma Wf_RewriteArithWithCasts {t} e (Hwf : Wf e) : Wf (@RewriteArithWithCasts t e).
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_gen_RewriteArithWithCasts {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteArithWithCasts t e)
          == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_RewriteArithWithCasts {t} e (Hwf : Wf e) : Interp (@RewriteArithWithCasts t e) == Interp e.
      Proof. apply Interp_gen_RewriteArithWithCasts; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArithWithCasts : wf.
    Hint Rewrite @Interp_gen_RewriteArithWithCasts @Interp_RewriteArithWithCasts : interp.
  End Hints.
End Compilers.
