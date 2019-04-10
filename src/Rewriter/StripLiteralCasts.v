Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.RewriterAllTactics.
Require Import Crypto.RewriterRulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.Compilers.defaults.
  Import LanguageWf.Compilers.
  Import RewriterAllTactics.Compilers.RewriteRules.GoalType.
  Import RewriterAllTactics.Compilers.RewriteRules.Tactic.

  Module Import RewriteRules.
    Section __.
      Definition VerifiedRewriterStripLiteralCasts : VerifiedRewriter.
      Proof using All. make_rewriter false strip_literal_casts_rewrite_rules_proofs. Defined.

      Definition RewriteStripLiteralCasts {t} := Eval hnf in @Rewrite VerifiedRewriterStripLiteralCasts t.

      Lemma Wf_RewriteStripLiteralCasts {t} e (Hwf : Wf e) : Wf (@RewriteStripLiteralCasts t e).
      Proof. now apply VerifiedRewriterStripLiteralCasts. Qed.

      Lemma Interp_gen_RewriteStripLiteralCasts {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteStripLiteralCasts t e)
          == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterStripLiteralCasts. Qed.

      Lemma Interp_RewriteStripLiteralCasts {t} e (Hwf : Wf e) : Interp (@RewriteStripLiteralCasts t e) == Interp e.
      Proof. apply Interp_gen_RewriteStripLiteralCasts; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteStripLiteralCasts : wf.
    Hint Rewrite @Interp_gen_RewriteStripLiteralCasts @Interp_RewriteStripLiteralCasts : interp.
  End Hints.
End Compilers.
