Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.LanguageWfExtra.
Require Import Crypto.RewriterAllTacticsExtra.
Require Import Crypto.RewriterRulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import LanguageWf.Compilers.
  Import Identifier.Compilers.
  Import LanguageWfExtra.Compilers.
  Import RewriterAllTactics.Compilers.RewriteRules.GoalType.
  Import RewriterAllTacticsExtra.Compilers.RewriteRules.Tactic.
  Import Compilers.Classes.

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

      Lemma Interp_RewriteStripLiteralCasts {t} e (Hwf : Wf e) : expr.Interp (@ident.interp) (@RewriteStripLiteralCasts t e) == expr.Interp (@ident.interp) e.
      Proof. apply Interp_gen_RewriteStripLiteralCasts; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteStripLiteralCasts : wf wf_extra.
    Hint Rewrite @Interp_gen_RewriteStripLiteralCasts @Interp_RewriteStripLiteralCasts : interp interp_extra.
  End Hints.
End Compilers.
