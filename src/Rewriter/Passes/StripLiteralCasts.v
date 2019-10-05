Require Import Crypto.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.Rewriter.AllTacticsExtra.
Require Import Crypto.Rewriter.RulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.API.Compilers.
  Import Language.Wf.Compilers.
  Import Language.WfExtra.Compilers.
  Import Rewriter.AllTactics.Compilers.RewriteRules.GoalType.
  Import Rewriter.AllTacticsExtra.Compilers.RewriteRules.Tactic.
  Import Compilers.Classes.

  Module Import RewriteRules.
    Section __.
      Definition VerifiedRewriterStripLiteralCasts : VerifiedRewriter.
      Proof using All. make_rewriter false strip_literal_casts_rewrite_rules_proofs. Defined.

      Definition RewriteStripLiteralCasts {t} := Eval hnf in @Rewrite VerifiedRewriterStripLiteralCasts t.

      Lemma Wf_RewriteStripLiteralCasts {t} e (Hwf : Wf e) : Wf (@RewriteStripLiteralCasts t e).
      Proof. now apply VerifiedRewriterStripLiteralCasts. Qed.

      Lemma Interp_RewriteStripLiteralCasts {t} e (Hwf : Wf e) : expr.Interp (@Compilers.ident_interp) (@RewriteStripLiteralCasts t e) == expr.Interp (@Compilers.ident_interp) e.
      Proof. now apply VerifiedRewriterStripLiteralCasts. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteStripLiteralCasts : wf wf_extra.
    Hint Rewrite @Interp_RewriteStripLiteralCasts : interp interp_extra.
  End Hints.
End Compilers.
