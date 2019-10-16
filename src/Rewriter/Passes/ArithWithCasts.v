Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.Rewriter.AllTacticsExtra.
Require Import Crypto.Rewriter.RulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.API.Compilers.
  Import Language.Wf.Compilers.
  Import Language.WfExtra.Compilers.
  Import Rewriter.AllTacticsExtra.Compilers.RewriteRules.GoalType.
  Import Rewriter.AllTactics.Compilers.RewriteRules.Tactic.
  Import Compilers.Classes.

  Module Import RewriteRules.
    Section __.
      Definition VerifiedRewriterArithWithCasts : VerifiedRewriter_with_args false arith_with_casts_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition RewriteArithWithCasts {t} := Eval hnf in @Rewrite VerifiedRewriterArithWithCasts t.

      Lemma Wf_RewriteArithWithCasts {t} e (Hwf : Wf e) : Wf (@RewriteArithWithCasts t e).
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_RewriteArithWithCasts {t} e (Hwf : Wf e) : API.Interp (@RewriteArithWithCasts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArithWithCasts : wf wf_extra.
    Hint Rewrite @Interp_RewriteArithWithCasts : interp interp_extra.
  End Hints.
End Compilers.
