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
      Definition VerifiedRewriterNBE : VerifiedRewriter_with_args true nbe_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition RewriteNBE {t} := Eval hnf in @Rewrite VerifiedRewriterNBE t.

      Lemma Wf_RewriteNBE {t} e (Hwf : Wf e) : Wf (@RewriteNBE t e).
      Proof. now apply VerifiedRewriterNBE. Qed.

      Lemma Interp_RewriteNBE {t} e (Hwf : Wf e) : API.Interp (@RewriteNBE t e) == API.Interp e.
      Proof. now apply VerifiedRewriterNBE. Qed.
    End __.
  End RewriteRules.

  Definition PartialEvaluate {t} (e : Expr t) : Expr t := RewriteRules.RewriteNBE e.

  Lemma Wf_PartialEvaluate {t} e (Hwf : Wf e) : Wf (@PartialEvaluate t e).
  Proof. apply Wf_RewriteNBE, Hwf. Qed.

  Lemma Interp_PartialEvaluate {t} e (Hwf : Wf e)
    : API.Interp (@PartialEvaluate t e) == API.Interp e.
  Proof. apply Interp_RewriteNBE, Hwf. Qed.

  Module Export Hints.
    Hint Resolve Wf_PartialEvaluate Wf_RewriteNBE : wf wf_extra.
    Hint Rewrite @Interp_PartialEvaluate @Interp_RewriteNBE : interp interp_extra.
  End Hints.
End Compilers.
