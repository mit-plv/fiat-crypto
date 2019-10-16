Require Import Coq.ZArith.ZArith.
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
      Context (max_const_val : Z).

      Definition VerifiedRewriterArith : VerifiedRewriter_with_args false (arith_rewrite_rules_proofs max_const_val).
      Proof using All. make_rewriter. Defined.

      Definition RewriteArith {t} := Eval hnf in @Rewrite VerifiedRewriterArith t.

      Lemma Wf_RewriteArith {t} e (Hwf : Wf e) : Wf (@RewriteArith t e).
      Proof. now apply VerifiedRewriterArith. Qed.

      Lemma Interp_RewriteArith {t} e (Hwf : Wf e) : API.Interp (@RewriteArith t e) == API.Interp e.
      Proof. now apply VerifiedRewriterArith. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArith : wf wf_extra.
    Hint Rewrite @Interp_RewriteArith : interp interp_extra.
  End Hints.
End Compilers.
