Require Import Coq.ZArith.ZArith.
Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.RewriterAllTactics.
Require Import Crypto.RewriterRulesProofs.
Require Import Crypto.IdentifiersGENERATEDProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.Compilers.defaults.
  Import LanguageWf.Compilers.
  Import RewriterAllTactics.Compilers.RewriteRules.GoalType.
  Import RewriterAllTactics.Compilers.RewriteRules.Tactic.
  Import IdentifiersGENERATEDProofs.Compilers.pattern.ident.

  Module Import RewriteRules.
    Section __.
      Context (bitwidth : Z)
              (lgcarrymax : Z).

      Definition VerifiedRewriterMulSplit : VerifiedRewriter.
      Proof using All. make_rewriter package_proofs false (mul_split_rewrite_rules_proofs bitwidth lgcarrymax). Defined.

      Definition RewriteMulSplit {t} := Eval hnf in @Rewrite VerifiedRewriterMulSplit t.

      Lemma Wf_RewriteMulSplit {t} e (Hwf : Wf e) : Wf (@RewriteMulSplit t e).
      Proof. now apply VerifiedRewriterMulSplit. Qed.

      Lemma Interp_gen_RewriteMulSplit {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteMulSplit t e)
          == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterMulSplit. Qed.

      Lemma Interp_RewriteMulSplit {t} e (Hwf : Wf e) : Interp (@RewriteMulSplit t e) == Interp e.
      Proof. apply Interp_gen_RewriteMulSplit; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteMulSplit : wf.
    Hint Rewrite @Interp_gen_RewriteMulSplit @Interp_RewriteMulSplit : interp.
  End Hints.
End Compilers.
