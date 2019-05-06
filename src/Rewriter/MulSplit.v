Require Import Coq.ZArith.ZArith.
Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.RewriterAllTacticsExtra.
Require Import Crypto.RewriterRulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import LanguageWf.Compilers.
  Import RewriterAllTactics.Compilers.RewriteRules.GoalType.
  Import RewriterAllTacticsExtra.Compilers.RewriteRules.Tactic.
  Import Compilers.Classes.

  Module Import RewriteRules.
    Section __.
      Context (bitwidth : Z)
              (lgcarrymax : Z).

      Definition VerifiedRewriterMulSplit : VerifiedRewriter.
      Proof using All. make_rewriter false (mul_split_rewrite_rules_proofs bitwidth lgcarrymax). Defined.

      Definition RewriteMulSplit {t} := Eval hnf in @Rewrite VerifiedRewriterMulSplit t.

      Lemma Wf_RewriteMulSplit {t} e (Hwf : Wf e) : Wf (@RewriteMulSplit t e).
      Proof. now apply VerifiedRewriterMulSplit. Qed.

      Lemma Interp_gen_RewriteMulSplit {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident_gen_interp _ cast_outside_of_range) (@RewriteMulSplit t e)
          == expr.Interp (@ident_gen_interp _ cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterMulSplit. Qed.

      Lemma Interp_RewriteMulSplit {t} e (Hwf : Wf e) : expr.Interp (@ident_interp _) (@RewriteMulSplit t e) == expr.Interp (@ident_interp _) e.
      Proof. apply Interp_gen_RewriteMulSplit; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteMulSplit : wf.
    Hint Rewrite @Interp_gen_RewriteMulSplit @Interp_RewriteMulSplit : interp.
  End Hints.
End Compilers.
