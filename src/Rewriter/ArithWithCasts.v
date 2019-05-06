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
      Definition VerifiedRewriterArithWithCasts : VerifiedRewriter.
      Proof using All. make_rewriter false arith_with_casts_rewrite_rules_proofs. Defined.

      Definition RewriteArithWithCasts {t} := Eval hnf in @Rewrite VerifiedRewriterArithWithCasts t.

      Lemma Wf_RewriteArithWithCasts {t} e (Hwf : Wf e) : Wf (@RewriteArithWithCasts t e).
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_gen_RewriteArithWithCasts {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident_gen_interp _ cast_outside_of_range) (@RewriteArithWithCasts t e)
          == expr.Interp (@ident_gen_interp _ cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_RewriteArithWithCasts {t} e (Hwf : Wf e) : expr.Interp (@ident_interp _) (@RewriteArithWithCasts t e) == expr.Interp (@ident_interp _) e.
      Proof. apply Interp_gen_RewriteArithWithCasts; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArithWithCasts : wf.
    Hint Rewrite @Interp_gen_RewriteArithWithCasts @Interp_RewriteArithWithCasts : interp.
  End Hints.
End Compilers.
