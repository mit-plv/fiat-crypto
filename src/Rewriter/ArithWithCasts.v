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
      Definition VerifiedRewriterArithWithCasts : VerifiedRewriter.
      Proof using All. make_rewriter false arith_with_casts_rewrite_rules_proofs. Defined.

      Definition RewriteArithWithCasts {t} := Eval hnf in @Rewrite VerifiedRewriterArithWithCasts t.

      Lemma Wf_RewriteArithWithCasts {t} e (Hwf : Wf e) : Wf (@RewriteArithWithCasts t e).
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_gen_RewriteArithWithCasts {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteArithWithCasts t e)
          == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_RewriteArithWithCasts {t} e (Hwf : Wf e) : expr.Interp (@ident.interp) (@RewriteArithWithCasts t e) == expr.Interp (@ident.interp) e.
      Proof. apply Interp_gen_RewriteArithWithCasts; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArithWithCasts : wf wf_extra.
    Hint Rewrite @Interp_gen_RewriteArithWithCasts @Interp_RewriteArithWithCasts : interp interp_extra.
  End Hints.
End Compilers.
