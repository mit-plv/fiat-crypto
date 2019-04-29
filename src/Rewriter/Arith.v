Require Import Coq.ZArith.ZArith.
Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.RewriterAllTactics.
Require Import Crypto.RewriterRulesProofs.
Require Import Crypto.GENERATEDIdentifiersWithoutTypesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.Compilers.defaults.
  Import LanguageWf.Compilers.
  Import RewriterAllTactics.Compilers.RewriteRules.GoalType.
  Import RewriterAllTactics.Compilers.RewriteRules.Tactic.
  Import GENERATEDIdentifiersWithoutTypesProofs.Compilers.pattern.ident.

  Module Import RewriteRules.
    Section __.
      Context (max_const_val : Z).

      Definition VerifiedRewriterArith : VerifiedRewriter.
      Proof using All. make_rewriter package_proofs false (arith_rewrite_rules_proofs max_const_val). Defined.

      Definition RewriteArith {t} := Eval hnf in @Rewrite VerifiedRewriterArith t.

      Lemma Wf_RewriteArith {t} e (Hwf : Wf e) : Wf (@RewriteArith t e).
      Proof. now apply VerifiedRewriterArith. Qed.

      Lemma Interp_gen_RewriteArith {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteArith t e)
          == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterArith. Qed.

      Lemma Interp_RewriteArith {t} e (Hwf : Wf e) : Interp (@RewriteArith t e) == Interp e.
      Proof. apply Interp_gen_RewriteArith; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArith : wf.
    Hint Rewrite @Interp_gen_RewriteArith @Interp_RewriteArith : interp.
  End Hints.
End Compilers.
