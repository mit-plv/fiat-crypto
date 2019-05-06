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
      Definition VerifiedRewriterNBE : VerifiedRewriter.
      Proof using All. make_rewriter true nbe_rewrite_rules_proofs. Defined.

      Definition RewriteNBE {t} := Eval hnf in @Rewrite VerifiedRewriterNBE t.

      Lemma Wf_RewriteNBE {t} e (Hwf : Wf e) : Wf (@RewriteNBE t e).
      Proof. now apply VerifiedRewriterNBE. Qed.

      Lemma Interp_gen_RewriteNBE {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident_gen_interp _ cast_outside_of_range) (@RewriteNBE t e)
          == expr.Interp (@ident_gen_interp _ cast_outside_of_range) e.
      Proof. now apply VerifiedRewriterNBE. Qed.

      Lemma Interp_RewriteNBE {t} e (Hwf : Wf e) : expr.Interp (@ident_interp _) (@RewriteNBE t e) == expr.Interp (@ident_interp _) e.
      Proof. apply Interp_gen_RewriteNBE; assumption. Qed.
    End __.
  End RewriteRules.

  Definition PartialEvaluate {t} (e : Expr t) : Expr t := RewriteRules.RewriteNBE e.

  Lemma Wf_PartialEvaluate {t} e (Hwf : Wf e) : Wf (@PartialEvaluate t e).
  Proof. apply Wf_RewriteNBE, Hwf. Qed.

  Lemma Interp_gen_PartialEvaluate {cast_outside_of_range} {t} e (Hwf : Wf e)
    : expr.Interp (@ident_gen_interp _ cast_outside_of_range) (@PartialEvaluate t e) == expr.Interp (@ident_gen_interp _ cast_outside_of_range) e.
  Proof. apply Interp_gen_RewriteNBE, Hwf. Qed.

  Lemma Interp_PartialEvaluate {t} e (Hwf : Wf e)
    : expr.Interp (@ident_interp _) (@PartialEvaluate t e) == expr.Interp (@ident_interp _) e.
  Proof. apply Interp_gen_PartialEvaluate; assumption. Qed.

  Module Export Hints.
    Hint Resolve Wf_PartialEvaluate Wf_RewriteNBE : wf.
    Hint Rewrite @Interp_gen_PartialEvaluate @Interp_gen_RewriteNBE @Interp_PartialEvaluate @Interp_RewriteNBE : interp.
  End Hints.
End Compilers.
