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
      Context (adc_no_carry_to_add : bool).

      Definition VerifiedRewriterArithWithCasts : VerifiedRewriter_with_args false false true (arith_with_casts_rewrite_rules_proofs adc_no_carry_to_add).
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterArithWithCasts.
      Let optsT := Eval hnf in optsT VerifiedRewriterArithWithCasts.

      Definition RewriteArithWithCasts (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterArithWithCasts opts t.

      Lemma Wf_RewriteArithWithCasts opts {t} e (Hwf : Wf e) : Wf (@RewriteArithWithCasts opts t e).
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.

      Lemma Interp_RewriteArithWithCasts opts {t} e (Hwf : Wf e) : API.Interp (@RewriteArithWithCasts opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterArithWithCasts. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArithWithCasts : wf wf_extra.
    Hint Opaque RewriteArithWithCasts : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteArithWithCasts : interp interp_extra.
  End Hints.
End Compilers.
