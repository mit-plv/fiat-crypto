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
      Context (bitwidth : Z).

      Definition VerifiedRewriterNoSelect : VerifiedRewriter_with_args false false true (noselect_rewrite_rules_proofs bitwidth).
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterNoSelect.
      Let optsT := Eval hnf in optsT VerifiedRewriterNoSelect.

      Definition RewriteNoSelect (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterNoSelect opts t.

      Lemma Wf_RewriteNoSelect opts {t} e (Hwf : Wf e) : Wf (@RewriteNoSelect opts t e).
      Proof. now apply VerifiedRewriterNoSelect. Qed.

      Lemma Interp_RewriteNoSelect opts {t} e (Hwf : Wf e) : API.Interp (@RewriteNoSelect opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterNoSelect. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteNoSelect : wf wf_extra.
    Hint Opaque RewriteNoSelect : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteNoSelect : interp interp_extra.
  End Hints.
End Compilers.
