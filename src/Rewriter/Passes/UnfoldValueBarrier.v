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
      Definition VerifiedRewriterUnfoldValueBarrier : VerifiedRewriter_with_args false false true unfold_value_barrier_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterUnfoldValueBarrier.
      Let optsT := Eval hnf in optsT VerifiedRewriterUnfoldValueBarrier.

      Definition RewriteUnfoldValueBarrier (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterUnfoldValueBarrier opts t.

      Lemma Wf_RewriteUnfoldValueBarrier opts {t} e (Hwf : Wf e) : Wf (@RewriteUnfoldValueBarrier opts t e).
      Proof. now apply VerifiedRewriterUnfoldValueBarrier. Qed.

      Lemma Interp_RewriteUnfoldValueBarrier opts {t} e (Hwf : Wf e) : API.Interp (@RewriteUnfoldValueBarrier opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterUnfoldValueBarrier. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteUnfoldValueBarrier : wf wf_extra.
    Hint Opaque RewriteUnfoldValueBarrier : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteUnfoldValueBarrier : interp interp_extra.
  End Hints.
End Compilers.
