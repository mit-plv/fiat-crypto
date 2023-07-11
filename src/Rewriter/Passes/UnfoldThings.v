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
      Definition VerifiedRewriterUnfoldThings : VerifiedRewriter_with_args false false true unfold_things_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterUnfoldThings.
      Let optsT := Eval hnf in optsT VerifiedRewriterUnfoldThings.

      Definition RewriteUnfoldThings (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterUnfoldThings opts t.

      Lemma Wf_RewriteUnfoldThings opts {t} e (Hwf : Wf e) : Wf (@RewriteUnfoldThings opts t e).
      Proof. now apply VerifiedRewriterUnfoldThings. Qed.

      Lemma Interp_RewriteUnfoldThings opts {t} e (Hwf : Wf e) : API.Interp (@RewriteUnfoldThings opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterUnfoldThings. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
#[global]
    Hint Resolve Wf_RewriteUnfoldThings : wf wf_extra.
#[global]
    Hint Opaque RewriteUnfoldThings : wf wf_extra interp interp_extra rewrite.
#[global]
    Hint Rewrite @Interp_RewriteUnfoldThings : interp interp_extra.
  End Hints.
End Compilers.
