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
      Context (bitwidth : Z)
              (lgcarrymax : Z).

      Definition VerifiedRewriterMultiRetSplit : VerifiedRewriter_with_args false false true (multiret_split_rewrite_rules_proofs bitwidth lgcarrymax).
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterMultiRetSplit.
      Let optsT := Eval hnf in optsT VerifiedRewriterMultiRetSplit.

      Definition RewriteMultiRetSplit (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterMultiRetSplit opts t.

      Lemma Wf_RewriteMultiRetSplit opts {t} e (Hwf : Wf e) : Wf (@RewriteMultiRetSplit opts t e).
      Proof. now apply VerifiedRewriterMultiRetSplit. Qed.

      Lemma Interp_RewriteMultiRetSplit opts {t} e (Hwf : Wf e) : API.Interp (@RewriteMultiRetSplit opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterMultiRetSplit. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteMultiRetSplit : wf wf_extra.
    Hint Opaque RewriteMultiRetSplit : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteMultiRetSplit : interp interp_extra.
  End Hints.
End Compilers.
