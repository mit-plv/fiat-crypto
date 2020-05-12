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
      Definition VerifiedRewriterAddAssocLeft : VerifiedRewriter_with_args false false true add_assoc_left_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterAddAssocLeft.
      Let optsT := Eval hnf in optsT VerifiedRewriterAddAssocLeft.

      Definition RewriteAddAssocLeft (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterAddAssocLeft opts t.

      Lemma Wf_RewriteAddAssocLeft opts {t} e (Hwf : Wf e) : Wf (@RewriteAddAssocLeft opts t e).
      Proof. now apply VerifiedRewriterAddAssocLeft. Qed.

      Lemma Interp_RewriteAddAssocLeft opts {t} e (Hwf : Wf e) : API.Interp (@RewriteAddAssocLeft opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterAddAssocLeft. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteAddAssocLeft : wf wf_extra.
    Hint Opaque RewriteAddAssocLeft : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteAddAssocLeft : interp interp_extra.
  End Hints.
End Compilers.
