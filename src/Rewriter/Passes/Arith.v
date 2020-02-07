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
      Context (max_const_val : Z).

      Definition VerifiedRewriterArith : VerifiedRewriter_with_args false false true (arith_rewrite_rules_proofs max_const_val).
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterArith.
      Let optsT := Eval hnf in optsT VerifiedRewriterArith.

      Definition RewriteArith (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterArith opts t.

      Lemma Wf_RewriteArith opts {t} e (Hwf : Wf e) : Wf (@RewriteArith opts t e).
      Proof. now apply VerifiedRewriterArith. Qed.

      Lemma Interp_RewriteArith opts {t} e (Hwf : Wf e) : API.Interp (@RewriteArith opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterArith. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteArith : wf wf_extra.
    Hint Opaque RewriteArith : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteArith : interp interp_extra.
  End Hints.
End Compilers.
