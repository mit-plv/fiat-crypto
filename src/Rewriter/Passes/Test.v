Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.Rewriter.AllTacticsExtra.
Require Import Crypto.Rewriter.TestRulesProofs.

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
      (* Passing [true] as the second argument makes [make_rewriter] significantly faster by disabling early reduction; the trade-off is that rewriting later on is a bit slower. *)
      Definition VerifiedRewriterTest : VerifiedRewriter_with_args false true true test_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterTest.
      Let optsT := Eval hnf in optsT VerifiedRewriterTest.

      Definition RewriteTest (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterTest opts t.

      Lemma Wf_RewriteTest opts {t} e (Hwf : Wf e) : Wf (@RewriteTest opts t e).
      Proof. now apply VerifiedRewriterTest. Qed.

      Lemma Interp_RewriteTest opts {t} e (Hwf : Wf e) : API.Interp (@RewriteTest opts t e) == API.Interp e.
      Proof. now apply VerifiedRewriterTest. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteTest : wf wf_extra.
    Hint Opaque RewriteTest : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteTest : interp interp_extra.
  End Hints.
End Compilers.

Module Example.
  Import Coq.ZArith.ZArith.
  Import Compilers.RewriteRules.
  Import Crypto.Util.ZRange.
  Import Crypto.Language.PreExtra.
  Import Rewriter.Util.plugins.RewriterBuild.
  Local Notation cstZ r := (ident.cast (r%zrange)).
  Goal forall x y : Z, fst (x, y) = x.
  Proof.
    Rewrite_for VerifiedRewriterTest.
  Abort.
End Example.
