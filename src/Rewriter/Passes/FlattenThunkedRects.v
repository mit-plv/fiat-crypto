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
      Definition VerifiedRewriterFlattenThunkedRects : VerifiedRewriter_with_args false false true flatten_thunked_rects_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterFlattenThunkedRects.
      Let optsT := Eval hnf in optsT VerifiedRewriterFlattenThunkedRects.

      Definition RewriteFlattenThunkedRects (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterFlattenThunkedRects opts t.

      Lemma Wf_RewriteFlattenThunkedRects opts {t} e (Hwf : Wf e) : Wf (@RewriteFlattenThunkedRects opts t e).
      Proof. now apply VerifiedRewriterFlattenThunkedRects. Qed.

      Lemma Interp_RewriteFlattenThunkedRects opts {t} e (Hwf : Wf e) : expr.Interp (@Compilers.ident_interp) (@RewriteFlattenThunkedRects opts t e) == expr.Interp (@Compilers.ident_interp) e.
      Proof. now apply VerifiedRewriterFlattenThunkedRects. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteFlattenThunkedRects : wf wf_extra.
    Hint Opaque RewriteFlattenThunkedRects : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteFlattenThunkedRects : interp interp_extra.
  End Hints.
End Compilers.
