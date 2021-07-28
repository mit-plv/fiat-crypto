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
      Context (which_bitwidths : list Z).

      Definition VerifiedRewriterRelaxBitwidthAdcSbb : VerifiedRewriter_with_args false false true (relax_bitwidth_adc_sbb_rewrite_rules_proofs which_bitwidths).
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterRelaxBitwidthAdcSbb.
      Let optsT := Eval hnf in optsT VerifiedRewriterRelaxBitwidthAdcSbb.

      Definition RewriteRelaxBitwidthAdcSbb (opts : optsT) {t : API.type} := Eval hnf in @Rewrite VerifiedRewriterRelaxBitwidthAdcSbb opts t.

      Lemma Wf_RewriteRelaxBitwidthAdcSbb opts {t} e (Hwf : Wf e) : Wf (@RewriteRelaxBitwidthAdcSbb opts t e).
      Proof. now apply VerifiedRewriterRelaxBitwidthAdcSbb. Qed.

      Lemma Interp_RewriteRelaxBitwidthAdcSbb opts {t} e (Hwf : Wf e) : expr.Interp (@Compilers.ident_interp) (@RewriteRelaxBitwidthAdcSbb opts t e) == expr.Interp (@Compilers.ident_interp) e.
      Proof. now apply VerifiedRewriterRelaxBitwidthAdcSbb. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteRelaxBitwidthAdcSbb : wf wf_extra.
    Hint Opaque RewriteRelaxBitwidthAdcSbb : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteRelaxBitwidthAdcSbb : interp interp_extra.
  End Hints.
End Compilers.
