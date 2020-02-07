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
      Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
              (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
              (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2)).

      Definition VerifiedRewriterToFancy : VerifiedRewriter_with_args false false true fancy_rewrite_rules_proofs.
      Proof using All. make_rewriter. Defined.

      Definition default_opts := Eval hnf in @default_opts VerifiedRewriterToFancy.
      Let optsT := Eval hnf in optsT VerifiedRewriterToFancy.

      Definition RewriteToFancy (opts : optsT) {t : API.type} : API.Expr t -> API.Expr t.
      Proof using invert_low invert_high.
        let v := (eval hnf in (@Rewrite VerifiedRewriterToFancy opts t)) in exact v.
      Defined.

      Lemma Wf_RewriteToFancy opts {t} e (Hwf : Wf e) : Wf (@RewriteToFancy opts t e).
      Proof using All. now apply VerifiedRewriterToFancy. Qed.

      Lemma Interp_RewriteToFancy opts {t} e (Hwf : Wf e) : API.Interp (@RewriteToFancy opts t e) == API.Interp e.
      Proof using All. now apply VerifiedRewriterToFancy. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteToFancy : wf wf_extra.
    Hint Opaque RewriteToFancy : wf wf_extra interp interp_extra rewrite.
    Hint Rewrite @Interp_RewriteToFancy : interp interp_extra.
  End Hints.
End Compilers.
