Require Import Coq.ZArith.ZArith.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.Rewriter.AllTacticsExtra.
Require Import Crypto.Rewriter.RulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.Wf.Compilers.
  Import Identifier.Compilers.
  Import Language.WfExtra.Compilers.
  Import Rewriter.AllTactics.Compilers.RewriteRules.GoalType.
  Import Rewriter.AllTacticsExtra.Compilers.RewriteRules.Tactic.
  Import Compilers.Classes.

  Module Import RewriteRules.
    Section __.
      Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
              (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
              (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2)).

      Definition VerifiedRewriterToFancy : VerifiedRewriter.
      Proof using All. make_rewriter false fancy_rewrite_rules_proofs. Defined.

      Definition RewriteToFancy {t} : Expr (ident:=ident) t -> Expr (ident:=ident) t.
      Proof using invert_low invert_high.
        let v := (eval hnf in (@Rewrite VerifiedRewriterToFancy t)) in exact v.
      Defined.

      Lemma Wf_RewriteToFancy {t} e (Hwf : Wf e) : Wf (@RewriteToFancy t e).
      Proof using All. now apply VerifiedRewriterToFancy. Qed.

      Lemma Interp_gen_RewriteToFancy {cast_outside_of_range t} e (Hwf : Wf e)
        : expr.Interp (@ident.gen_interp cast_outside_of_range) (@RewriteToFancy t e)
          == expr.Interp (@ident.gen_interp cast_outside_of_range) e.
      Proof using All. now apply VerifiedRewriterToFancy. Qed.

      Lemma Interp_RewriteToFancy {t} e (Hwf : Wf e) : expr.Interp (@ident.interp) (@RewriteToFancy t e) == expr.Interp (@ident.interp) e.
      Proof using All. apply Interp_gen_RewriteToFancy; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteToFancy : wf wf_extra.
    Hint Rewrite @Interp_gen_RewriteToFancy @Interp_RewriteToFancy : interp interp_extra.
  End Hints.
End Compilers.
