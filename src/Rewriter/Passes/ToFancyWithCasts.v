Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.WfExtra.
Require Import Crypto.Rewriter.AllTacticsExtra.
Require Import Crypto.Rewriter.RulesProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.API.Compilers.
  Import Language.Wf.Compilers.
  Import Language.WfExtra.Compilers.
  Import Rewriter.AllTactics.Compilers.RewriteRules.GoalType.
  Import Rewriter.AllTacticsExtra.Compilers.RewriteRules.Tactic.
  Import Compilers.Classes.

  Module Import RewriteRules.
    Section __.
      Context (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
              (value_range flag_range : zrange)
              (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
              (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2)).

      Definition VerifiedRewriterToFancyWithCasts : VerifiedRewriter.
      Proof using All. make_rewriter false (@fancy_with_casts_rewrite_rules_proofs invert_low invert_high value_range flag_range Hlow Hhigh). Defined.

      Definition RewriteToFancyWithCasts {t} : API.Expr t -> API.Expr t.
      Proof using invert_low invert_high value_range flag_range.
        let v := (eval hnf in (@Rewrite VerifiedRewriterToFancyWithCasts t)) in exact v.
      Defined.

      Lemma Wf_RewriteToFancyWithCasts {t} e (Hwf : Wf e) : Wf (@RewriteToFancyWithCasts t e).
      Proof using All. now apply VerifiedRewriterToFancyWithCasts. Qed.

      Lemma Interp_gen_RewriteToFancyWithCasts {cast_outside_of_range t} e (Hwf : Wf e)
        : API.gen_Interp cast_outside_of_range (@RewriteToFancyWithCasts t e)
          == API.gen_Interp cast_outside_of_range e.
      Proof using All. now apply VerifiedRewriterToFancyWithCasts. Qed.

      Lemma Interp_RewriteToFancyWithCasts {t} e (Hwf : Wf e) : API.Interp (@RewriteToFancyWithCasts t e) == API.Interp e.
      Proof using All. apply Interp_gen_RewriteToFancyWithCasts; assumption. Qed.
    End __.
  End RewriteRules.

  Module Export Hints.
    Hint Resolve Wf_RewriteToFancyWithCasts : wf wf_extra.
    Hint Rewrite @Interp_gen_RewriteToFancyWithCasts @Interp_RewriteToFancyWithCasts : interp interp_extra.
  End Hints.
End Compilers.
