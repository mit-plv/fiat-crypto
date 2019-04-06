Require Import Coq.ZArith.ZArith.
Require Import Crypto.RewriterFull.
Require Import Crypto.RewriterWf1.
Local Open Scope Z_scope.

Module Compilers.
  Import RewriterFull.Compilers.
  Import RewriterWf1.Compilers.

  Module Import RewriteRules.
    Import RewriterFull.Compilers.RewriteRules.
    Import RewriterWf1.Compilers.RewriteRules.WfTactics.GoalType.
    Import RewriterWf1.Compilers.RewriteRules.WfTactics.Tactic.

    Lemma RewriterRulesNBEWf : Wf_GoalT RewriterNBE.
    Proof. prove_good (). Qed.

    Lemma RewriterRulesArithWf max_const : Wf_GoalT (RewriterArith max_const).
    Proof. prove_good (). Qed.

    Lemma RewriterRulesArithWithCastsWf : Wf_GoalT RewriterArithWithCasts.
    Proof. prove_good (). Qed.

    Lemma RewriterRulesStripLiteralCastsWf : Wf_GoalT RewriterStripLiteralCasts.
    Proof. prove_good (). Qed.

    Lemma RewriterRulesToFancyWf
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
      : Wf_GoalT (RewriterToFancy invert_low invert_high).
    Proof. prove_good (). Qed.

    Lemma RewriterRulesToFancyWithCastsWf
          (invert_low invert_high : Z -> Z -> option Z)
          (value_range flag_range : ZRange.zrange)
          (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
          (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
      : Wf_GoalT (RewriterToFancyWithCasts invert_low invert_high value_range flag_range).
    Proof. prove_good (). Qed.
  End RewriteRules.
End Compilers.
