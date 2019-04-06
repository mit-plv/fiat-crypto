Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZRange.
Require Import Crypto.RewriterRules.
Require Import Crypto.Rewriter.
Local Open Scope Z_scope.

Import Compilers.RewriteRules.GoalType.
Import Compilers.RewriteRules.Tactic.

Module Compilers.
  Module RewriteRules.
    Definition RewriterNBE : RewriterT.
    Proof. make_Rewriter true nbe_rewrite_rulesT. Defined.

    Definition RewriterArith (max_const_val : Z) : RewriterT.
    Proof. make_Rewriter false (arith_rewrite_rulesT max_const_val). Defined.

    Definition RewriterArithWithCasts : RewriterT.
    Proof. make_Rewriter false arith_with_casts_rewrite_rulesT. Defined.

    Definition RewriterStripLiteralCasts : RewriterT.
    Proof. make_Rewriter false strip_literal_casts_rewrite_rulesT. Defined.

    Definition RewriterToFancy
               (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
      : RewriterT.
    Proof. make_Rewriter false fancy_rewrite_rulesT. Defined.

    Definition RewriterToFancyWithCasts
               (invert_low invert_high : Z (*log2wordmax*) -> Z -> @option Z)
               (value_range flag_range : zrange)
      : RewriterT.
    Proof. make_Rewriter false (fancy_with_casts_rewrite_rulesT invert_low invert_high value_range flag_range). Defined.

    Definition RewriteNBE {t} := Eval hnf in @Rewrite RewriterNBE t.
    Definition RewriteArith max_const_val {t} := Eval hnf in @Rewrite (RewriterArith max_const_val) t.
    Definition RewriteArithWithCasts {t} := Eval hnf in @Rewrite RewriterArithWithCasts t.
    Definition RewriteStripLiteralCasts {t} := Eval hnf in @Rewrite RewriterStripLiteralCasts t.
    Definition RewriteToFancy invert_low invert_high {t}
      := Eval hnf in @Rewrite (RewriterToFancy invert_low invert_high) t.
    Definition RewriteToFancyWithCasts invert_low invert_high value_range flag_range {t}
      := Eval hnf in @Rewrite (RewriterToFancyWithCasts invert_low invert_high value_range flag_range) t.
  End RewriteRules.

  Import Language.Compilers.defaults.

  Definition PartialEvaluate {t} (e : Expr t) : Expr t
    := RewriteRules.RewriteNBE e.
End Compilers.
