Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.ZSimplify.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Simple.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Local Open Scope Z_scope.

Module Z.
  Lemma rshi_correct_full : forall s a b n,
    Z.rshi s a b n = if (0 <=? n)
                     then ((b + a * s) / 2 ^ n) mod s
                     else ((b + a * s) * 2 ^ (-n)) mod s.
  Proof.
    cbv [Z.rshi]; intros. pose proof (Z.log2_nonneg s).
    destruct (Decidable.dec (0 <= n)), (Z_zerop s); subst;
      break_match;
      now repeat match goal with
             | H : _ = s |- _ => rewrite H
             | _ => rewrite Z.land_ones by auto with zarith
             | _ => progress Z.ltb_to_lt
             | _ => progress autorewrite with Zshift_to_pow push_Zpow zsimplify_const
             | _ => reflexivity
             | _ => lia
             end.
  Qed.

  Lemma rshi_correct_full_alt : forall s a b n,
    Z.rshi s a b n = if (0 <=? n)
                     then ((b + a * s) / 2 ^ n) mod s
                     else (b * 2 ^ (-n)) mod s.
  Proof. intros; rewrite rshi_correct_full; push_Zmod; pull_Zmod; autorewrite with zsimplify_const; reflexivity. Qed.

  Lemma rshi_correct : forall s a b n, 0 <= n -> s <> 0 ->
                                  Z.rshi s a b n = ((b + a * s) / 2 ^ n) mod s.
  Proof. intros; rewrite rshi_correct_full; break_match; Z.ltb_to_lt; lia. Qed.

  Lemma rshi_small s a b n :
    (0 <= b < s) ->
    (0 <= a < 2^ n) ->
    (0 <= n) ->
    Z.rshi s a b n = ((b + a * s) / 2 ^ n).
  Proof.
    intros.
    rewrite Z.rshi_correct by auto with zarith.
    apply Z.mod_small.
    Z.div_mod_to_quot_rem; nia.
  Qed.

End Z.
