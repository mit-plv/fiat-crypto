Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.PullPush.
Local Open Scope Z_scope.

Module Z.
     Lemma rshi_correct : forall s a b n, 0 <= n -> s <> 0 ->
         Z.rshi s a b n = ((b + a * s) / 2 ^ n) mod s.
     Proof.
       cbv [Z.rshi]; intros. pose proof (Z.log2_nonneg s).
       break_match;
         repeat match goal with
              | H : _ = s |- _ => rewrite H
              | _ => rewrite Z.land_ones by auto with zarith
              | _ => progress autorewrite with Zshift_to_pow push_Zpow
              | _ => reflexivity
              end.
     Qed.
End Z.