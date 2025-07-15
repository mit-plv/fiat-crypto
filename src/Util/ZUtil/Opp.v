From Coq Require Import ZArith.
From Coq Require Import Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
  Proof. lia. Qed.
#[global]
  Hint Rewrite opp_eq_0_iff : zsimplify.

  Lemma opp_sub n m : - n - m = - (n + m).
  Proof. lia. Qed.
End Z.
