Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.

Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Testbit.

Require Import Crypto.Util.ZUtil.Tactics.SolveTestbit.

Local Open Scope Z_scope.

Module Z.
  Lemma ones_from_spec m k i
        (Hk : 0 <= k) :
    Z.testbit (Z.ones_from m k) i = if (i <? 0) then false else ((m - k) <=? i) && (i <? m).
  Proof. unfold Z.ones_from; Z.solve_testbit. Qed.

  Lemma ones_from_spec_full m k i :
    Z.testbit (Z.ones_from m k) i = if (i <? 0) then false else ((m - k) <=? i) && ((i <? m) || (k <? 0)).
  Proof. unfold Z.ones_from; Z.solve_testbit. Qed.

  Hint Rewrite ones_from_spec : testbit_rewrite.

  Lemma ones_from_0 m : Z.ones_from m 0 = 0.
  Proof. Z.solve_using_testbit. Qed.
End Z.
