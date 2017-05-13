Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Hints.Core.

Ltac Ztestbit_full_step :=
  match goal with
  | _ => progress autorewrite with Ztestbit_full
  | [ |- context[Z.testbit ?x ?y] ]
    => rewrite (Z.testbit_neg_r x y) by zutil_arith
  | [ |- context[Z.testbit ?x ?y] ]
    => rewrite (Z.bits_above_pow2 x y) by zutil_arith
  | [ |- context[Z.testbit ?x ?y] ]
    => rewrite (Z.bits_above_log2 x y) by zutil_arith
  end.
Ltac Ztestbit_full := repeat Ztestbit_full_step.

Ltac Ztestbit_step :=
  match goal with
  | _ => progress autorewrite with Ztestbit
  | _ => progress Ztestbit_full_step
  end.
Ltac Ztestbit := repeat Ztestbit_step.
