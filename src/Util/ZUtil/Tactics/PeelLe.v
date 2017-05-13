Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Hints.Core.

Local Open Scope Z.

Module Z.
  Ltac peel_le_step :=
    match goal with
    | [ |- ?x + _ <= ?x + _ ]
      => apply Z.add_le_mono_l
    | [ |- _ + ?x <= _ + ?x ]
      => apply Z.add_le_mono_r
    | [ |- ?x - _ <= ?x - _ ]
      => apply Z.sub_le_mono_l
    | [ |- _ - ?x <= _ - ?x ]
      => apply Z.sub_le_mono_r
    | [ |- ?x^_ <= ?x^_ ]
      => apply Z.pow_le_mono_r; [ zutil_arith | ]
    | [ |- _^?x <= _^?x ]
      => apply Z.pow_le_mono_l; split; [ zutil_arith | ]
    | [ |- Z.log2_up _ <= Z.log2_up _ ]
      => apply Z.log2_up_le_mono
    | [ |- Z.log2 _ <= Z.log2 _ ]
      => apply Z.log2_le_mono
    | [ |- Z.succ _ <= Z.succ _ ]
      => apply Zsucc_le_compat
    | [ |- Z.pred _ <= Z.pred _ ]
      => apply Z.pred_le_mono
    | [ |- ?x * _ <= ?x * _ ]
      => first [ apply Z.mul_le_mono_nonneg_l; [ zutil_arith | ]
               | apply Z.mul_le_mono_nonpos_l; [ zutil_arith | ] ]
    | [ |- _ * ?x <= _ * ?x ]
      => first [ apply Z.mul_le_mono_nonneg_r; [ zutil_arith | ]
               | apply Z.mul_le_mono_nonpos_r; [ zutil_arith | ] ]
    | [ |- -_ <= -_ ]
      => apply Z.opp_le_mono
    | [ |- _ / ?x <= _ / ?x ]
      => apply Z.div_le_mono; [ zutil_arith | ]
    | [ |- ?x / _ <= ?x / _ ]
      => apply Z.div_le_compat_l; [ zutil_arith | split; [ zutil_arith | ] ]
    | [ |- Z.quot _ ?x <= Z.quot _ ?x ]
      => apply Z.quot_le_mono; [ zutil_arith | ]
    | [ |- Z.quot ?x _ <= Z.quot ?x _ ]
      => apply Z.quot_le_compat_l; [ zutil_arith | split; [ zutil_arith | ] ]
    | [ |- Z.max ?x _ <= Z.max ?x _ ]
      => apply Z.max_le_compat_l
    | [ |- Z.max _ ?x <= Z.max _ ?x ]
      => apply Z.max_le_compat_r
    | [ |- Z.min ?x _ <= Z.min ?x _ ]
      => apply Z.min_le_compat_l
    | [ |- Z.min _ ?x <= Z.min _ ?x ]
      => apply Z.min_le_compat_r
    end.
  Ltac peel_le := repeat peel_le_step.
End Z.
