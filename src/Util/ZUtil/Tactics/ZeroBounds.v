Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.PrimeBound.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Le.
Local Open Scope Z_scope.

Module Z.
  (* prove that combinations of known positive/nonnegative numbers are positive/nonnegative *)
  Ltac zero_bounds'' :=
    repeat match goal with
    | [ |- 0 <= _ + _] => apply Z.add_nonneg_nonneg
    | [ |- 0 <= _ - _] => apply Z.le_0_sub
    | [ |- 0 <= _ * _] => apply Z.mul_nonneg_nonneg
    | [ |- 0 <= _ / _] => apply Z.div_nonneg
    | [ |- 0 <= _ ^ _ ] => apply Z.pow_nonneg
    | [ |- 0 <= Z.shiftl _ _] => apply Z.shiftl_nonneg
    | [ |- 0 <= Z.shiftr _ _] => apply Z.shiftr_nonneg
    | [ |- 0 <= _ mod _] => apply Z.mod_pos_bound
    | [ |- 0 <= Z.land _ _] => apply Z.land_nonneg;
                               first [ left; solve [zero_bounds'']
                                     | right; solve [zero_bounds'']]
    | [ |- 0 <= Z.lor _ _] => apply Z.lor_nonneg; split; zero_bounds''
    | [ |- 0 < _ + _] => try solve [apply Z.add_pos_nonneg; zero_bounds''];
                         try solve [apply Z.add_nonneg_pos; zero_bounds'']
    | [ |- 0 < _ - _] => apply Z.lt_0_sub
    | [ |- 0 < _ * _] => apply Z.lt_0_mul; left; split
    | [ |- 0 < _ / _] => apply Z.div_str_pos
    | [ |- 0 < _ ^ _ ] => apply Z.pow_pos_nonneg
    end; try lia; try Z.prime_bound; auto.

  Ltac zero_bounds' :=
    repeat match goal with
           | |- ?a <> 0 => apply Z.positive_is_nonzero
           | |- ?a > 0 => apply Z.lt_gt
           | |- ?a >= 0 => apply Z.le_ge
           end;
    try match goal with
        | |- 0 < ?a => zero_bounds''
        | |- 0 <= ?a => zero_bounds''
        end.

  Ltac zero_bounds := try lia; try Z.prime_bound; zero_bounds'.

  Hint Extern 1 => progress zero_bounds : zero_bounds.
End Z.
