Require Import Coq.ZArith.ZArith Coq.omega.Omega.
Require Import Crypto.Util.ZUtil.Tactics.PrimeBound.
Require Import Crypto.Util.ZUtil.Div.
Local Open Scope Z_scope.

Module Z.
  (* prove that combinations of known positive/nonnegative numbers are positive/nonnegative *)
  Ltac zero_bounds' :=
    repeat match goal with
    | [ |- 0 <= _ + _] => apply Z.add_nonneg_nonneg
    | [ |- 0 <= _ - _] => apply Z.le_0_sub
    | [ |- 0 <= _ * _] => apply Z.mul_nonneg_nonneg
    | [ |- 0 <= _ / _] => apply Z.div_nonneg
    | [ |- 0 <= _ ^ _ ] => apply Z.pow_nonneg
    | [ |- 0 <= Z.shiftr _ _] => apply Z.shiftr_nonneg
    | [ |- 0 <= _ mod _] => apply Z.mod_pos_bound
    | [ |- 0 < _ + _] => try solve [apply Z.add_pos_nonneg; zero_bounds'];
                         try solve [apply Z.add_nonneg_pos; zero_bounds']
    | [ |- 0 < _ - _] => apply Z.lt_0_sub
    | [ |- 0 < _ * _] => apply Z.lt_0_mul; left; split
    | [ |- 0 < _ / _] => apply Z.div_str_pos
    | [ |- 0 < _ ^ _ ] => apply Z.pow_pos_nonneg
    end; try omega; try Z.prime_bound; auto.

  Ltac zero_bounds := try omega; try Z.prime_bound; zero_bounds'.

  Hint Extern 1 => progress zero_bounds : zero_bounds.
End Z.
