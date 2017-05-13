Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Notations.
Local Open Scope Z_scope.

Module Z.
  Definition pow2_mod n i := (n &' (Z.ones i)).

  Definition zselect (cond zero_case nonzero_case : Z) :=
    if cond =? 0 then zero_case else nonzero_case.

  Definition get_carry (bitwidth : Z) (v : Z) : Z * Z
    := (v mod 2^bitwidth, v / 2^bitwidth).
  Definition add_with_carry (c : Z) (x y : Z) : Z
    := c + x + y.
  Definition add_with_get_carry (bitwidth : Z) (c : Z) (x y : Z) : Z * Z
    := get_carry bitwidth (add_with_carry c x y).
  Definition add_get_carry (bitwidth : Z) (x y : Z) : Z * Z
    := add_with_get_carry bitwidth 0 x y.
End Z.
