Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.LetIn.
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

  Definition get_borrow (bitwidth : Z) (v : Z) : Z * Z
    := let '(v, c) := get_carry bitwidth v in
       (v, -c).
  Definition sub_with_borrow (c : Z) (x y : Z) : Z
    := add_with_carry (-c) x (-y).
  Definition sub_with_get_borrow (bitwidth : Z) (c : Z) (x y : Z) : Z * Z
    := get_borrow bitwidth (sub_with_borrow c x y).
  Definition sub_get_borrow (bitwidth : Z) (x y : Z) : Z * Z
    := sub_with_get_borrow bitwidth 0 x y.

  (* splits at [bound], not [2^bitwidth]; wrapper to make add_getcarry
  work if input is not known to be a power of 2 *)
  Definition add_get_carry_full (bound : Z) (x y : Z) : Z * Z
    := if dec (2 ^ (Z.log2 bound) = bound)
       then add_get_carry (Z.log2 bound) x y
       else ((x + y) mod bound, (x + y) / bound).
  Definition add_with_get_carry_full (bound : Z) (c x y : Z) : Z * Z
    := if dec (2 ^ (Z.log2 bound) = bound)
       then add_with_get_carry (Z.log2 bound) c x y
       else ((c + x + y) mod bound, (c + x + y) / bound).
  Definition sub_get_borrow_full (bound : Z) (x y : Z) : Z * Z
    := if dec (2 ^ (Z.log2 bound) = bound)
       then sub_get_borrow (Z.log2 bound) x y
       else ((x - y) mod bound, -((x - y) / bound)).
  Definition sub_with_get_borrow_full (bound : Z) (c x y : Z) : Z * Z
    := if dec (2 ^ (Z.log2 bound) = bound)
       then sub_with_get_borrow (Z.log2 bound) c x y
       else ((x - y - c) mod bound, -((x - y - c) / bound)).

  Definition mul_split_at_bitwidth (bitwidth : Z) (x y : Z) : Z * Z
    := dlet xy := x * y in
        (match bitwidth with
         | Z.pos _ | Z0 => xy &' Z.ones bitwidth
         | Z.neg _ => xy mod 2^bitwidth
         end,
         match bitwidth with
         | Z.pos _ | Z0 => xy >> bitwidth
         | Z.neg _ => xy / 2^bitwidth
         end).
  Definition mul_split (s x y : Z) : Z * Z
    := if s =? 2^Z.log2 s
       then mul_split_at_bitwidth (Z.log2 s) x y
       else ((x * y) mod s, (x * y) / s).
End Z.
