Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.LetIn.
Local Open Scope Z_scope.

Module Z.
  Definition pow2_mod n i := (n &' (Z.ones i)).

  Definition zselect (cond zero_case nonzero_case : Z) :=
    if cond =? 0 then zero_case else nonzero_case.

  Definition add_modulo x y modulus :=
    if (modulus <=? x + y) then (x + y) - modulus else (x + y).

  (** Logical negation, modulo a number *)
  Definition lnot_modulo (v : Z) (modulus : Z) : Z
    := Z.lnot v mod modulus.

  (** Boolean negation *)
  Definition bneg (v : Z) : Z
    := if dec (v = 0) then 1 else 0.

  (* most significant bit *)
  Definition cc_m s x := if dec (2 ^ (Z.log2 s) = s) then x >> (Z.log2 s - 1) else x / (s / 2).

  (* least significant bit *)
  Definition cc_l x := x mod 2.

  (* two-register right shift *)
  Definition rshi s hi lo n :=
       let k := Z.log2 s in
       if dec (2 ^ k = s)
       then ((lo + (hi << k)) >> n) &' (Z.ones k)
       else ((lo + hi * s) >> n) mod s.

  (** left-shift that truncates *)
  Definition truncating_shiftl bw x n := (x << n) mod (2^bw).

  Definition get_carry (bitwidth : Z) (v : Z) : Z * Z
    := (v mod 2^bitwidth, v / 2^bitwidth).
  Definition add_with_carry (c : Z) (x y : Z) : Z
    := c + x + y.
  Definition add_with_get_carry (bitwidth : Z) (c : Z) (x y : Z) : Z * Z
    := dlet v := add_with_carry c x y in get_carry bitwidth v.
  Definition add_get_carry (bitwidth : Z) (x y : Z) : Z * Z
    := add_with_get_carry bitwidth 0 x y.

  Definition get_borrow (bitwidth : Z) (v : Z) : Z * Z
    := let '(v, c) := get_carry bitwidth v in
       (v, -c).
  Definition sub_with_borrow (c : Z) (x y : Z) : Z
    := add_with_carry (-c) x (-y).
  Definition sub_with_get_borrow (bitwidth : Z) (c : Z) (x y : Z) : Z * Z
    := dlet v := sub_with_borrow c x y in get_borrow bitwidth v.
  Definition sub_get_borrow (bitwidth : Z) (x y : Z) : Z * Z
    := sub_with_get_borrow bitwidth 0 x y.

  (* splits at [bound], not [2^bitwidth]; wrapper to make add_getcarry
  work if input is not known to be a power of 2 *)
  Definition add_get_carry_full (bound : Z) (x y : Z) : Z * Z
    := if 2 ^ (Z.log2 bound) =? bound
       then add_get_carry (Z.log2 bound) x y
       else ((x + y) mod bound, (x + y) / bound).
  Definition add_with_get_carry_full (bound : Z) (c x y : Z) : Z * Z
    := if 2 ^ (Z.log2 bound) =? bound
       then add_with_get_carry (Z.log2 bound) c x y
       else ((c + x + y) mod bound, (c + x + y) / bound).
  Definition sub_get_borrow_full (bound : Z) (x y : Z) : Z * Z
    := if 2 ^ (Z.log2 bound) =? bound
       then sub_get_borrow (Z.log2 bound) x y
       else ((x - y) mod bound, -((x - y) / bound)).
  Definition sub_with_get_borrow_full (bound : Z) (c x y : Z) : Z * Z
    := if 2 ^ (Z.log2 bound) =? bound
       then sub_with_get_borrow (Z.log2 bound) c x y
       else ((x - y - c) mod bound, -((x - y - c) / bound)).

  Definition mul_split_at_bitwidth (bitwidth : Z) (x y : Z) : Z * Z
    := dlet xy := x * y in
       (if Z.geb bitwidth 0
        then xy &' Z.ones bitwidth
        else xy mod 2^bitwidth,
        if Z.geb bitwidth 0
        then xy >> bitwidth
        else xy / 2^bitwidth).
  Definition mul_split (s x y : Z) : Z * Z
    := if s =? 2^Z.log2 s
       then mul_split_at_bitwidth (Z.log2 s) x y
       else ((x * y) mod s, (x * y) / s).

  Definition combine_at_bitwidth (bitwidth lo hi : Z) : Z
    := lo + (hi << bitwidth).

  (** if positive, round up to 2^k-1 (0b11111....); if negative, round down to -2^k (0b...111000000...) *)
  Definition round_lor_land_bound (x : Z) : Z
    := if (0 <=? x)%Z
       then 2^(Z.log2_up (x+1))-1
       else -2^(Z.log2_up (-x)).
End Z.
