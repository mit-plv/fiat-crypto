From Coq Require Import ZArith.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.LetIn.
Local Open Scope Z_scope.

Module Z.
  Definition divideb (x y : Z) : bool
    := if x =? 0
       then y =? 0
       else y mod x =? 0.

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

  Definition add_split (s x y : Z) : Z * Z
    := dlet sum := Z.add x y in (sum mod s, sum / s).

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

  Definition mul_high (s x y : Z) : Z
    := snd (mul_split s x y).

  (** returns [1] iff [x < y] *)
  Definition ltz (x y : Z) : Z
    := if x <? y then 1 else 0.

  Definition combine_at_bitwidth (bitwidth lo hi : Z) : Z
    := lo + (hi << bitwidth).

  (** if positive, round up to 2^k-1 (0b11111....); if negative, round down to -2^k (0b...111000000...) *)
  Definition round_lor_land_bound (x : Z) : Z
    := if (0 <=? x)%Z
       then 2^(Z.log2_up (x+1))-1
       else -2^(Z.log2_up (-x)).

  Fixpoint log10_fuel (fuel : nat) (v : Z) :=
    match fuel with
    | O => 0
    | S fuel
      => if v >? 1
         then 1 + log10_fuel fuel (v / 10)
         else 0
    end.
  Definition log10 (v : Z) : Z := log10_fuel (Z.to_nat (Z.log2 v)) v.

  (** Special identity function for constant-time cmov *)
  Definition value_barrier (x : Z) := x.

  (* arithmetic right shift *)
  Definition arithmetic_shiftr1 (m a : Z) :=
    (a &' 2^(m - 1)) |' (a >> 1).

  Definition sign_bit m a := a >> (m - 1).

  Definition ones_from m k := (Z.ones k) << (m - k).
  Definition ones_at m k := (Z.ones k) << m.

  Definition sign_extend old_m new_m a :=
    dlet q := Z.zselect (sign_bit old_m a) 0 (ones_at old_m (new_m - old_m)) in
          q |' a.

  Definition arithmetic_shiftr m a k :=
    dlet q := Z.zselect (sign_bit m a) 0 (ones_from m k) in
          q |' (a >> k).

  (** Note that the following definition may be inconvenient to reason about,
      and [(a + 2^(m-1)) mod 2^m - 2^(m-1)] may prove simpler to reason about arithmetically.
      See also https://github.com/mit-plv/coqutil/blob/c8006ceca816076b117c31d7feaefb5bbb850754/src/coqutil/Word/Naive.v#L15
      and https://github.com/mit-plv/coqutil/blob/c8006ceca816076b117c31d7feaefb5bbb850754/src/coqutil/Word/Properties.v#L190 *)

  Definition twos_complement m a :=
    (if ((a mod 2 ^ m) <? 2 ^ (m - 1)) then a mod 2 ^ m else a mod 2 ^ m - 2 ^ m).

  (* Negation in twos complement *)
  Definition twos_complement_opp m a :=
    ((Z.lnot_modulo a (2 ^ m)) + 1) mod (2 ^ m).

  (* Check if a number considered in twos complement of bitwidth m is negative *)
  Definition twos_complement_neg m a := a >> (m - 1).

  (* note the corner case condition: when f is exactly 2 to the mw-1'th power, then -f = f and
   so checking that -f is negative does not work in that case.
   This is not really an issue, since it just requires that our integers are small (which they are)
   Long term, we would like to add comparison operators to the supported C language *)
  Definition twos_complement_pos m a :=
    dlet b := twos_complement_opp m a in sign_bit m b.

  Definition twos_complement_mul ma mb a b :=
    (sign_extend ma (ma + mb) a) * (sign_extend mb (ma + mb) b).

  Definition signed (s : N) (n : Z) : Z :=
    Z.land (Z.shiftl 1 (Z.of_N s-1) + n) (Z.ones (Z.of_N s)) - Z.shiftl 1 (Z.of_N s-1).
End Z.

Module Export Notations.
  Notation "( x | ? y )" := (Z.divideb x y) : Z_scope.
End Notations.
