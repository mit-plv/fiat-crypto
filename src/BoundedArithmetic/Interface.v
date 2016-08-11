(*** Interface for bounded arithmetic *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Definition size := nat.

Local Coercion Z.of_nat : nat >-> Z.

Class ArchitectureBoundedOps (n : size) :=
  { BoundedType : Type (* [n]-bit word *);
    decode : BoundedType -> Z;
    encode : Z -> BoundedType;
    ShiftRight : forall a : size, BoundedType * BoundedType -> BoundedType;
    (** given [(high, low)], constructs [(high << (n - a)) + (low >>
          a)], i.e., shifts [high * 2ⁿ + low] down by [a] bits *)
    ShiftLeft : forall a : size, BoundedType -> BoundedType * BoundedType;
    (** given [x], constructs [(((x << a) / 2ⁿ) mod 2ⁿ, (x << a) mod
        2ⁿ], i.e., shifts [x] up by [a] bits, and takes the low [2n]
        bits of the result *)
    Mod2Pow : forall a : size, BoundedType -> BoundedType (* [mod 2ᵃ] *);
    CarryAdd : forall (carry : bool) (x y : BoundedType), bool * BoundedType;
    (** Ouputs [(x + y + if carry then 1 else 0) mod 2ⁿ], together
          with a boolean that's [true] if the sum is ≥ 2ⁿ, and [false]
          if there is no carry *)
    CarrySub : forall (carry : bool) (x y : BoundedType), bool * BoundedType;
  (** Ouputs [(x - y - if carry then 1 else 0) mod 2ⁿ], together
          with a boolean that's [true] if the sum is negative, and [false]
          if there is no borrow *) }.

Inductive BoundedHalfType {n} {ops : ArchitectureBoundedOps n} :=
| UpperHalf (_ : BoundedType)
| LowerHalf (_ : BoundedType).

Definition UnderlyingBounded {n} {ops : ArchitectureBoundedOps n} (x : BoundedHalfType)
  := match x with
     | UpperHalf v => v
     | LowerHalf v => v
     end.

Definition decode_half {n_over_two : size} {ops : ArchitectureBoundedOps (2 * n_over_two)%nat} (x : BoundedHalfType) : Z
  := match x with
     | UpperHalf v => decode v / 2^n_over_two
     | LowerHalf v => (decode v) mod 2^n_over_two
     end.

Class ArchitectureBoundedFullMulOps n {ops : ArchitectureBoundedOps n} :=
  { Mul : BoundedType -> BoundedType -> BoundedType * BoundedType
  (** Outputs [(high, low)] *) }.
Class ArchitectureBoundedHalfWidthMulOps n {ops : ArchitectureBoundedOps n} :=
  { HalfWidthMul : BoundedHalfType -> BoundedHalfType -> BoundedType }.

Class ArchitectureBoundedProperties {n} (ops : ArchitectureBoundedOps n) :=
  { bounded_valid : BoundedType -> Prop;
    decode_valid : forall v,
        bounded_valid v
        -> 0 <= decode v < 2^n;
    encode_valid : forall z,
        0 <= z < 2^n
        -> bounded_valid (encode z);
    encode_correct : forall z,
        0 <= z < 2^n
        -> decode (encode z) = z;
    ShiftRight_valid : forall a high_low,
        bounded_valid (fst high_low) -> bounded_valid (snd high_low)
        -> bounded_valid (ShiftRight a high_low);
    ShiftRight_correct : forall a high_low,
        bounded_valid (fst high_low) -> bounded_valid (snd high_low)
        -> decode (ShiftRight a high_low) = (decode (fst high_low) * 2^n + decode (snd high_low)) / 2^a;
    ShiftLeft_fst_valid : forall a v,
        bounded_valid v
        -> bounded_valid (fst (ShiftLeft a v));
    ShiftLeft_snd_valid : forall a v,
        bounded_valid v
        -> bounded_valid (snd (ShiftLeft a v));
    ShiftLeft_fst_correct : forall a v,
        bounded_valid v
        -> decode (fst (ShiftLeft a v)) = (decode v * 2^a) mod 2^n;
    ShiftLeft_snd_correct : forall a v,
        bounded_valid v
        -> decode (snd (ShiftLeft a v)) = ((decode v * 2^a) / 2^n) mod 2^n;
    Mod2Pow_valid : forall a v,
        bounded_valid v
        -> bounded_valid (Mod2Pow a v);
    Mod2Pow_correct : forall a v,
        bounded_valid v
        -> decode (Mod2Pow a v) = (decode v) mod 2^a;
    CarryAdd_valid : forall c x y,
        bounded_valid x -> bounded_valid y
        -> bounded_valid (snd (CarryAdd c x y));
    CarryAdd_fst_correct : forall c x y,
        bounded_valid x -> bounded_valid y
        -> fst (CarryAdd c x y) = (2^n <=? (decode x + decode y + if c then 1 else 0));
    CarryAdd_snd_correct : forall c x y,
        bounded_valid x -> bounded_valid y
        -> decode (snd (CarryAdd c x y)) = (decode x + decode y + if c then 1 else 0) mod 2^n;
    CarrySub_valid : forall c x y,
        bounded_valid x -> bounded_valid y
        -> bounded_valid (snd (CarrySub c x y));
    CarrySub_fst_correct : forall c x y,
        bounded_valid x -> bounded_valid y
        -> fst (CarrySub c x y) = ((decode x - decode y - if c then 1 else 0) <? 0);
    CarrySub_snd_correct : forall c x y,
        bounded_valid x -> bounded_valid y
        -> decode (snd (CarrySub c x y)) = (decode x - decode y - if c then 1 else 0) mod 2^n }.

Class ArchitectureBoundedFullMulProperties {n ops} (mops : @ArchitectureBoundedFullMulOps n ops) {props : ArchitectureBoundedProperties ops} :=
  { Mul_fst_valid : forall x y,
      bounded_valid x -> bounded_valid y
      -> bounded_valid (fst (Mul x y));
    Mul_snd_valid : forall x y,
        bounded_valid x -> bounded_valid y
        -> bounded_valid (snd (Mul x y));
    Mul_high_correct : forall x y,
        bounded_valid x -> bounded_valid y
        -> decode (fst (Mul x y)) = (decode x * decode y) / 2^n;
    Mul_low_correct : forall x y,
        bounded_valid x -> bounded_valid y
        -> decode (snd (Mul x y)) = (decode x * decode y) mod 2^n }.

Class ArchitectureBoundedHalfWidthMulProperties {n_over_two ops} (mops : @ArchitectureBoundedHalfWidthMulOps (2 * n_over_two)%nat ops) {props : ArchitectureBoundedProperties ops} :=
  { HalfWidthMul_valid : forall x y,
      bounded_valid (UnderlyingBounded x) -> bounded_valid (UnderlyingBounded y)
      -> bounded_valid (HalfWidthMul x y);
    HalfWidthMul_correct : forall x y,
        bounded_valid (UnderlyingBounded x) -> bounded_valid (UnderlyingBounded y)
        -> decode (HalfWidthMul x y) = (decode_half x * decode_half y)%Z }.
