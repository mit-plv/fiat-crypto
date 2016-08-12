(*** Interface for bounded arithmetic *)
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.

Local Open Scope nat_scope.
Local Open Scope Z_scope.
Local Open Scope type_scope.

Definition size := nat.

Local Coercion Z.of_nat : nat >-> Z.

Section InstructionGallery.
  Context (n:Z) (* bit-width of width of W *)
          {W : Type}(* previously [BoundedType], [W] for word *)
          (decode : W -> Z).
  Local Notation imm := Z (only parsing). (* immediate (compile-time) argument *)

  Class is_load_immediate (ldi:imm->W) :=
    decode_load_immediate : forall x, 0 <= x < 2^n -> decode (ldi x) = x.

  Class is_shift_right_doubleword_immediate (shrd:W->W->imm->W) :=
    decode_shift_right_doubleword :
      forall high low count,
        0 <= count < n
        -> decode (shrd high low count) = (((decode high << n) + decode low) >> count) mod 2^n.

  Class is_shift_left_immediate (shl:W->imm->W) :=
    decode_shift_left_immediate :
      forall r count, 0 <= count < n -> decode (shl r count) = (decode r << count) mod 2^n.

  Class is_spread_left_immediate (sprl:W->imm->W*W(*high, low*)) :=
    {
      fst_spread_left_immediate : forall r count, 0 <= count < n ->
        decode (fst (sprl r count)) = (decode r << count) >> n;
      snd_spread_left_immediate : forall r count, 0 <= count < n ->
          decode (snd (sprl r count)) = (decode r << count) mod 2^n
    }.

  Class is_mask_keep_low (mkl:W->imm->W) :=
    decode_mask_keep_low : forall r count,
      0 <= count < n -> decode (mkl r count) = decode r mod 2^count.

  Local Notation bit b := (if b then 1 else 0).
  Class is_add_with_carry (adc:W->W->bool->bool*W) :=
    {
      fst_add_with_carry : forall x y c, bit (fst (adc x y c)) = (decode x + decode y + bit c) >> n;
      snd_add_with_carry : forall x y c, decode (snd (adc x y c)) = (decode x + decode y + bit c) mod (2^n)
    }.

  Class is_sub_with_carry (subc:W->W->bool->bool*W) :=
    {
    fst_sub_with_carry : forall x y c, fst (subc x y c) = ((decode x - decode y - bit c) <? 0);
    snd_sub_with_carry : forall x y c, decode (snd (subc x y c)) = (decode x - decode y - bit c) mod 2^n
    }.

  Class is_mul (mul:W->W->W) :=
    decode_mul : forall x y, decode (mul x y) = decode x * decode y mod 2^n.

  Class is_mul_low_low (w:Z) (mulhwll:W->W->W) :=
    decode_mul_low_low :
      forall x y, decode (mulhwll x y) = ((decode x mod 2^w) * (decode y mod 2^w)) mod 2^n.
  Class is_mul_high_low (w:Z) (mulhwhl:W->W->W) :=
    decode_mul_high_low :
      forall x y, decode (mulhwhl x y) = ((decode x >> w) * (decode y mod 2^w)) mod 2^n.
  Class is_mul_high_high (w:Z) (mulhwhh:W->W->W) :=
    decode_mul_high_high :
      forall x y, decode (mulhwhh x y) = ((decode x >> w) * (decode y >> w)) mod 2^n.
End InstructionGallery.

Module fancy_machine.
  Local Notation imm := Z (only parsing).
  Class instructions (n:Z) :=
    {
      W : Type (* [n]-bit word *);
      ldi : imm -> W;
      shrd : W->W->imm -> W;
      sprl : W->imm -> W*W;
      mkl : W->imm -> W;
      adc : W->W->bool -> bool*W;
      subc : W->W->bool -> bool*W
    }.

  Class arithmetic {n} (ops:instructions n) :=
    {
      decode : W -> Z;
      decode_range : forall x, 0 <= decode x < 2^n;
      load_immediate : is_load_immediate n decode ldi;
      shift_right_doubleword_immediate : is_shift_right_doubleword_immediate n decode shrd;
      spread_left_immediate : is_spread_left_immediate n decode sprl;
      mask_keep_low : is_mask_keep_low n decode mkl;
      add_with_carry : is_add_with_carry n decode adc;
      sub_with_carry : is_sub_with_carry n decode subc
    }.
  Global Existing Instance load_immediate.
  Global Existing Instance shift_right_doubleword_immediate.
  Global Existing Instance spread_left_immediate.
  Global Existing Instance mask_keep_low.
  Global Existing Instance add_with_carry.
  Global Existing Instance sub_with_carry.
End fancy_machine.