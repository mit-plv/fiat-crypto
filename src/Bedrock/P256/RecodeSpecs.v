Require Import Lists.List.
From coqutil Require Import
  Byte
  Word.LittleEndianList.

From bedrock2 Require Import
  NotationsCustomEntry
  WeakestPrecondition
  ProgramLogic
  Syntax
  BasicC64Semantics.

Import BinInt String ListNotations.
Import ProgramLogic.Coercions.

#[local] Open Scope string_scope.
#[local] Open Scope Z_scope.
#[local] Open Scope list_scope.

(* TODO replace with a context to verify both architectures. *)
#[local] Notation width := 64.

Definition ctime_ltu :=
  func! (a, b) ~> r {
    unpack! _d, r = br_full_sub(a, b, $0);
    unpack! r = br_value_barrier(r)
  }.

(* Limb size (nonzero). *)
#[local] Notation w := 5.

Definition extract_limb_at_bit :=
  func! (p_input, total_bits, i) ~> r {
    idx = i >> $3; (* index = i/8 *)
    a = load1(p_input + idx);
    b = $0;
    if idx + $1 < (total_bits + $7) >> $3 {
      b = load1(p_input + idx + $1)
    };
    s = a + (b << $8);
    t = s >> (i & $7); (* offset = i%8 *)
    r = t & (($1 << $w) - $1)
  }.

Definition decompose_to_limbs :=
  func! (p_output, p_input, total_bits) {
    i = $0;
    while i < total_bits {
      unpack! r = extract_limb_at_bit(p_input, total_bits, i);
      store1(p_output, r); p_output = p_output + $1;
      i = i + $w;
      $(cmd.unset "r")
    }
  }.

Definition signed_recode_carry :=
  func! (p_limbs, ci, n) ~> ci {
      while n {
        x = load1(p_limbs) + ci;
        unpack! ci = ctime_ltu($(2^(w - 1)), x);
        unpack! x = br_cmov(ci, x - $(2^w), x);
        store1(p_limbs, x); p_limbs = p_limbs + $1;
        n = n - $1;
        $(cmd.unset "x")
      }
    }.

Definition signed_recode :=
  func! (p_limbs, n) {
    unpack! _c = signed_recode_carry(p_limbs, $0, n)
  }.

Section WithBase.
Context (B : Z).
Definition positional := fold_right (fun a s => a + (B)*s) 0.

Lemma positional_nil :
  positional nil = 0.
Proof. reflexivity. Qed.

Lemma positional_cons h t :
  positional (h :: t) = h + B*(positional t).
Proof. reflexivity. Qed.

Definition positional_bytes l :=
  positional (map byte.unsigned l).

Definition positional_signed_bytes l :=
  positional (map byte.signed l).

Lemma positional_bytes_cons h t :
  positional_bytes (h :: t) = byte.unsigned h + B*(positional_bytes t).
Proof. constructor. Qed.
End WithBase.

#[local] Notation bytearray := (Array.array ptsto (word.of_Z 1)).

#[export] Instance spec_of_ctime_ltu : spec_of "ctime_ltu" :=
  fnspec! "ctime_ltu" a b ~> r,
  { requires t m := True;
    ensures T M :=
      M = m /\ T = t /\
      word.unsigned r < 2 /\
      r = if word.ltu a b then word.of_Z 1 else word.of_Z 0
  }.

#[export] Instance spec_of_extract_limb_at_bit : spec_of "extract_limb_at_bit" :=
  fnspec! "extract_limb_at_bit" (p_input total_bits i : word) / input ~> r,
    { requires t m :=
        m =*> bytearray p_input input /\
        8 * (length input - 1) < total_bits <= 8 * length input /\
        le_combine input < 2^total_bits /\
        i < total_bits /\
        total_bits + 7 < 2^width;
      ensures T M :=
        M = m /\
        T = t /\
        r = le_combine input / 2^i mod 2^w :>Z
    }.

#[export] Instance spec_of_decompose_to_limbs : spec_of "decompose_to_limbs" :=
  fnspec! "decompose_to_limbs" (p_output p_input total_bits : word) / output input R,
    { requires t m :=
        m =* bytearray p_output output * bytearray p_input input * R /\
        8 * (length input - 1) < total_bits <= 8 * length input /\
        w * (length output - 1) < total_bits <= w * length output /\
        le_combine input < 2^total_bits /\
        total_bits + 7 < 2^width;
      ensures T M := exists OUTPUT,
        M =* bytearray p_output OUTPUT * bytearray p_input input * R /\
        length output = length OUTPUT /\
        T = t /\
        Forall (fun b => (0 <= byte.unsigned b < 2^w)) OUTPUT /\
        positional_bytes (2^w) OUTPUT = le_combine input
    }.

#[export] Instance spec_of_signed_recode_carry : spec_of "signed_recode_carry" :=
  fnspec! "signed_recode_carry" (p_limbs ci n : word) / limbs R ~> CO,
    { requires t m :=
        m =* bytearray p_limbs limbs * R /\ length limbs = word.unsigned n :>Z /\
        Forall (fun b => (0 <= byte.unsigned b < 2^w)) limbs /\
        0 <= ci <= 1;
      ensures T M := exists LIMBS,
        M =* bytearray p_limbs LIMBS * R /\ length LIMBS = word.unsigned n :>Z /\
        T = t /\
        positional_signed_bytes (2^w) LIMBS + 2^(w*n)*CO = word.unsigned ci + positional_bytes (2^w) limbs /\
        Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) LIMBS /\
        0 <= CO <= 1
    }.

#[export] Instance spec_of_signed_recode : spec_of "signed_recode" :=
  fnspec! "signed_recode" (p_limbs n : word) / limbs R,
  { requires t m :=
      m =* bytearray p_limbs limbs * R /\ length limbs = word.unsigned n :>Z /\
      Forall (fun b => (0 <= byte.unsigned b < 2^w)) limbs /\
      2 * (positional_bytes (2^w) limbs) < 2^(w*n) /\
      -2^(w*n) <= positional (2^w) (repeat (-2^w + 2) (Z.to_nat n));
    ensures T M := exists LIMBS,
      M =* bytearray p_limbs LIMBS * R /\ length LIMBS = word.unsigned n :>Z /\
      T = t /\
      positional_signed_bytes (2^w) LIMBS = positional_bytes (2^w) limbs /\
      Forall (fun b => (-2^w + 2 <= 2*(byte.signed b) <= 2^w)) LIMBS
  }.
