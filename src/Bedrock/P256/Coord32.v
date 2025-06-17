Require Import Bedrock.P256.Specs.
Require Import Bedrock.P256.Platform.
Import bedrock2.NotationsCustomEntry Specs.NotationsCustomEntry.

(* duplicated from shrd.v, edited to shift by 32 *)
Definition shrd :=
  func! (lo, hi, n) ~> (res) {
      res = lo >> n;
      if n {
        res = hi << ($32 - n) | res
      }
    }.

Definition p256_coord_nonzero := func! (p_x) ~> nz {
  nz = load(p_x) | load(p_x.+$4) | load(p_x.+$4.+$4) | load(p_x.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4.+$4.+$4);
  nz = nz | load(p_x.+$4.+$4.+$4.+$4.+$4.+$4.+$4);
  unpack! nz = br_broadcast_nonzero(nz)
}.

(*
Definition p256_coord_sub := func!(out, x, y) {
  unpack! t0, borrow = full_sub(load(x),          load(y),          $0);
  unpack! t1, borrow = full_sub(load(x+$4),       load(y+$4),       borrow);
  unpack! t2, borrow = full_sub(load(x+$4+$4),    load(y+$4+$4),    borrow);
  unpack! t3, borrow = full_sub(load(x+$4+$4+$4), load(y+$4+$4+$4), borrow);
  unpack! t4, borrow = full_sub(load(x+$4+$4+$4+$4), load(y+$4+$4+$4+$4), borrow);
  unpack! t5, borrow = full_sub(load(x+$4+$4+$4+$4+$4), load(y+$4+$4+$4+$4+$4), borrow);
  unpack! t6, borrow = full_sub(load(x+$4+$4+$4+$4+$4+$4), load(y+$4+$4+$4+$4+$4+$4), borrow);
  unpack! t7, borrow = full_sub(load(x+$4+$4+$4+$4+$4+$4+$4), load(y+$4+$4+$4+$4+$4+$4+$4), borrow);
  unpack! mask = br_value_barrier(-borrow);
  unpack! r0, carry = full_add(t0, mask,   $0);
  unpack! r1, carry = full_add(t1, mask,   carry);
  unpack! r2, carry = full_add(t2, mask,   carry);
  unpack! r3, carry = full_add(t3, $0,     carry);
  unpack! r4, carry = full_add(t4, $0,     carry);
  unpack! r5, carry = full_add(t5, $0,     carry);
  unpack! r6, carry = full_add(t6, borrow, carry);
  unpack! r7, carry = full_add(t7, mask,   carry);
  store(out,          r0);
  store(out+$4,       r1);
  store(out+$4+$4,    r2);
  store(out+$4+$4+$4, r3);
  store(out+$4+$4+$4+$4,          r4);
  store(out+$4+$4+$4+$4+$4,       r5);
  store(out+$4+$4+$4+$4+$4+$4,    r6);
  store(out+$4+$4+$4+$4+$4+$4+$4, r7)
}.
*)

Definition u256_shr := func!(p_out, p_x, n) {
  x0 = load(p_x);
  x1 = load(p_x+$4);
  x2 = load(p_x+$4+$4);
  x3 = load(p_x+$4+$4+$4);
  x4 = load(p_x+$4+$4+$4+$4);
  x5 = load(p_x+$4+$4+$4+$4+$4);
  x6 = load(p_x+$4+$4+$4+$4+$4+$4);
  x7 = load(p_x+$4+$4+$4+$4+$4+$4+$4);
  unpack! y0 = shrd(x0, x1, n);
  unpack! y1 = shrd(x1, x2, n);
  unpack! y2 = shrd(x2, x3, n);
  unpack! y3 = shrd(x3, x4, n);
  unpack! y4 = shrd(x4, x5, n);
  unpack! y5 = shrd(x5, x6, n);
  unpack! y6 = shrd(x6, x7, n);
  y7 = x6 >> n;
  store(p_out, y0);
  store(p_out+$4, y1);
  store(p_out+$4+$4, y2);
  store(p_out+$4+$4+$4, y3);
  store(p_out+$4+$4+$4+$4, y4);
  store(p_out+$4+$4+$4+$4+$4, y5);
  store(p_out+$4+$4+$4+$4+$4+$4, y6);
  store(p_out+$4+$4+$4+$4+$4+$4+$4, y7)
}.

Definition u256_set_p256_minushalf_conditional := func!(p_out, mask) {
  mh0 = -$1; mh1 = mh0; mh2 = mh0>>$1; mh3 = $0; mh4 = $0; mh5 = $1<<$31; mh6 = mh5; mh7 = mh2;
  store(p_out,          mask&mh0);
  store(p_out+$4,       mask&mh1);
  store(p_out+$4+$4,    mask&mh2);
  store(p_out+$4+$4+$4, mask&mh3);
  store(p_out+$4+$4+$4+$4,          mask&mh4);
  store(p_out+$4+$4+$4+$4+$4,       mask&mh6);
  store(p_out+$4+$4+$4+$4+$4+$4,    mask&mh7);
  store(p_out+$4+$4+$4+$4+$4+$4+$4, mask&mh8)
}.

Definition p256_coord_halve := func!(y, x) {
  stackalloc 32 as mmh;
  unpack! m = br_broadcast_odd(load(x));
  u256_set_p256_minushalf_conditional(mmh, m);
  u256_shr(y, x, $1);
  p256_coord_sub(y, y, mmh)
}.

(*
Definition p256_coord_add := func!(p_out, p_x, p_y) {
  unpack! t0, carry = full_add(load(p_x),          load(p_y),          $0);
  unpack! t1, carry = full_add(load(p_x+$8),       load(p_y+$8),       carry);
  unpack! t2, carry = full_add(load(p_x+$8+$8),    load(p_y+$8+$8),    carry);
  unpack! t3, carry = full_add(load(p_x+$8+$8+$8), load(p_y+$8+$8+$8), carry);
  unpack! r0, borrow = full_sub(t0, $0xffffffffffffffff, $0);
  unpack! r1, borrow = full_sub(t1, $0xffffffff,         borrow);
  unpack! r2, borrow = full_sub(t2, $0,                  borrow);
  unpack! r3, borrow = full_sub(t3, $0xffffffff00000001, borrow);
  unpack! r4, borrow = full_sub(carry, $0, borrow);
  unpack! r0 = br_cmov(borrow, t0, r0);
  unpack! r1 = br_cmov(borrow, t1, r1);
  unpack! r2 = br_cmov(borrow, t2, r2);
  unpack! r3 = br_cmov(borrow, t3, r3);
  store(p_out,          r0);
  store(p_out+$8,       r1);
  store(p_out+$8+$8,    r2);
  store(p_out+$8+$8+$8, r3)
}.
*)

Import String List bedrock2.ToCString Macros.WithBaseName.
Local Open Scope string_scope. Local Open Scope list_scope.

Definition coord32 := &[,
 br_broadcast_odd;
 shrd;
 p256_coord_nonzero;
 u256_shr;
 u256_set_p256_minushalf_conditional;
 p256_coord_halve
 ].

Compute String.concat LF (List.map c_func coord32).
