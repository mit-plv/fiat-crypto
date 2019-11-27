Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Import Crypto.Stringification.C.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import
  Language.Compilers
  Language.API.Compilers
  Stringification.C.Compilers.

Import Language.API.Compilers.API.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Existing Instance ToString.C.OutputCAPI.
Local Instance static : static_opt := true.
Local Instance : emit_primitives_opt := true.

Module debugging_remove_mul_split_to_C_uint1_carry.
  Section __.
    Context (n : nat := 5%nat)
            (s : Z := 2^255)
            (c : list (Z * Z) := [(1,19)])
            (machine_wordsize : Z := 64)
            (should_split_mul : should_split_mul_opt := true)
            (widen_carry : widen_carry_opt := true)
            (widen_bytes : widen_bytes_opt := false).

    Local Existing Instances should_split_mul widen_carry widen_bytes.

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

    Definition possible_values_of_machine_wordsize
      := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.

    Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.

    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.


    Let limbwidth_num := Eval vm_compute in Qnum limbwidth.
    Let limbwidth_den := Eval vm_compute in QDen limbwidth.

    Set Printing Depth 100000.
    Local Open Scope string_scope.
    Redirect "log" Compute
      Pipeline.BoundsPipelineToString
      "" (* prefix *)
      "mul"
      false (* subst01 *)
      None (* fancy *)
      possible_values
      ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n idxs)) in
            exact r)
             (fun _ _ => []) (* comment *)
             (Some loose_bounds, (Some loose_bounds, tt))
             (Some tight_bounds).
(* /*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 *   arg2: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
static void mul(uint64_t out1[5], const uint64_t arg1[5], const uint64_t arg2[5]) {
  uint64_t x1;
  uint64_t x2;
  mulx_u64(&x1, &x2, (arg1[4]), ((arg2[4]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x3;
  uint64_t x4;
  mulx_u64(&x3, &x4, (arg1[4]), ((arg2[3]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x5;
  uint64_t x6;
  mulx_u64(&x5, &x6, (arg1[4]), ((arg2[2]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x7;
  uint64_t x8;
  mulx_u64(&x7, &x8, (arg1[4]), ((arg2[1]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x9;
  uint64_t x10;
  mulx_u64(&x9, &x10, (arg1[3]), ((arg2[4]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x11;
  uint64_t x12;
  mulx_u64(&x11, &x12, (arg1[3]), ((arg2[3]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x13;
  uint64_t x14;
  mulx_u64(&x13, &x14, (arg1[3]), ((arg2[2]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x15;
  uint64_t x16;
  mulx_u64(&x15, &x16, (arg1[2]), ((arg2[4]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x17;
  uint64_t x18;
  mulx_u64(&x17, &x18, (arg1[2]), ((arg2[3]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x19;
  uint64_t x20;
  mulx_u64(&x19, &x20, (arg1[1]), ((arg2[4]) * (uint64_t)UINT8_C(0x13)));
  uint64_t x21;
  uint64_t x22;
  mulx_u64(&x21, &x22, (arg1[4]), (arg2[0]));
  uint64_t x23;
  uint64_t x24;
  mulx_u64(&x23, &x24, (arg1[3]), (arg2[1]));
  uint64_t x25;
  uint64_t x26;
  mulx_u64(&x25, &x26, (arg1[3]), (arg2[0]));
  uint64_t x27;
  uint64_t x28;
  mulx_u64(&x27, &x28, (arg1[2]), (arg2[2]));
  uint64_t x29;
  uint64_t x30;
  mulx_u64(&x29, &x30, (arg1[2]), (arg2[1]));
  uint64_t x31;
  uint64_t x32;
  mulx_u64(&x31, &x32, (arg1[2]), (arg2[0]));
  uint64_t x33;
  uint64_t x34;
  mulx_u64(&x33, &x34, (arg1[1]), (arg2[3]));
  uint64_t x35;
  uint64_t x36;
  mulx_u64(&x35, &x36, (arg1[1]), (arg2[2]));
  uint64_t x37;
  uint64_t x38;
  mulx_u64(&x37, &x38, (arg1[1]), (arg2[1]));
  uint64_t x39;
  uint64_t x40;
  mulx_u64(&x39, &x40, (arg1[1]), (arg2[0]));
  uint64_t x41;
  uint64_t x42;
  mulx_u64(&x41, &x42, (arg1[0]), (arg2[4]));
  uint64_t x43;
  uint64_t x44;
  mulx_u64(&x43, &x44, (arg1[0]), (arg2[3]));
  uint64_t x45;
  uint64_t x46;
  mulx_u64(&x45, &x46, (arg1[0]), (arg2[2]));
  uint64_t x47;
  uint64_t x48;
  mulx_u64(&x47, &x48, (arg1[0]), (arg2[1]));
  uint64_t x49;
  uint64_t x50;
  mulx_u64(&x49, &x50, (arg1[0]), (arg2[0]));
  uint64_t x51;
  uint1 x52;
  addcarryx_u64(&x51, &x52, 0x0, x13, x7);
  uint64_t x53;
  uint1 x54;
  addcarryx_u64(&x53, &x54, x52, x14, x8);
  uint64_t x55;
  uint1 x56;
  addcarryx_u64(&x55, &x56, 0x0, x17, x51);
  uint64_t x57;
  uint1 x58;
  addcarryx_u64(&x57, &x58, x56, x18, x53);
  uint64_t x59;
  uint1 x60;
  addcarryx_u64(&x59, &x60, 0x0, x19, x55);
  uint64_t x61;
  uint1 x62;
  addcarryx_u64(&x61, &x62, x60, x20, x57);
  uint64_t x63;
  uint1 x64;
  addcarryx_u64(&x63, &x64, 0x0, x49, x59);
  uint64_t x65;
  uint1 x66;
  addcarryx_u64(&x65, &x66, x64, x50, x61);
  uint64_t x67 = ((x63 >> 51) | ((x65 << 13) & UINT64_C(0xffffffffffffffff)));
  uint64_t x68 = (x63 & UINT64_C(0x7ffffffffffff));
  uint64_t x69;
  uint1 x70;
  addcarryx_u64(&x69, &x70, 0x0, x23, x21);
  uint64_t x71;
  uint1 x72;
  addcarryx_u64(&x71, &x72, x70, x24, x22);
  uint64_t x73;
  uint1 x74;
  addcarryx_u64(&x73, &x74, 0x0, x27, x69);
  uint64_t x75;
  uint1 x76;
  addcarryx_u64(&x75, &x76, x74, x28, x71);
  uint64_t x77;
  uint1 x78;
  addcarryx_u64(&x77, &x78, 0x0, x33, x73);
  uint64_t x79;
  uint1 x80;
  addcarryx_u64(&x79, &x80, x78, x34, x75);
  uint64_t x81;
  uint1 x82;
  addcarryx_u64(&x81, &x82, 0x0, x41, x77);
  uint64_t x83;
  uint1 x84;
  addcarryx_u64(&x83, &x84, x82, x42, x79);
  uint64_t x85;
  uint1 x86;
  addcarryx_u64(&x85, &x86, 0x0, x25, x1);
  uint64_t x87;
  uint1 x88;
  addcarryx_u64(&x87, &x88, x86, x26, x2);
  uint64_t x89;
  uint1 x90;
  addcarryx_u64(&x89, &x90, 0x0, x29, x85);
  uint64_t x91;
  uint1 x92;
  addcarryx_u64(&x91, &x92, x90, x30, x87);
  uint64_t x93;
  uint1 x94;
  addcarryx_u64(&x93, &x94, 0x0, x35, x89);
  uint64_t x95;
  uint1 x96;
  addcarryx_u64(&x95, &x96, x94, x36, x91);
  uint64_t x97;
  uint1 x98;
  addcarryx_u64(&x97, &x98, 0x0, x43, x93);
  uint64_t x99;
  uint1 x100;
  addcarryx_u64(&x99, &x100, x98, x44, x95);
  uint64_t x101;
  uint1 x102;
  addcarryx_u64(&x101, &x102, 0x0, x9, x3);
  uint64_t x103;
  uint1 x104;
  addcarryx_u64(&x103, &x104, x102, x10, x4);
  uint64_t x105;
  uint1 x106;
  addcarryx_u64(&x105, &x106, 0x0, x31, x101);
  uint64_t x107;
  uint1 x108;
  addcarryx_u64(&x107, &x108, x106, x32, x103);
  uint64_t x109;
  uint1 x110;
  addcarryx_u64(&x109, &x110, 0x0, x37, x105);
  uint64_t x111;
  uint1 x112;
  addcarryx_u64(&x111, &x112, x110, x38, x107);
  uint64_t x113;
  uint1 x114;
  addcarryx_u64(&x113, &x114, 0x0, x45, x109);
  uint64_t x115;
  uint1 x116;
  addcarryx_u64(&x115, &x116, x114, x46, x111);
  uint64_t x117;
  uint1 x118;
  addcarryx_u64(&x117, &x118, 0x0, x11, x5);
  uint64_t x119;
  uint1 x120;
  addcarryx_u64(&x119, &x120, x118, x12, x6);
  uint64_t x121;
  uint1 x122;
  addcarryx_u64(&x121, &x122, 0x0, x15, x117);
  uint64_t x123;
  uint1 x124;
  addcarryx_u64(&x123, &x124, x122, x16, x119);
  uint64_t x125;
  uint1 x126;
  addcarryx_u64(&x125, &x126, 0x0, x39, x121);
  uint64_t x127;
  uint1 x128;
  addcarryx_u64(&x127, &x128, x126, x40, x123);
  uint64_t x129;
  uint1 x130;
  addcarryx_u64(&x129, &x130, 0x0, x47, x125);
  uint64_t x131;
  uint1 x132;
  addcarryx_u64(&x131, &x132, x130, x48, x127);
  uint64_t x133;
  uint1 x134;
  addcarryx_u64(&x133, &x134, 0x0, x67, x129);
  uint64_t x135 = (x134 + x131);
  uint64_t x136 = ((x133 >> 51) | ((x135 << 13) & UINT64_C(0xffffffffffffffff)));
  uint64_t x137 = (x133 & UINT64_C(0x7ffffffffffff));
  uint64_t x138;
  uint1 x139;
  addcarryx_u64(&x138, &x139, 0x0, x136, x113);
  uint64_t x140 = (x139 + x115);
  uint64_t x141 = ((x138 >> 51) | ((x140 << 13) & UINT64_C(0xffffffffffffffff)));
  uint64_t x142 = (x138 & UINT64_C(0x7ffffffffffff));
  uint64_t x143;
  uint1 x144;
  addcarryx_u64(&x143, &x144, 0x0, x141, x97);
  uint64_t x145 = (x144 + x99);
  uint64_t x146 = ((x143 >> 51) | ((x145 << 13) & UINT64_C(0xffffffffffffffff)));
  uint64_t x147 = (x143 & UINT64_C(0x7ffffffffffff));
  uint64_t x148;
  uint1 x149;
  addcarryx_u64(&x148, &x149, 0x0, x146, x81);
  uint64_t x150 = (x149 + x83);
  uint64_t x151 = ((x148 >> 51) | ((x150 << 13) & UINT64_C(0xffffffffffffffff)));
  uint64_t x152 = (x148 & UINT64_C(0x7ffffffffffff));
  uint64_t x153 = (x151 * (uint64_t)UINT8_C(0x13));
  uint64_t x154 = (x68 + x153);
  uint64_t x155 = (x154 >> 51);
  uint64_t x156 = (x154 & UINT64_C(0x7ffffffffffff));
  uint64_t x157 = (x155 + x137);
  uint64_t x158 = (x157 >> 51);
  uint64_t x159 = (x157 & UINT64_C(0x7ffffffffffff));
  uint64_t x160 = (x158 + x142);
  out1[0] = x156;
  out1[1] = x159;
  out1[2] = x160;
  out1[3] = x147;
  out1[4] = x152;
}
*)
  End __.
End debugging_remove_mul_split_to_C_uint1_carry.

Module debugging_remove_mul_split.
  Section __.
    Context (n : nat := 5%nat)
            (s : Z := 2^255)
            (c : list (Z * Z) := [(1,19)])
            (machine_wordsize : Z := 64)
            (should_split_mul : should_split_mul_opt := true)
            (widen_carry : widen_carry_opt := true)
            (widen_bytes : widen_bytes_opt := true).

    Local Existing Instances should_split_mul widen_carry widen_bytes.

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

    Definition possible_values_of_machine_wordsize
      := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.

    Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.

    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.


    Let limbwidth_num := Eval vm_compute in Qnum limbwidth.
    Let limbwidth_den := Eval vm_compute in QDen limbwidth.

    Set Printing Depth 100000.
    Local Open Scope string_scope.
    Local Notation "'uint64,uint64'" := (ident.Z_cast2
                                           (r[0 ~> 18446744073709551615]%zrange,
                                            r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
    Local Notation "'uint64'" := (ident.Z_cast r[0 ~> 18446744073709551615]%zrange) : expr_scope.
    Local Open Scope expr_scope.
    Local Open Scope core_scope.
    Redirect "log" Compute
      Pipeline.BoundsPipeline
      false (* subst01 *)
      None (* fancy *)
      possible_values
      ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n idxs)) in
            exact r)
             (Some loose_bounds, (Some loose_bounds, tt))
             (Some tight_bounds).
(*     = ErrorT.Success
         (fun var : type -> Type =>
          λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
          expr_let x1 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x2 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x3 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[2]]))%expr_pat * ##19))))%expr_pat in
          expr_let x4 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[1]]))%expr_pat * ##19))))%expr_pat in
          expr_let x5 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x6 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x7 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[2]]))%expr_pat * ##19))))%expr_pat in
          expr_let x8 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[2]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x9 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[2]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x10 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @
                            ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x11 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[4]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x12 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[3]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x13 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[3]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x14 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[2]])) @ ((#uint64)%expr @ ($x0 [[2]]))))%expr_pat in
          expr_let x15 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[2]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x16 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[2]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x17 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[3]]))))%expr_pat in
          expr_let x18 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[2]]))))%expr_pat in
          expr_let x19 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x20 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x21 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[4]]))))%expr_pat in
          expr_let x22 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[3]]))))%expr_pat in
          expr_let x23 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[2]]))))%expr_pat in
          expr_let x24 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x25 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x26 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x7)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x4))))%expr_pat in
          expr_let x27 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x26)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x7)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x4))))%expr_pat in
          expr_let x28 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x9)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x26))))%expr_pat in
          expr_let x29 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x28)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x9)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x27))))%expr_pat in
          expr_let x30 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x10)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x28))))%expr_pat in
          expr_let x31 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x30)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x10)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x29))))%expr_pat in
          expr_let x32 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x25)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x30))))%expr_pat in
          expr_let x33 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x32)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x25)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x31))))%expr_pat in
          expr_let x34 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x32))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @
                                 ((#uint64)%expr @ ((#ident.fst)%expr @ $x33)) @ ##13))%expr_pat))%expr_pat in
          expr_let x35 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x32))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x36 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x12)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x11))))%expr_pat in
          expr_let x37 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x36)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x12)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x11))))%expr_pat in
          expr_let x38 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x14)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x36))))%expr_pat in
          expr_let x39 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x38)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x14)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x37))))%expr_pat in
          expr_let x40 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x17)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x38))))%expr_pat in
          expr_let x41 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x40)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x17)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x39))))%expr_pat in
          expr_let x42 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x21)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x40))))%expr_pat in
          expr_let x43 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x42)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x21)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x41))))%expr_pat in
          expr_let x44 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x13)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x1))))%expr_pat in
          expr_let x45 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x44)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x13)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x1))))%expr_pat in
          expr_let x46 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x15)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x44))))%expr_pat in
          expr_let x47 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x46)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x15)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x45))))%expr_pat in
          expr_let x48 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x18)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x46))))%expr_pat in
          expr_let x49 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x48)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x18)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x47))))%expr_pat in
          expr_let x50 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x22)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x48))))%expr_pat in
          expr_let x51 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x50)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x22)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x49))))%expr_pat in
          expr_let x52 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x5)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x2))))%expr_pat in
          expr_let x53 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x52)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x5)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x2))))%expr_pat in
          expr_let x54 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x16)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x52))))%expr_pat in
          expr_let x55 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x54)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x16)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x53))))%expr_pat in
          expr_let x56 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x19)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x54))))%expr_pat in
          expr_let x57 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x56)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x19)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x55))))%expr_pat in
          expr_let x58 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x23)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x56))))%expr_pat in
          expr_let x59 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x58)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x23)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x57))))%expr_pat in
          expr_let x60 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x6)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x3))))%expr_pat in
          expr_let x61 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x60)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x6)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x3))))%expr_pat in
          expr_let x62 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x8)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x60))))%expr_pat in
          expr_let x63 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x62)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x8)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x61))))%expr_pat in
          expr_let x64 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x20)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x62))))%expr_pat in
          expr_let x65 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x64)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x20)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x63))))%expr_pat in
          expr_let x66 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x24)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x64))))%expr_pat in
          expr_let x67 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x66)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x24)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x65))))%expr_pat in
          expr_let x68 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x34) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x66))))%expr_pat in
          expr_let x69 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x68))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x67))%expr_pat))%expr_pat in
          expr_let x70 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x68))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x69) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x71 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x68))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x72 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x70) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x58))))%expr_pat in
          expr_let x73 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x72))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x59))%expr_pat))%expr_pat in
          expr_let x74 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x72))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x73) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x75 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x72))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x76 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x74) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x50))))%expr_pat in
          expr_let x77 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x76))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x51))%expr_pat))%expr_pat in
          expr_let x78 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x76))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x77) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x79 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x76))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x80 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x78) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x42))))%expr_pat in
          expr_let x81 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x80))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x43))%expr_pat))%expr_pat in
          expr_let x82 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x80))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x81) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x83 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x80))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x84 := ((#uint64)%expr @ (((#uint64)%expr @ $x82)%expr_pat * ##19))%expr_pat in
          expr_let x85 := ((#uint64)%expr @
                           (((#uint64)%expr @ $x35)%expr_pat + ((#uint64)%expr @ $x84)%expr_pat))%expr_pat in
          expr_let x86 := ((#uint64)%expr @ (((#uint64)%expr @ $x85)%expr_pat >> ##51))%expr_pat in
          expr_let x87 := ((#uint64)%expr @ (((#uint64)%expr @ $x85)%expr_pat &' ##2251799813685247))%expr_pat in
          expr_let x88 := ((#uint64)%expr @
                           (((#uint64)%expr @ $x86)%expr_pat + ((#uint64)%expr @ $x71)%expr_pat))%expr_pat in
          expr_let x89 := ((#uint64)%expr @ (((#uint64)%expr @ $x88)%expr_pat >> ##51))%expr_pat in
          expr_let x90 := ((#uint64)%expr @ (((#uint64)%expr @ $x88)%expr_pat &' ##2251799813685247))%expr_pat in
          expr_let x91 := ((#uint64)%expr @
                           (((#uint64)%expr @ $x89)%expr_pat + ((#uint64)%expr @ $x75)%expr_pat))%expr_pat in
          [((#uint64)%expr @ $x87)%expr_pat; ((#uint64)%expr @ $x90)%expr_pat;
          ((#uint64)%expr @ $x91)%expr_pat; ((#uint64)%expr @ $x79)%expr_pat;
          ((#uint64)%expr @ $x83)%expr_pat])
     : Pipeline.ErrorT
         (Expr
            (type.base (base.type.list (base.type.type_base base.type.Z)) ->
             type.base (base.type.list (base.type.type_base base.type.Z)) ->
             type.base (base.type.list (base.type.type_base base.type.Z))))
 *)
  End __.
End debugging_remove_mul_split.

Module debugging_remove_mul_split2.
  Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
  Import Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
  Section __.
    Context (m : Z := 2^224 - 2^96 + 1)
            (machine_wordsize : Z := 64)
            (should_split_mul : should_split_mul_opt := true)
            (widen_carry : widen_carry_opt := true)
            (widen_bytes : widen_bytes_opt := true).

    Local Existing Instances should_split_mul widen_carry widen_bytes.

    Let s := 2^Z.log2_up m.
    Let c := s - m.
    Let n : nat := Eval compute in Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let r := 2^machine_wordsize.
    Let r' := match Z.modinv r m with
              | Some r' => r'
              | None => 0
              end.
    Let m' := Eval vm_compute in
          match Z.modinv (-m) r with
          | Some m' => m'
          | None => 0
          end.

    Local Notation saturated_bounds := (Primitives.saturated_bounds n machine_wordsize).

    Definition bounds : list (ZRange.type.option.interp base.type.Z)
      := Option.invert_Some saturated_bounds (*List.map (fun u => Some r[0~>u]%zrange) upperbounds*).

    Definition possible_values_of_machine_wordsize
      := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.
    Let possible_values := possible_values_of_machine_wordsize.

    Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.

    (*
    Time Definition foo :=
      ltac:(let r := Reify ((mulmod machine_wordsize n m m')) in
            exact r).
*)
    Set Printing Depth 100000.
    Local Open Scope string_scope.
    (*
    Redirect "log" Compute
      Pipeline.BoundsPipelineToStrings
      true (* static *)
      "" (* prefix *)
      "mul"
      false (* subst01 *)
      None
      None (* fancy *)
      possible_values
      foo
      (fun _ _ => []) (* comment *)
      (Some bounds, (Some bounds, tt))
      (Some bounds).
*)
    Redirect "log" Check (fun with_mul_split => with_mul_split).
    Time Redirect "log" Compute smul m machine_wordsize "" (* prefix *).
    Redirect "log" Check (fun without_mul_split => without_mul_split).
    Time Redirect "log" Compute smul m machine_wordsize "" (* prefix *).
    Goal True.
      pose (smul m machine_wordsize "") as v; clear -v.
      cbv in m; subst m machine_wordsize.
      cbv [smul] in v.
      set (k := mul _ _) in (value of v).
      clear v.
      cbv [mul] in k.
      Import WordByWordMontgomeryReificationCache.
      cbv -[Pipeline.BoundsPipeline reified_mul_gen] in k.
      cbv [Pipeline.BoundsPipeline LetIn.Let_In] in k.
      set (v := CheckedPartialEvaluateWithBounds _ _ _ _) in (value of k).
      Notation INL := (inl _).
      vm_compute in v.
      Notation IDD := (id _).
      lazymatch (eval cbv [v] in v) with
      | @inl ?A ?B ?x => pose (id x) as v'; change v with (@inl A B v') in (value of k); clear v
      end.
      cbv beta iota in k.
      set (v := Pipeline.RewriteAndEliminateDeadAndInline _ _ _ _) in (value of k).
      set (v'' := MulSplit.Compilers.RewriteRules.RewriteMulSplit _ _ _) in (value of k).
      vm_compute in v; clear v';
      lazymatch (eval cbv [v] in v) with
      | ?x => pose (id x) as v'; change v with v' in (value of v''); clear v
      end.
      cbv [id] in v'.
      vm_compute in v''.
    Abort.
  End __.
End debugging_remove_mul_split2.

Local Instance split_mul_to : split_mul_to_opt := None.

Module debugging_rewriting.
  Section __.
    Context (n : nat := 2%nat)
            (s : Z := 2^127)
            (c : list (Z * Z) := [(1,1)])
            (machine_wordsize : Z := 64).

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

    Definition possible_values_of_machine_wordsize
      := [0; machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.


    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.


    Let limbwidth_num := Eval vm_compute in Qnum limbwidth.
    Let limbwidth_den := Eval vm_compute in QDen limbwidth.

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true None [64; 128]
         ltac:(let r := Reify (fun f g
                               => (  (addmod limbwidth_num limbwidth_den n f g)
                              )) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true None [64; 128]
         ltac:(let r := Reify (fun f g
                               => (  (add (weight limbwidth_num limbwidth_den) n f g)
                              )) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true None [64; 128]
         ltac:(let r := Reify (fun f g
                               => let a_a := to_associational (weight limbwidth_num limbwidth_den) n f in
                                  let b_a := to_associational (weight limbwidth_num limbwidth_den) n g in from_associational (weight limbwidth_num limbwidth_den) n (a_a ++ b_a)
                              ) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true None [64; 128]
         ltac:(let r := Reify (fun f (g : list Z)
                               => let a_a := to_associational (weight limbwidth_num limbwidth_den) n f in
                                  a_a) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true None [64; 128]
         ltac:(let r := Reify (fun (f g : list Z)
                               => let a_a := combine (map (weight limbwidth_num limbwidth_den) (seq 0 n)) f in
                                  a_a) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Definition foo := (Pipeline.BoundsPipeline
                         true None [64; 128]
                         ltac:(let r := Reify (combine [1; 2] [1; 2]) in
                               exact r)
                                tt
                                ZRange.type.base.option.None).

  (*
  Goal True.
    pose foo as X; cbv [foo] in X.
    clear -X.
    cbv [Pipeline.BoundsPipeline LetIn.Let_In] in X.
    set (Y := (PartialEvaluateWithListInfoFromBounds _ _)) in (value of X).
    vm_compute in Y.
    subst Y; set (Y := (Rewriter.Compilers.PartialEvaluate _)) in (value of X).
    cbv [Rewriter.Compilers.PartialEvaluate Rewriter.Compilers.RewriteRules.RewriteNBE Rewriter.Compilers.RewriteRules.Compile.Rewrite Rewriter.Compilers.RewriteRules.Compile.rewrite] in Y.
    clear -Y.
    change (Rewriter.Compilers.RewriteRules.nbe_default_fuel) with (S (pred Rewriter.Compilers.RewriteRules.nbe_default_fuel)) in (value of Y).
    cbn [Rewriter.Compilers.RewriteRules.Compile.repeat_rewrite] in Y.
    cbv [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in Y.
    Print Rewriter.Compilers.RewriteRules.nbe_rewrite_head.
  Abort.
   *)
  End __.
End debugging_rewriting.

Section debugging_p448.
  Context (n : nat := 8%nat)
          (s : Z := 2^448)
          (c : list (Z * Z) := [(2^224,1);(1,1)])
          (machine_wordsize : Z := 64).

  Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
  Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

  Definition possible_values_of_machine_wordsize
    := [0; machine_wordsize; 2 * machine_wordsize]%Z.

  Let possible_values := possible_values_of_machine_wordsize.


  Let prime_upperbound_list : list Z
    := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
  Let tight_upperbounds : list Z
    := List.map
         (fun v : Z => Qceiling (11/10 * v))
         prime_upperbound_list.
  Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
  Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
    := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.


  Let limbwidth_num := Eval vm_compute in Qnum limbwidth.
  Let limbwidth_den := Eval vm_compute in QDen limbwidth.

  Set Printing Depth 100000.
  Local Open Scope string_scope.
  Redirect "log" Print squaremod.
  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f
                              => (  (squaremod (weight limbwidth_num limbwidth_den) s c n f)
                                    )) in
              exact r)
               (Some (repeat (@None _) n), tt)
               ZRange.type.base.option.None).

  Time Redirect "log" Compute
       Pipeline.BoundsPipelineToStrings
       "" (* prefix *)
       "mul"
       false (* subst01 *)
       None (* fancy *)
       possible_values
       ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n [3; 7; 4; 0; 5; 1; 6; 2; 7; 3; 4; 0]%nat)) in
             exact r)
              (fun _ _ => []) (* comment *)
              (Some loose_bounds, (Some loose_bounds, tt))
              (Some tight_bounds).

  Time Redirect "log" Compute
       Pipeline.BoundsPipeline
       false (* subst01 *)
       None (* fancy *)
       possible_values
       ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n [3; 7; 4; 0; 5; 1; 6; 2; 7; 3; 4; 0]%nat)) in
             exact r)
              (Some loose_bounds, (Some loose_bounds, tt))
              (Some tight_bounds).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n [3; 7; 4; 0; 5; 1; 6; 2; 7; 3; 4; 0]%nat)) in
              exact r)
               (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
               ZRange.type.base.option.None).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n []%nat)) in
              exact r)
               (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
               ZRange.type.base.option.None).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun f g
                              => (  (mulmod (weight limbwidth_num limbwidth_den) s c n f g)
                                    )) in
              exact r)
               (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
               ZRange.type.base.option.None).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true None [64; 128]
        ltac:(let r := Reify (fun a b
                              => (let weight := weight limbwidth_num limbwidth_den in
                                  let a_a := to_associational weight n a in
                                  let b_a := to_associational weight n b in
                                  let ab_a := mul a_a b_a in
                                  let abm_a := reduce s c ab_a in
                                  let abm_a := reduce s c abm_a in
                                  let abm_a := reduce s c abm_a in
                                  let abm_a := reduce s c abm_a in
                                  let abm_a := reduce s c abm_a in
                                  let abm_a := reduce s c abm_a in
                                  let abm_a := reduce s c abm_a in
                                  let abm_a := reduce s c abm_a in
                                  from_associational weight n abm_a

                                    )) in
              exact r)
               (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
               ZRange.type.base.option.None).
End debugging_p448.

(* TODO: Figure out what examples should go here *)
(*
Module X25519_64.
  Definition n := 5%nat.
  Definition s := 2^255.
  Definition c := [(1, 19)].
  Definition machine_wordsize := 64.
  Local Notation tight_bounds := (tight_bounds n s c).
  Local Notation loose_bounds := (loose_bounds n s c).
  Local Notation prime_bound := (prime_bound s c).

  Derive base_51_relax
         SuchThat (rrelax_correctT n s c machine_wordsize base_51_relax)
         As base_51_relax_correct.
  Proof. Time solve_rrelax machine_wordsize. Time Qed.
  Derive base_51_carry_mul
         SuchThat (rcarry_mul_correctT n s c machine_wordsize base_51_carry_mul)
         As base_51_carry_mul_correct.
  Proof. Time solve_rcarry_mul machine_wordsize. Time Qed.
  Derive base_51_carry
         SuchThat (rcarry_correctT n s c machine_wordsize base_51_carry)
         As base_51_carry_correct.
  Proof. Time solve_rcarry machine_wordsize. Time Qed.
  Derive base_51_add
         SuchThat (radd_correctT n s c machine_wordsize base_51_add)
         As base_51_add_correct.
  Proof. Time solve_radd machine_wordsize. Time Qed.
  Derive base_51_sub
         SuchThat (rsub_correctT n s c machine_wordsize base_51_sub)
         As base_51_sub_correct.
  Proof. Time solve_rsub machine_wordsize. Time Qed.
  Derive base_51_opp
         SuchThat (ropp_correctT n s c machine_wordsize base_51_opp)
         As base_51_opp_correct.
  Proof. Time solve_ropp machine_wordsize. Time Qed.
  Derive base_51_to_bytes
         SuchThat (rto_bytes_correctT n s c machine_wordsize base_51_to_bytes)
         As base_51_to_bytes_correct.
  Proof. Time solve_rto_bytes machine_wordsize. Time Qed.
  Derive base_51_from_bytes
         SuchThat (rfrom_bytes_correctT n s c machine_wordsize base_51_from_bytes)
         As base_51_from_bytes_correct.
  Proof. Time solve_rfrom_bytes machine_wordsize. Time Qed.
  Derive base_51_encode
         SuchThat (rencode_correctT n s c machine_wordsize base_51_encode)
         As base_51_encode_correct.
  Proof. Time solve_rencode machine_wordsize. Time Qed.
  Derive base_51_zero
         SuchThat (rzero_correctT n s c machine_wordsize base_51_zero)
         As base_51_zero_correct.
  Proof. Time solve_rzero machine_wordsize. Time Qed.
  Derive base_51_one
         SuchThat (rone_correctT n s c machine_wordsize base_51_one)
         As base_51_one_correct.
  Proof. Time solve_rone machine_wordsize. Time Qed.
  Lemma base_51_curve_good
    : check_args n s c machine_wordsize (ErrorT.Success tt) = ErrorT.Success tt.
  Proof. vm_compute; reflexivity. Qed.

  Definition base_51_good : GoodT n s c machine_wordsize
    := Good n s c machine_wordsize
            base_51_curve_good
            base_51_carry_mul_correct
            base_51_carry_correct
            base_51_relax_correct
            base_51_add_correct
            base_51_sub_correct
            base_51_opp_correct
            base_51_zero_correct
            base_51_one_correct
            base_51_encode_correct
            base_51_to_bytes_correct
            base_51_from_bytes_correct.

  Print Assumptions base_51_good.
  Import PrintingNotations.
  Set Printing Width 80.
  Open Scope string_scope.
  Print base_51_carry_mul.
(*base_51_carry_mul =
fun var : type -> Type =>
(λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
 expr_let x1 := (uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                ((uint64)(x[[1]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19) +₁₂₈
                 ((uint64)(x[[2]]) *₁₂₈ ((uint64)(x0[[3]]) *₆₄ 19) +₁₂₈
                  ((uint64)(x[[3]]) *₁₂₈ ((uint64)(x0[[2]]) *₆₄ 19) +₁₂₈
                   (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[1]]) *₆₄ 19)))) in
 expr_let x2 := (uint64)(x1 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ ((uint64)(x0[[3]]) *₆₄ 19) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[2]]) *₆₄ 19))))) in
 expr_let x3 := (uint64)(x2 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[2]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[3]]) *₆₄ 19))))) in
 expr_let x4 := (uint64)(x3 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[3]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[2]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ (uint64)(x0[[0]]) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ ((uint64)(x0[[4]]) *₆₄ 19))))) in
 expr_let x5 := (uint64)(x4 >> 51) +₁₂₈
                ((uint64)(x[[0]]) *₁₂₈ (uint64)(x0[[4]]) +₁₂₈
                 ((uint64)(x[[1]]) *₁₂₈ (uint64)(x0[[3]]) +₁₂₈
                  ((uint64)(x[[2]]) *₁₂₈ (uint64)(x0[[2]]) +₁₂₈
                   ((uint64)(x[[3]]) *₁₂₈ (uint64)(x0[[1]]) +₁₂₈
                    (uint64)(x[[4]]) *₁₂₈ (uint64)(x0[[0]]))))) in
 expr_let x6 := ((uint64)(x1) & 2251799813685247) +₆₄ (uint64)(x5 >> 51) *₆₄ 19 in
 expr_let x7 := (uint64)(x6 >> 51) +₆₄ ((uint64)(x2) & 2251799813685247) in
 expr_let x8 := ((uint64)(x6) & 2251799813685247) in
 expr_let x9 := ((uint64)(x7) & 2251799813685247) in
 expr_let x10 := (uint64)(x7 >> 51) +₆₄ ((uint64)(x3) & 2251799813685247) in
 expr_let x11 := ((uint64)(x4) & 2251799813685247) in
 expr_let x12 := ((uint64)(x5) & 2251799813685247) in
 [x8; x9; x10; x11; x12])%expr
     : Expr
         (type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)
  Print base_51_sub.
  (*
base_51_sub =
fun var : type -> Type =>
(λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
 expr_let x1 := (4503599627370458 +₆₄ (uint64)(x[[0]])) -₆₄ (uint64)(x0[[0]]) in
 expr_let x2 := (4503599627370494 +₆₄ (uint64)(x[[1]])) -₆₄ (uint64)(x0[[1]]) in
 expr_let x3 := (4503599627370494 +₆₄ (uint64)(x[[2]])) -₆₄ (uint64)(x0[[2]]) in
 expr_let x4 := (4503599627370494 +₆₄ (uint64)(x[[3]])) -₆₄ (uint64)(x0[[3]]) in
 expr_let x5 := (4503599627370494 +₆₄ (uint64)(x[[4]])) -₆₄ (uint64)(x0[[4]]) in
 [x1; x2; x3; x4; x5])%expr
     : Expr
         (type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)

  Redirect "log" Compute Compilers.ToString.C.ToFunctionString
          true true "" "fecarry_mul" [] base_51_carry_mul
          None (Some loose_bounds, (Some loose_bounds, tt)).
  (*
void fecarry_mul(uint64_t[5] x1, uint64_t[5] x2, uint64_t[5] x3) {
  uint128_t x4 = (((uint128_t)(x1[0]) * (x2[0])) + (((uint128_t)(x1[1]) * ((x2[4]) * 0x13)) + (((uint128_t)(x1[2]) * ((x2[3]) * 0x13)) + (((uint128_t)(x1[3]) * ((x2[2]) * 0x13)) + ((uint128_t)(x1[4]) * ((x2[1]) * 0x13))))));
  uint128_t x5 = ((uint64_t)(x4 >> 51) + (((uint128_t)(x1[0]) * (x2[1])) + (((uint128_t)(x1[1]) * (x2[0])) + (((uint128_t)(x1[2]) * ((x2[4]) * 0x13)) + (((uint128_t)(x1[3]) * ((x2[3]) * 0x13)) + ((uint128_t)(x1[4]) * ((x2[2]) * 0x13)))))));
  uint128_t x6 = ((uint64_t)(x5 >> 51) + (((uint128_t)(x1[0]) * (x2[2])) + (((uint128_t)(x1[1]) * (x2[1])) + (((uint128_t)(x1[2]) * (x2[0])) + (((uint128_t)(x1[3]) * ((x2[4]) * 0x13)) + ((uint128_t)(x1[4]) * ((x2[3]) * 0x13)))))));
  uint128_t x7 = ((uint64_t)(x6 >> 51) + (((uint128_t)(x1[0]) * (x2[3])) + (((uint128_t)(x1[1]) * (x2[2])) + (((uint128_t)(x1[2]) * (x2[1])) + (((uint128_t)(x1[3]) * (x2[0])) + ((uint128_t)(x1[4]) * ((x2[4]) * 0x13)))))));
  uint128_t x8 = ((uint64_t)(x7 >> 51) + (((uint128_t)(x1[0]) * (x2[4])) + (((uint128_t)(x1[1]) * (x2[3])) + (((uint128_t)(x1[2]) * (x2[2])) + (((uint128_t)(x1[3]) * (x2[1])) + ((uint128_t)(x1[4]) * (x2[0])))))));
  uint64_t x9 = ((uint64_t)(x4 & 0x7ffffffffffffUL) + ((uint64_t)(x8 >> 51) * 0x13));
  uint64_t x10 = ((x9 >> 51) + (uint64_t)(x5 & 0x7ffffffffffffUL));
  x3[0] = (x9 & 0x7ffffffffffffUL);
  x3[1] = (x10 & 0x7ffffffffffffUL);
  x3[2] = ((x10 >> 51) + (uint64_t)(x6 & 0x7ffffffffffffUL));
  x3[3] = (uint64_t)(x7 & 0x7ffffffffffffUL);
  x3[4] = (uint64_t)(x8 & 0x7ffffffffffffUL);
}
*)
  Redirect "log" Compute Compilers.ToString.C.ToFunctionString
          true true "" "fesub" [] base_51_sub
          None (Some tight_bounds, (Some tight_bounds, tt)).
(*
void fesub(uint64_t[5] x1, uint64_t[5] x2, uint64_t[5] x3) {
  x3[0] = ((0xfffffffffffdaUL + (x1[0])) - (x2[0]));
  x3[1] = ((0xffffffffffffeUL + (x1[1])) - (x2[1]));
  x3[2] = ((0xffffffffffffeUL + (x1[2])) - (x2[2]));
  x3[3] = ((0xffffffffffffeUL + (x1[3])) - (x2[3]));
  x3[4] = ((0xffffffffffffeUL + (x1[4])) - (x2[4]));
}
*)
End X25519_64.

Module X25519_32.
  Definition n := 10%nat.
  Definition s := 2^255.
  Definition c := [(1, 19)].
  Definition machine_wordsize := 32.

  Derive base_25p5_relax
         SuchThat (rrelax_correctT n s c machine_wordsize base_25p5_relax)
         As base_25p5_relax_correct.
  Proof. Time solve_rrelax machine_wordsize. Time Qed.
  Derive base_25p5_carry_mul
         SuchThat (rcarry_mul_correctT n s c machine_wordsize base_25p5_carry_mul)
         As base_25p5_carry_mul_correct.
  Proof. Time solve_rcarry_mul machine_wordsize. Time Qed.
  Derive base_25p5_carry
         SuchThat (rcarry_correctT n s c machine_wordsize base_25p5_carry)
         As base_25p5_carry_correct.
  Proof. Time solve_rcarry machine_wordsize. Time Qed.
  Derive base_25p5_add
         SuchThat (radd_correctT n s c machine_wordsize base_25p5_add)
         As base_25p5_add_correct.
  Proof. Time solve_radd machine_wordsize. Time Qed.
  Derive base_25p5_sub
         SuchThat (rsub_correctT n s c machine_wordsize base_25p5_sub)
         As base_25p5_sub_correct.
  Proof. Time solve_rsub machine_wordsize. Time Qed.
  Derive base_25p5_opp
         SuchThat (ropp_correctT n s c machine_wordsize base_25p5_opp)
         As base_25p5_opp_correct.
  Proof. Time solve_ropp machine_wordsize. Time Qed.
  (* These are very, very, very slow *)
  (*
  Derive base_25p5_to_bytes
         SuchThat (rto_bytes_correctT n s c machine_wordsize base_25p5_to_bytes)
         As base_25p5_to_bytes_correct.
  Proof. Time solve_rto_bytes machine_wordsize. Time Qed.
  Derive base_25p5_from_bytes
         SuchThat (rfrom_bytes_correctT n s c machine_wordsize base_25p5_from_bytes)
         As base_25p5_from_bytes_correct.
  Proof. Time solve_rfrom_bytes machine_wordsize. Time Qed.
   *)
  Derive base_25p5_encode
         SuchThat (rencode_correctT n s c machine_wordsize base_25p5_encode)
         As base_25p5_encode_correct.
  Proof. Time solve_rencode machine_wordsize. Time Qed.
  Derive base_25p5_zero
         SuchThat (rzero_correctT n s c machine_wordsize base_25p5_zero)
         As base_25p5_zero_correct.
  Proof. Time solve_rzero machine_wordsize. Time Qed.
  Derive base_25p5_one
         SuchThat (rone_correctT n s c machine_wordsize base_25p5_one)
         As base_25p5_one_correct.
  Proof. Time solve_rone machine_wordsize. Time Qed.
  Lemma base_25p5_curve_good
    : check_args n s c machine_wordsize (ErrorT.Success tt) = ErrorT.Success tt.
  Proof. vm_compute; reflexivity. Qed.

  (*
  Definition base_25p5_good : GoodT n s c machine_wordsize
    := Good n s c machine_wordsize
            base_25p5_curve_good
            base_25p5_carry_mul_correct
            base_25p5_carry_correct
            base_25p5_relax_correct
            base_25p5_add_correct
            base_25p5_sub_correct
            base_25p5_opp_correct
            base_25p5_zero_correct
            base_25p5_one_correct
            base_25p5_encode_correct
            base_25p5_to_bytes_correct
            base_25p5_from_bytes_correct.
   *)
  (*
  Print Assumptions base_25p5_good.
   *)
  Import PrintingNotations.
  Set Printing Width 80.
  Print base_25p5_carry_mul.
(*
base_25p5_carry_mul =
fun var : type -> Type =>
(λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
 expr_let x1 := (uint32)(x[[0]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                ((uint64)((uint32)(x[[1]]) *₆₄ ((uint32)(x0[[9]]) *₃₂ 19) << 1) +₆₄
                 ((uint32)(x[[2]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19) +₆₄
                  ((uint64)((uint32)(x[[3]]) *₆₄ ((uint32)(x0[[7]]) *₃₂ 19) << 1) +₆₄
                   ((uint32)(x[[4]]) *₆₄ ((uint32)(x0[[6]]) *₃₂ 19) +₆₄
                    ((uint64)((uint32)(x[[5]]) *₆₄ ((uint32)(x0[[5]]) *₃₂ 19) << 1) +₆₄
                     ((uint32)(x[[6]]) *₆₄ ((uint32)(x0[[4]]) *₃₂ 19) +₆₄
                      ((uint64)((uint32)(x[[7]]) *₆₄ ((uint32)(x0[[3]]) *₃₂ 19) << 1) +₆₄
                       ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[2]]) *₃₂ 19) +₆₄
                        (uint64)((uint32)(x[[9]]) *₆₄
                                 ((uint32)(x0[[1]]) *₃₂ 19) << 1))))))))) in
 expr_let x2 := (uint64)(x1 >> 26) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[1]]) +₆₄
                 ((uint32)(x[[1]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                  ((uint32)(x[[2]]) *₆₄ ((uint32)(x0[[9]]) *₃₂ 19) +₆₄
                   ((uint32)(x[[3]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19) +₆₄
                    ((uint32)(x[[4]]) *₆₄ ((uint32)(x0[[7]]) *₃₂ 19) +₆₄
                     ((uint32)(x[[5]]) *₆₄ ((uint32)(x0[[6]]) *₃₂ 19) +₆₄
                      ((uint32)(x[[6]]) *₆₄ ((uint32)(x0[[5]]) *₃₂ 19) +₆₄
                       ((uint32)(x[[7]]) *₆₄ ((uint32)(x0[[4]]) *₃₂ 19) +₆₄
                        ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[3]]) *₃₂ 19) +₆₄
                         (uint32)(x[[9]]) *₆₄ ((uint32)(x0[[2]]) *₃₂ 19)))))))))) in
 expr_let x3 := (uint64)(x2 >> 25) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                 ((uint64)((uint32)(x[[1]]) *₆₄ (uint32)(x0[[1]]) << 1) +₆₄
                  ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                   ((uint64)((uint32)(x[[3]]) *₆₄ ((uint32)(x0[[9]]) *₃₂ 19) << 1) +₆₄
                    ((uint32)(x[[4]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19) +₆₄
                     ((uint64)((uint32)(x[[5]]) *₆₄ ((uint32)(x0[[7]]) *₃₂ 19) << 1) +₆₄
                      ((uint32)(x[[6]]) *₆₄ ((uint32)(x0[[6]]) *₃₂ 19) +₆₄
                       ((uint64)((uint32)(x[[7]]) *₆₄
                                 ((uint32)(x0[[5]]) *₃₂ 19) << 1) +₆₄
                        ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[4]]) *₃₂ 19) +₆₄
                         (uint64)((uint32)(x[[9]]) *₆₄
                                  ((uint32)(x0[[3]]) *₃₂ 19) << 1)))))))))) in
 expr_let x4 := (uint64)(x3 >> 26) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[3]]) +₆₄
                 ((uint32)(x[[1]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                  ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[1]]) +₆₄
                   ((uint32)(x[[3]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                    ((uint32)(x[[4]]) *₆₄ ((uint32)(x0[[9]]) *₃₂ 19) +₆₄
                     ((uint32)(x[[5]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19) +₆₄
                      ((uint32)(x[[6]]) *₆₄ ((uint32)(x0[[7]]) *₃₂ 19) +₆₄
                       ((uint32)(x[[7]]) *₆₄ ((uint32)(x0[[6]]) *₃₂ 19) +₆₄
                        ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[5]]) *₃₂ 19) +₆₄
                         (uint32)(x[[9]]) *₆₄ ((uint32)(x0[[4]]) *₃₂ 19)))))))))) in
 expr_let x5 := (uint64)(x4 >> 25) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[4]]) +₆₄
                 ((uint64)((uint32)(x[[1]]) *₆₄ (uint32)(x0[[3]]) << 1) +₆₄
                  ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                   ((uint64)((uint32)(x[[3]]) *₆₄ (uint32)(x0[[1]]) << 1) +₆₄
                    ((uint32)(x[[4]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                     ((uint64)((uint32)(x[[5]]) *₆₄ ((uint32)(x0[[9]]) *₃₂ 19) << 1) +₆₄
                      ((uint32)(x[[6]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19) +₆₄
                       ((uint64)((uint32)(x[[7]]) *₆₄
                                 ((uint32)(x0[[7]]) *₃₂ 19) << 1) +₆₄
                        ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[6]]) *₃₂ 19) +₆₄
                         (uint64)((uint32)(x[[9]]) *₆₄
                                  ((uint32)(x0[[5]]) *₃₂ 19) << 1)))))))))) in
 expr_let x6 := (uint64)(x5 >> 26) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[5]]) +₆₄
                 ((uint32)(x[[1]]) *₆₄ (uint32)(x0[[4]]) +₆₄
                  ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[3]]) +₆₄
                   ((uint32)(x[[3]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                    ((uint32)(x[[4]]) *₆₄ (uint32)(x0[[1]]) +₆₄
                     ((uint32)(x[[5]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                      ((uint32)(x[[6]]) *₆₄ ((uint32)(x0[[9]]) *₃₂ 19) +₆₄
                       ((uint32)(x[[7]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19) +₆₄
                        ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[7]]) *₃₂ 19) +₆₄
                         (uint32)(x[[9]]) *₆₄ ((uint32)(x0[[6]]) *₃₂ 19)))))))))) in
 expr_let x7 := (uint64)(x6 >> 25) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[6]]) +₆₄
                 ((uint64)((uint32)(x[[1]]) *₆₄ (uint32)(x0[[5]]) << 1) +₆₄
                  ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[4]]) +₆₄
                   ((uint64)((uint32)(x[[3]]) *₆₄ (uint32)(x0[[3]]) << 1) +₆₄
                    ((uint32)(x[[4]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                     ((uint64)((uint32)(x[[5]]) *₆₄ (uint32)(x0[[1]]) << 1) +₆₄
                      ((uint32)(x[[6]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                       ((uint64)((uint32)(x[[7]]) *₆₄
                                 ((uint32)(x0[[9]]) *₃₂ 19) << 1) +₆₄
                        ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19) +₆₄
                         (uint64)((uint32)(x[[9]]) *₆₄
                                  ((uint32)(x0[[7]]) *₃₂ 19) << 1)))))))))) in
 expr_let x8 := (uint64)(x7 >> 26) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[7]]) +₆₄
                 ((uint32)(x[[1]]) *₆₄ (uint32)(x0[[6]]) +₆₄
                  ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[5]]) +₆₄
                   ((uint32)(x[[3]]) *₆₄ (uint32)(x0[[4]]) +₆₄
                    ((uint32)(x[[4]]) *₆₄ (uint32)(x0[[3]]) +₆₄
                     ((uint32)(x[[5]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                      ((uint32)(x[[6]]) *₆₄ (uint32)(x0[[1]]) +₆₄
                       ((uint32)(x[[7]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                        ((uint32)(x[[8]]) *₆₄ ((uint32)(x0[[9]]) *₃₂ 19) +₆₄
                         (uint32)(x[[9]]) *₆₄ ((uint32)(x0[[8]]) *₃₂ 19)))))))))) in
 expr_let x9 := (uint64)(x8 >> 25) +₆₄
                ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[8]]) +₆₄
                 ((uint64)((uint32)(x[[1]]) *₆₄ (uint32)(x0[[7]]) << 1) +₆₄
                  ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[6]]) +₆₄
                   ((uint64)((uint32)(x[[3]]) *₆₄ (uint32)(x0[[5]]) << 1) +₆₄
                    ((uint32)(x[[4]]) *₆₄ (uint32)(x0[[4]]) +₆₄
                     ((uint64)((uint32)(x[[5]]) *₆₄ (uint32)(x0[[3]]) << 1) +₆₄
                      ((uint32)(x[[6]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                       ((uint64)((uint32)(x[[7]]) *₆₄ (uint32)(x0[[1]]) << 1) +₆₄
                        ((uint32)(x[[8]]) *₆₄ (uint32)(x0[[0]]) +₆₄
                         (uint64)((uint32)(x[[9]]) *₆₄
                                  ((uint32)(x0[[9]]) *₃₂ 19) << 1)))))))))) in
 expr_let x10 := (uint64)(x9 >> 26) +₆₄
                 ((uint32)(x[[0]]) *₆₄ (uint32)(x0[[9]]) +₆₄
                  ((uint32)(x[[1]]) *₆₄ (uint32)(x0[[8]]) +₆₄
                   ((uint32)(x[[2]]) *₆₄ (uint32)(x0[[7]]) +₆₄
                    ((uint32)(x[[3]]) *₆₄ (uint32)(x0[[6]]) +₆₄
                     ((uint32)(x[[4]]) *₆₄ (uint32)(x0[[5]]) +₆₄
                      ((uint32)(x[[5]]) *₆₄ (uint32)(x0[[4]]) +₆₄
                       ((uint32)(x[[6]]) *₆₄ (uint32)(x0[[3]]) +₆₄
                        ((uint32)(x[[7]]) *₆₄ (uint32)(x0[[2]]) +₆₄
                         ((uint32)(x[[8]]) *₆₄ (uint32)(x0[[1]]) +₆₄
                          (uint32)(x[[9]]) *₆₄ (uint32)(x0[[0]])))))))))) in
 expr_let x11 := ((uint32)(x1) & 67108863) +₆₄ (uint64)(x10 >> 25) *₆₄ 19 in
 expr_let x12 := (uint32)(x11 >> 26) +₃₂ ((uint32)(x2) & 33554431) in
 expr_let x13 := ((uint32)(x11) & 67108863) in
 expr_let x14 := ((uint32)(x12) & 33554431) in
 expr_let x15 := (uint32)(x12 >> 25) +₃₂ ((uint32)(x3) & 67108863) in
 expr_let x16 := ((uint32)(x4) & 33554431) in
 expr_let x17 := ((uint32)(x5) & 67108863) in
 expr_let x18 := ((uint32)(x6) & 33554431) in
 expr_let x19 := ((uint32)(x7) & 67108863) in
 expr_let x20 := ((uint32)(x8) & 33554431) in
 expr_let x21 := ((uint32)(x9) & 67108863) in
 expr_let x22 := ((uint32)(x10) & 33554431) in
 [x13; x14; x15; x16; x17; x18; x19; x20; x21; x22])%expr
     : Expr
         (type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
 *)
  Print base_25p5_sub.
  (*
base_25p5_sub =
fun var : type -> Type =>
(λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
 expr_let x1 := (134217690 +₃₂ (uint32)(x[[0]])) -₃₂ (uint32)(x0[[0]]) in
 expr_let x2 := (67108862 +₃₂ (uint32)(x[[1]])) -₃₂ (uint32)(x0[[1]]) in
 expr_let x3 := (134217726 +₃₂ (uint32)(x[[2]])) -₃₂ (uint32)(x0[[2]]) in
 expr_let x4 := (67108862 +₃₂ (uint32)(x[[3]])) -₃₂ (uint32)(x0[[3]]) in
 expr_let x5 := (134217726 +₃₂ (uint32)(x[[4]])) -₃₂ (uint32)(x0[[4]]) in
 expr_let x6 := (67108862 +₃₂ (uint32)(x[[5]])) -₃₂ (uint32)(x0[[5]]) in
 expr_let x7 := (134217726 +₃₂ (uint32)(x[[6]])) -₃₂ (uint32)(x0[[6]]) in
 expr_let x8 := (67108862 +₃₂ (uint32)(x[[7]])) -₃₂ (uint32)(x0[[7]]) in
 expr_let x9 := (134217726 +₃₂ (uint32)(x[[8]])) -₃₂ (uint32)(x0[[8]]) in
 expr_let x10 := (67108862 +₃₂ (uint32)(x[[9]])) -₃₂ (uint32)(x0[[9]]) in
 [x1; x2; x3; x4; x5; x6; x7; x8; x9; x10])%expr
     : Expr
         (type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)) ->
          type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)
End X25519_32.

Import Language.Compilers.

Module P192_64.
  Definition s := 2^192.
  Definition c :=  [(2^64, 1); (1,1)].
  Definition machine_wordsize := 64.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.
  Set Printing Depth 100000.

  Local Notation "'mul64' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint64, _)%core) @ (#Z_mul_split @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'add64' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adc64' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint64, bool)%core) @ (#Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) 18446744073709551616) @ c @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adx64' '(' c ',' x ',' y ')'" :=
    (#(Z_cast bool) @ (#Z_add_with_carry @ c @ x @ y))%expr (at level 50) : expr_scope.

  Print mulmod.
(*
mulmod = fun var : type -> Type => λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
         expr_let x1 := mul64 ((uint64)(x[[2]]), (uint64)(x0[[2]])) in
         expr_let x2 := mul64 ((uint64)(x[[2]]), (uint64)(x0[[1]])) in
         expr_let x3 := mul64 ((uint64)(x[[2]]), (uint64)(x0[[0]])) in
         expr_let x4 := mul64 ((uint64)(x[[1]]), (uint64)(x0[[2]])) in
         expr_let x5 := mul64 ((uint64)(x[[1]]), (uint64)(x0[[1]])) in
         expr_let x6 := mul64 ((uint64)(x[[1]]), (uint64)(x0[[0]])) in
         expr_let x7 := mul64 ((uint64)(x[[0]]), (uint64)(x0[[2]])) in
         expr_let x8 := mul64 ((uint64)(x[[0]]), (uint64)(x0[[1]])) in
         expr_let x9 := mul64 ((uint64)(x[[0]]), (uint64)(x0[[0]])) in
         expr_let x10 := add64 (x1₂, x9₂) in
         expr_let x11 := adc64 (x10₂, 0, x8₂) in
         expr_let x12 := add64 (x1₁, x10₁) in
         expr_let x13 := adc64 (x12₂, 0, x11₁) in
         expr_let x14 := add64 (x2₂, x12₁) in
         expr_let x15 := adc64 (x14₂, 0, x13₁) in
         expr_let x16 := add64 (x4₂, x14₁) in
         expr_let x17 := adc64 (x16₂, x1₂, x15₁) in
         expr_let x18 := add64 (x2₁, x16₁) in
         expr_let x19 := adc64 (x18₂, x1₁, x17₁) in
         expr_let x20 := add64 (x1₂, x9₁) in
         expr_let x21 := adc64 (x20₂, x3₂, x18₁) in
         expr_let x22 := adc64 (x21₂, x2₂, x19₁) in
         expr_let x23 := add64 (x2₁, x20₁) in
         expr_let x24 := adc64 (x23₂, x4₁, x21₁) in
         expr_let x25 := adc64 (x24₂, x4₂, x22₁) in
         expr_let x26 := add64 (x3₂, x23₁) in
         expr_let x27 := adc64 (x26₂, x5₂, x24₁) in
         expr_let x28 := adc64 (x27₂, x3₁, x25₁) in
         expr_let x29 := add64 (x4₁, x26₁) in
         expr_let x30 := adc64 (x29₂, x7₂, x27₁) in
         expr_let x31 := adc64 (x30₂, x5₁, x28₁) in
         expr_let x32 := add64 (x5₂, x29₁) in
         expr_let x33 := adc64 (x32₂, x6₁, x30₁) in
         expr_let x34 := adc64 (x33₂, x6₂, x31₁) in
         expr_let x35 := add64 (x7₂, x32₁) in
         expr_let x36 := adc64 (x35₂, x8₁, x33₁) in
         expr_let x37 := adc64 (x36₂, x7₁, x34₁) in
         [x35₁; x36₁; x37₁]
     : Expr (type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)

End P192_64.

Module P192_32.
  Definition s := 2^192.
  Definition c :=  [(2^64, 1); (1,1)].
  Definition machine_wordsize := 32.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.
  Set Printing Depth 100000.

  Local Notation "'mul32' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint32, _)%core) @ (#Z_mul_split @ #(ident.Literal (t:=base.type.Z) 4294967296) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'add32' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) 4294967296) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adc32' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) 4294967296) @ c @ x @ y))%expr (at level 50) : expr_scope.

  Print mulmod.
  (*
mulmod = fun var : type -> Type => λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
         expr_let x1 := mul32 ((uint32)(x[[5]]), (uint32)(x0[[5]])) in
         expr_let x2 := mul32 ((uint32)(x[[5]]), (uint32)(x0[[4]])) in
         expr_let x3 := mul32 ((uint32)(x[[5]]), (uint32)(x0[[3]])) in
         expr_let x4 := mul32 ((uint32)(x[[5]]), (uint32)(x0[[2]])) in
         expr_let x5 := mul32 ((uint32)(x[[5]]), (uint32)(x0[[1]])) in
         expr_let x6 := mul32 ((uint32)(x[[5]]), (uint32)(x0[[0]])) in
         expr_let x7 := mul32 ((uint32)(x[[4]]), (uint32)(x0[[5]])) in
         expr_let x8 := mul32 ((uint32)(x[[4]]), (uint32)(x0[[4]])) in
         expr_let x9 := mul32 ((uint32)(x[[4]]), (uint32)(x0[[3]])) in
         expr_let x10 := mul32 ((uint32)(x[[4]]), (uint32)(x0[[2]])) in
         expr_let x11 := mul32 ((uint32)(x[[4]]), (uint32)(x0[[1]])) in
         expr_let x12 := mul32 ((uint32)(x[[4]]), (uint32)(x0[[0]])) in
         expr_let x13 := mul32 ((uint32)(x[[3]]), (uint32)(x0[[5]])) in
         expr_let x14 := mul32 ((uint32)(x[[3]]), (uint32)(x0[[4]])) in
         expr_let x15 := mul32 ((uint32)(x[[3]]), (uint32)(x0[[3]])) in
         expr_let x16 := mul32 ((uint32)(x[[3]]), (uint32)(x0[[2]])) in
         expr_let x17 := mul32 ((uint32)(x[[3]]), (uint32)(x0[[1]])) in
         expr_let x18 := mul32 ((uint32)(x[[3]]), (uint32)(x0[[0]])) in
         expr_let x19 := mul32 ((uint32)(x[[2]]), (uint32)(x0[[5]])) in
         expr_let x20 := mul32 ((uint32)(x[[2]]), (uint32)(x0[[4]])) in
         expr_let x21 := mul32 ((uint32)(x[[2]]), (uint32)(x0[[3]])) in
         expr_let x22 := mul32 ((uint32)(x[[2]]), (uint32)(x0[[2]])) in
         expr_let x23 := mul32 ((uint32)(x[[2]]), (uint32)(x0[[1]])) in
         expr_let x24 := mul32 ((uint32)(x[[2]]), (uint32)(x0[[0]])) in
         expr_let x25 := mul32 ((uint32)(x[[1]]), (uint32)(x0[[5]])) in
         expr_let x26 := mul32 ((uint32)(x[[1]]), (uint32)(x0[[4]])) in
         expr_let x27 := mul32 ((uint32)(x[[1]]), (uint32)(x0[[3]])) in
         expr_let x28 := mul32 ((uint32)(x[[1]]), (uint32)(x0[[2]])) in
         expr_let x29 := mul32 ((uint32)(x[[1]]), (uint32)(x0[[1]])) in
         expr_let x30 := mul32 ((uint32)(x[[1]]), (uint32)(x0[[0]])) in
         expr_let x31 := mul32 ((uint32)(x[[0]]), (uint32)(x0[[5]])) in
         expr_let x32 := mul32 ((uint32)(x[[0]]), (uint32)(x0[[4]])) in
         expr_let x33 := mul32 ((uint32)(x[[0]]), (uint32)(x0[[3]])) in
         expr_let x34 := mul32 ((uint32)(x[[0]]), (uint32)(x0[[2]])) in
         expr_let x35 := mul32 ((uint32)(x[[0]]), (uint32)(x0[[1]])) in
         expr_let x36 := mul32 ((uint32)(x[[0]]), (uint32)(x0[[0]])) in
         expr_let x37 := add32 (x1₁, x35₂) in
         expr_let x38 := adc32 (x37₂, 0, x34₂) in
         expr_let x39 := adc32 (x38₂, 0, x33₂) in
         expr_let x40 := adc32 (x39₂, 0, x32₂) in
         expr_let x41 := add32 (x2₂, x37₁) in
         expr_let x42 := adc32 (x41₂, 0, x38₁) in
         expr_let x43 := adc32 (x42₂, 0, x39₁) in
         expr_let x44 := adc32 (x43₂, 0, x40₁) in
         expr_let x45 := add32 (x7₂, x41₁) in
         expr_let x46 := adc32 (x45₂, 0, x42₁) in
         expr_let x47 := adc32 (x46₂, 0, x43₁) in
         expr_let x48 := adc32 (x47₂, 0, x44₁) in
         expr_let x49 := add32 (x3₁, x45₁) in
         expr_let x50 := adc32 (x49₂, 0, x46₁) in
         expr_let x51 := adc32 (x50₂, 0, x47₁) in
         expr_let x52 := adc32 (x51₂, 0, x48₁) in
         expr_let x53 := add32 (x4₂, x49₁) in
         expr_let x54 := adc32 (x53₂, x1₂, x50₁) in
         expr_let x55 := adc32 (x54₂, 0, x51₁) in
         expr_let x56 := adc32 (x55₂, 0, x52₁) in
         expr_let x57 := add32 (x8₁, x53₁) in
         expr_let x58 := adc32 (x57₂, x2₁, x54₁) in
         expr_let x59 := adc32 (x58₂, 0, x55₁) in
         expr_let x60 := adc32 (x59₂, 0, x56₁) in
         expr_let x61 := add32 (x9₂, x57₁) in
         expr_let x62 := adc32 (x61₂, x3₂, x58₁) in
         expr_let x63 := adc32 (x62₂, 0, x59₁) in
         expr_let x64 := adc32 (x63₂, 0, x60₁) in
         expr_let x65 := add32 (x13₁, x61₁) in
         expr_let x66 := adc32 (x65₂, x7₁, x62₁) in
         expr_let x67 := adc32 (x66₂, x1₁, x63₁) in
         expr_let x68 := adc32 (x67₂, 0, x64₁) in
         expr_let x69 := add32 (x14₂, x65₁) in
         expr_let x70 := adc32 (x69₂, x8₂, x66₁) in
         expr_let x71 := adc32 (x70₂, x2₂, x67₁) in
         expr_let x72 := adc32 (x71₂, 0, x68₁) in
         expr_let x73 := add32 (x19₂, x69₁) in
         expr_let x74 := adc32 (x73₂, x13₂, x70₁) in
         expr_let x75 := adc32 (x74₂, x7₂, x71₁) in
         expr_let x76 := adc32 (x75₂, x1₂, x72₁) in
         expr_let x77 := add32 (x5₁, x73₁) in
         expr_let x78 := adc32 (x77₂, x4₁, x74₁) in
         expr_let x79 := adc32 (x78₂, x3₁, x75₁) in
         expr_let x80 := adc32 (x79₂, x2₁, x76₁) in
         expr_let x81 := add32 (x1₁, x36₁) in
         expr_let x82 := adc32 (x81₂, 0, x36₂) in
         expr_let x83 := adc32 (x82₂, x6₂, x77₁) in
         expr_let x84 := adc32 (x83₂, x5₂, x78₁) in
         expr_let x85 := adc32 (x84₂, x4₂, x79₁) in
         expr_let x86 := adc32 (x85₂, x3₂, x80₁) in
         expr_let x87 := add32 (x2₂, x81₁) in
         expr_let x88 := adc32 (x87₂, 0, x82₁) in
         expr_let x89 := adc32 (x88₂, x10₁, x83₁) in
         expr_let x90 := adc32 (x89₂, x9₁, x84₁) in
         expr_let x91 := adc32 (x90₂, x8₁, x85₁) in
         expr_let x92 := adc32 (x91₂, x7₁, x86₁) in
         expr_let x93 := add32 (x7₂, x87₁) in
         expr_let x94 := adc32 (x93₂, x1₂, x88₁) in
         expr_let x95 := adc32 (x94₂, x11₂, x89₁) in
         expr_let x96 := adc32 (x95₂, x10₂, x90₁) in
         expr_let x97 := adc32 (x96₂, x9₂, x91₁) in
         expr_let x98 := adc32 (x97₂, x8₂, x92₁) in
         expr_let x99 := add32 (x5₁, x93₁) in
         expr_let x100 := adc32 (x99₂, x4₁, x94₁) in
         expr_let x101 := adc32 (x100₂, x15₁, x95₁) in
         expr_let x102 := adc32 (x101₂, x14₁, x96₁) in
         expr_let x103 := adc32 (x102₂, x13₁, x97₁) in
         expr_let x104 := adc32 (x103₂, x13₂, x98₁) in
         expr_let x105 := add32 (x6₂, x99₁) in
         expr_let x106 := adc32 (x105₂, x5₂, x100₁) in
         expr_let x107 := adc32 (x106₂, x16₂, x101₁) in
         expr_let x108 := adc32 (x107₂, x15₂, x102₁) in
         expr_let x109 := adc32 (x108₂, x14₂, x103₁) in
         expr_let x110 := adc32 (x109₂, x6₁, x104₁) in
         expr_let x111 := add32 (x10₁, x105₁) in
         expr_let x112 := adc32 (x111₂, x9₁, x106₁) in
         expr_let x113 := adc32 (x112₂, x20₁, x107₁) in
         expr_let x114 := adc32 (x113₂, x19₁, x108₁) in
         expr_let x115 := adc32 (x114₂, x19₂, x109₁) in
         expr_let x116 := adc32 (x115₂, x11₁, x110₁) in
         expr_let x117 := add32 (x11₂, x111₁) in
         expr_let x118 := adc32 (x117₂, x10₂, x112₁) in
         expr_let x119 := adc32 (x118₂, x21₂, x113₁) in
         expr_let x120 := adc32 (x119₂, x20₂, x114₁) in
         expr_let x121 := adc32 (x120₂, x12₁, x115₁) in
         expr_let x122 := adc32 (x121₂, x12₂, x116₁) in
         expr_let x123 := add32 (x15₁, x117₁) in
         expr_let x124 := adc32 (x123₂, x14₁, x118₁) in
         expr_let x125 := adc32 (x124₂, x25₁, x119₁) in
         expr_let x126 := adc32 (x125₂, x25₂, x120₁) in
         expr_let x127 := adc32 (x126₂, x17₁, x121₁) in
         expr_let x128 := adc32 (x127₂, x16₁, x122₁) in
         expr_let x129 := add32 (x16₂, x123₁) in
         expr_let x130 := adc32 (x129₂, x15₂, x124₁) in
         expr_let x131 := adc32 (x130₂, x26₂, x125₁) in
         expr_let x132 := adc32 (x131₂, x18₁, x126₁) in
         expr_let x133 := adc32 (x132₂, x18₂, x127₁) in
         expr_let x134 := adc32 (x133₂, x17₂, x128₁) in
         expr_let x135 := add32 (x20₁, x129₁) in
         expr_let x136 := adc32 (x135₂, x19₁, x130₁) in
         expr_let x137 := adc32 (x136₂, x31₂, x131₁) in
         expr_let x138 := adc32 (x137₂, x23₁, x132₁) in
         expr_let x139 := adc32 (x138₂, x22₁, x133₁) in
         expr_let x140 := adc32 (x139₂, x21₁, x134₁) in
         expr_let x141 := add32 (x21₂, x135₁) in
         expr_let x142 := adc32 (x141₂, x20₂, x136₁) in
         expr_let x143 := adc32 (x142₂, x24₁, x137₁) in
         expr_let x144 := adc32 (x143₂, x24₂, x138₁) in
         expr_let x145 := adc32 (x144₂, x23₂, x139₁) in
         expr_let x146 := adc32 (x145₂, x22₂, x140₁) in
         expr_let x147 := add32 (x25₁, x141₁) in
         expr_let x148 := adc32 (x147₂, x25₂, x142₁) in
         expr_let x149 := adc32 (x148₂, x29₁, x143₁) in
         expr_let x150 := adc32 (x149₂, x28₁, x144₁) in
         expr_let x151 := adc32 (x150₂, x27₁, x145₁) in
         expr_let x152 := adc32 (x151₂, x26₁, x146₁) in
         expr_let x153 := add32 (x26₂, x147₁) in
         expr_let x154 := adc32 (x153₂, x30₁, x148₁) in
         expr_let x155 := adc32 (x154₂, x30₂, x149₁) in
         expr_let x156 := adc32 (x155₂, x29₂, x150₁) in
         expr_let x157 := adc32 (x156₂, x28₂, x151₁) in
         expr_let x158 := adc32 (x157₂, x27₂, x152₁) in
         expr_let x159 := add32 (x31₂, x153₁) in
         expr_let x160 := adc32 (x159₂, x35₁, x154₁) in
         expr_let x161 := adc32 (x160₂, x34₁, x155₁) in
         expr_let x162 := adc32 (x161₂, x33₁, x156₁) in
         expr_let x163 := adc32 (x162₂, x32₁, x157₁) in
         expr_let x164 := adc32 (x163₂, x31₁, x158₁) in
         [x159₁; x160₁; x161₁; x162₁; x163₁; x164₁]
     : Expr (type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
*)

End P192_32.

Module P384_32.
  Definition s := 2^384.
  Definition c :=  [(2^128, 1); (2^96, 1); (2^32,-1); (1,1)].
  Definition machine_wordsize := 32.
  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Depth 100000.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.
  Set Printing Depth 100000.

  Local Notation "'mul32' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint32, _)%core) @ (#Z_mul_split @ #(ident.Literal (t:=base.type.Z) 4294967296) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'add32' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) 4294967296) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adc32' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) 4294967296) @ c @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'sub32' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_sub_get_borrow @ #(ident.Literal (t:=base.type.Z) 4294967296) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'sbb32' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_sub_with_get_borrow @ #(ident.Literal (t:=base.type.Z) 4294967296) @ c @ x @ y))%expr (at level 50) : expr_scope.

  Print mulmod.


End P384_32.

(* TODO : Too slow! Many, many terms in this one. *)

Module P256_32.
  Definition s := 2^256.
  Definition c :=  [(2^224, 1); (2^192, -1); (2^96, -1); (1,1)].
  Definition machine_wordsize := 32.

  Derive mulmod
         SuchThat (SaturatedSolinas.rmulmod_correctT s c machine_wordsize mulmod)
         As mulmod_correct.
  Proof. Time solve_rmulmod machine_wordsize. Time Qed.

  Import PrintingNotations.
  Open Scope expr_scope.
  Set Printing Width 100000.

  Local Notation "'mul32' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint32, _)%core) @ (#Z_mul_split @ #(ident.Literal (t:=base.type.Z) 4294967296) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'add32' '(' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_add_get_carry @ #(ident.Literal (t:=base.type.Z) 4294967296) @ x @ y))%expr (at level 50) : expr_scope.
  Local Notation "'adc32' '(' c ',' x ',' y ')'" :=
    (#(Z_cast2 (uint32, bool)%core) @ (#Z_add_with_get_carry @ #(ident.Literal (t:=base.type.Z) 4294967296) @ c @ x @ y))%expr (at level 50) : expr_scope.

  (* Print is too slow *)

  Time Print mulmod.

  (*
mulmod =
fun var : type -> Type =>
λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
expr_let x1 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x2 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x3 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x4 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x5 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x6 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x7 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x8 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[7]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x9 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x10 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x11 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x12 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x13 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x14 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x15 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x16 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[6]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x17 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x18 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x19 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x20 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x21 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x22 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x23 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x24 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[5]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x25 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x26 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x27 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x28 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x29 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x30 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x31 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x32 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[4]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x33 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x34 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x35 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x36 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x37 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x38 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x39 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x40 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[3]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x41 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x42 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x43 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x44 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x45 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x46 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x47 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x48 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[2]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x49 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x50 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x51 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x52 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x53 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x54 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x55 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x56 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[1]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x57 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[7]])))%expr_pat in
expr_let x58 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[6]])))%expr_pat in
expr_let x59 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[5]])))%expr_pat in
expr_let x60 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[4]])))%expr_pat in
expr_let x61 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[3]])))%expr_pat in
expr_let x62 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[2]])))%expr_pat in
expr_let x63 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[1]])))%expr_pat in
expr_let x64 := (#(Z_cast2 (uint32, uint32)%core)%expr @ (#(Z_mul_split_concrete 4294967296)%expr @ (uint32)(x[[0]]) @ (uint32)(x0[[0]])))%expr_pat in
expr_let x65 := (#(Z_cast r[-4294967294 ~> 0])%expr @ (- x1₂))%expr_pat in
expr_let x66 := (#(Z_cast r[-4294967294 ~> 0])%expr @ (- x1₂))%expr_pat in
expr_let x67 := (#(Z_cast r[-4294967294 ~> 0])%expr @ (- x1₂))%expr_pat in
expr_let x68 := (#(Z_cast r[-4294967294 ~> 0])%expr @ (- x1₂))%expr_pat in
expr_let x69 := (#(Z_cast r[-4294967294 ~> 0])%expr @ (- x1₂))%expr_pat in
expr_let x70 := (#(Z_cast r[-4294967294 ~> 0])%expr @ (- x1₂))%expr_pat in
expr_let x71 := (#(Z_cast r[-4294967294 ~> 0])%expr @ (- x1₂))%expr_pat in
[...]
expr_let x2983 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_get_carry_concrete 4294967296)%expr @ x35₁ @ x2975₁))%expr_pat in
expr_let x2984 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2983₂ @ x34₁ @ x2976₁))%expr_pat in
expr_let x2985 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2984₂ @ x33₁ @ x2977₁))%expr_pat in
expr_let x2986 := (#(Z_cast2 (uint32, r[-1 ~> 1])%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2985₂ @ x826 @ x2978₁))%expr_pat in
expr_let x2987 := (#(Z_cast2 (uint32, r[-1 ~> 1])%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2986₂ @ x39₁ @ x2979₁))%expr_pat in
expr_let x2988 := (#(Z_cast2 (uint32, r[-1 ~> 1])%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2987₂ @ x38₁ @ x2980₁))%expr_pat in
expr_let x2989 := (#(Z_cast2 (uint32, r[-1 ~> 1])%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2988₂ @ x37₁ @ x2981₁))%expr_pat in
expr_let x2990 := (#(Z_cast2 (uint32, r[-1 ~> 1])%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2989₂ @ x36₁ @ x2982₁))%expr_pat in
expr_let x2991 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_get_carry_concrete 4294967296)%expr @ x36₂ @ x2983₁))%expr_pat in
expr_let x2992 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2991₂ @ x35₂ @ x2984₁))%expr_pat in
expr_let x2993 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2992₂ @ x34₂ @ x2985₁))%expr_pat in
expr_let x2994 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2993₂ @ x40₁ @ x2986₁))%expr_pat in
expr_let x2995 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2994₂ @ x40₂ @ x2987₁))%expr_pat in
expr_let x2996 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2995₂ @ x39₂ @ x2988₁))%expr_pat in
expr_let x2997 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2996₂ @ x38₂ @ x2989₁))%expr_pat in
expr_let x2998 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2997₂ @ x37₂ @ x2990₁))%expr_pat in
expr_let x2999 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_get_carry_concrete 4294967296)%expr @ x42₁ @ x2991₁))%expr_pat in
expr_let x3000 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x2999₂ @ x41₁ @ x2992₁))%expr_pat in
expr_let x3001 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3000₂ @ x41₂ @ x2993₁))%expr_pat in
expr_let x3002 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3001₂ @ x47₁ @ x2994₁))%expr_pat in
expr_let x3003 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3002₂ @ x46₁ @ x2995₁))%expr_pat in
expr_let x3004 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3003₂ @ x45₁ @ x2996₁))%expr_pat in
expr_let x3005 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3004₂ @ x44₁ @ x2997₁))%expr_pat in
expr_let x3006 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3005₂ @ x43₁ @ x2998₁))%expr_pat in
expr_let x3007 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_get_carry_concrete 4294967296)%expr @ x43₂ @ x2999₁))%expr_pat in
expr_let x3008 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3007₂ @ x42₂ @ x3000₁))%expr_pat in
expr_let x3009 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3008₂ @ x48₁ @ x3001₁))%expr_pat in
expr_let x3010 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3009₂ @ x48₂ @ x3002₁))%expr_pat in
expr_let x3011 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3010₂ @ x47₂ @ x3003₁))%expr_pat in
expr_let x3012 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3011₂ @ x46₂ @ x3004₁))%expr_pat in
expr_let x3013 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3012₂ @ x45₂ @ x3005₁))%expr_pat in
expr_let x3014 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3013₂ @ x44₂ @ x3006₁))%expr_pat in
expr_let x3015 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_get_carry_concrete 4294967296)%expr @ x49₁ @ x3007₁))%expr_pat in
expr_let x3016 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3015₂ @ x49₂ @ x3008₁))%expr_pat in
expr_let x3017 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3016₂ @ x55₁ @ x3009₁))%expr_pat in
expr_let x3018 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3017₂ @ x54₁ @ x3010₁))%expr_pat in
expr_let x3019 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3018₂ @ x53₁ @ x3011₁))%expr_pat in
expr_let x3020 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3019₂ @ x52₁ @ x3012₁))%expr_pat in
expr_let x3021 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3020₂ @ x51₁ @ x3013₁))%expr_pat in
expr_let x3022 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3021₂ @ x50₁ @ x3014₁))%expr_pat in
expr_let x3023 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_get_carry_concrete 4294967296)%expr @ x50₂ @ x3015₁))%expr_pat in
expr_let x3024 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3023₂ @ x56₁ @ x3016₁))%expr_pat in
expr_let x3025 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3024₂ @ x56₂ @ x3017₁))%expr_pat in
expr_let x3026 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3025₂ @ x55₂ @ x3018₁))%expr_pat in
expr_let x3027 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3026₂ @ x54₂ @ x3019₁))%expr_pat in
expr_let x3028 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3027₂ @ x53₂ @ x3020₁))%expr_pat in
expr_let x3029 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3028₂ @ x52₂ @ x3021₁))%expr_pat in
expr_let x3030 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3029₂ @ x51₂ @ x3022₁))%expr_pat in
expr_let x3031 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_get_carry_concrete 4294967296)%expr @ x57₂ @ x3023₁))%expr_pat in
expr_let x3032 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3031₂ @ x63₁ @ x3024₁))%expr_pat in
expr_let x3033 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3032₂ @ x62₁ @ x3025₁))%expr_pat in
expr_let x3034 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3033₂ @ x61₁ @ x3026₁))%expr_pat in
expr_let x3035 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3034₂ @ x60₁ @ x3027₁))%expr_pat in
expr_let x3036 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3035₂ @ x59₁ @ x3028₁))%expr_pat in
expr_let x3037 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3036₂ @ x58₁ @ x3029₁))%expr_pat in
expr_let x3038 := (#(Z_cast2 (uint32, bool)%core)%expr @ (#(Z_add_with_get_carry_concrete 4294967296)%expr @ x3037₂ @ x57₁ @ x3030₁))%expr_pat in
[x3031₁; x3032₁; x3033₁; x3034₁; x3035₁; x3036₁; x3037₁; x3038₁]
     : Expr (type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)) -> type.base (base.type.list (base.type.type_base base.type.Z)))%ptype
Finished transaction in 211.393 secs (210.924u,0.028s) (successful)
*)
End P256_32.
*)
