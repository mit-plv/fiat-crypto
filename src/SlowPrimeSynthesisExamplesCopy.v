Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Crypto.PushButtonSynthesis.SaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Crypto.Stringification.C.
Require Crypto.Stringification.Go.
Require Crypto.Stringification.Java.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Coq.ZArith.Znat.

Require Import Crypto.Util.Notations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations. Local Open Scope Z_scope.

Import
  AbstractInterpretation.Compilers
  Language.Compilers
  Language.API.Compilers.

Import Language.API.Compilers.API.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Existing Instance default_low_level_rewriter_method.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := None.
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.

Local Existing Instance default_output_options.

Module debugging_mul.
  Import Crypto.Arithmetic.Saturated.
  Import Stringification.C.
  Import Stringification.C.Compilers.
  Import Stringification.C.Compilers.ToString.

  Local Existing Instances ToString.C.OutputCAPI Pipeline.show_ErrorMessage.
  Local Instance : only_signed_opt := false.
  Local Instance : no_select_opt := false.
  Local Instance : static_opt := true.
  Local Instance : internal_static_opt := true.
  Local Instance : inline_opt := true.
  Local Instance : inline_internal_opt := true.
  Local Instance : use_mul_for_cmovznz_opt := false.
  Local Instance : emit_primitives_opt := true.
  Local Instance : should_split_mul_opt := false.
  Local Instance : should_split_multiret_opt := false.
  Local Instance : widen_carry_opt := false.
  Local Instance : widen_bytes_opt := true. (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)

  Let s := 2^256.
  Let c := [(1, 38)].
  Let machine_wordsize := 64.

  Let possible_values := prefix_with_carry [machine_wordsize].
  Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
  Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
  Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

  Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Let m : nat := Z.to_nat (2*n).

  Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
  Let boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat bound n.

  Let out_bound := Some r[0 ~> (2^(machine_wordsize*2) - 1)]%zrange.
  Let out_boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat out_bound n.

  Time Compute
       Show.show
       (Pipeline.BoundsPipelineToString
          "fiat" "mul"
          false
          false
          None
          possible_values
          machine_wordsize
          ltac:(let n := (eval cbv in n) in
                let m := (eval cbv in m) in
                let r := Reify (@Saturated.Rows.mul (weight machine_wordsize 1) (2^machine_wordsize) n m) in
                exact r)
                 (fun _ _ => [])
                 (Some boundsn, (Some boundsn, tt))
                 (Some boundsn, None)
                 (None, (None, tt))
                 (None, None)
         : Pipeline.ErrorT _).

End debugging_mul.

Module debugging_red.

  Import PreExtra.
  Import Util.LetIn.
  Import ZUtil.Definitions.
  Import Weight.

  Section solinas_reduction.

    Context weight {wprops : @weight_properties weight}.

    (* Definition sat_reduce base s c n (p : list (Z * Z)) := *)
    (*   let '(s', _) := Saturated.Rows.adjust_s weight (S (S n)) s in *)
    (*   let lo_hi := Associational.split s' p in *)
    (*   fst lo_hi ++ (Saturated.Associational.sat_mul_const base [(1, s'/s)] (Saturated.Associational.sat_mul_const base c (snd lo_hi))). *)

    Definition sat_mul_const_test s n (p : list (Z * Z)) (q : list Z) :=
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul_const s p q_a in
      let pq_r := Saturated.Rows.from_associational weight n pq_a in
      let pq_f := Saturated.Rows.flatten weight n pq_r in
      pq_f.

    Definition sat_mul_const_test2 s n (p : list (Z * Z)) (q : list Z) :=
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul_const s p q_a in
      let pq_r := Saturated.Rows.from_associational weight n pq_a in
      pq_r.

    (* Definition sat_reduce_positional base s c m n (p : list Z) := *)
    (*   let p_a := Positional.to_associational weight m p in *)
    (*   let r_a := sat_reduce base s c m p_a in *)
    (*   let r_r := Saturated.Rows.from_associational weight n r_a in *)
    (*   let r_f := Saturated.Rows.flatten weight n r_r in *)
    (*   r_f. *)

    Definition sat_reduce base s c n (p : list (Z * Z)) :=
      let '(s', _) := Saturated.Rows.adjust_s weight (S (S n)) s in
      let lo_hi := Associational.split s' p in
      let mul_residue := Saturated.Associational.sat_mul base [(1, s'/s)] c in
      fst lo_hi ++ (Saturated.Associational.sat_mul_const base mul_residue (snd lo_hi)).

    Definition repeat_sat_reduce base s c (p : list (Z * Z)) n :=
      fold_right (fun _ q => sat_reduce base s c n q) p (seq 0 n).

    Definition mulmod base s c n nreductions (p q : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let r_a := repeat_sat_reduce base s c pq_a nreductions in
      Saturated.Rows.flatten weight n (Saturated.Rows.from_associational weight n r_a).

  End solinas_reduction.

  Section __.

    Let s := 2^255.
    Let c := [(1, 19)].
    Let machine_wordsize := 64.
    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m : nat := 2 * n.
    Let nreductions : nat :=
          let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
          if Z.of_nat m - i <=? 1
          then n
          else Z.to_nat (Qceiling (Z.of_nat m / (Z.of_nat m - i - 1))).
    Let nreductions' : nat := nreductions * 2%nat.
    Compute nreductions.

    Let w : nat -> Z := weight machine_wordsize 1.
    Let base : Z := 2 ^ machine_wordsize.

    Compute (sat_mul_const_test w base 2 c [5; 5]).
    Compute (sat_mul_const_test2 w base 2 c [5; 5]).
    Compute (sat_mul_const_test w base 2 [(1, 2)] [5; 5]).

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let bounds : list (ZRange.type.option.interp base.type.Z)
        := repeat bound 1.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
        := repeat bound (n).
    Let in_boundsn : list (ZRange.type.option.interp base.type.Z)
        := repeat bound (2 * n).
    Let out_boundsn : list (ZRange.type.option.interp base.type.Z)
        := repeat bound n.

    Import Crypto.Arithmetic.Saturated.
    Import Stringification.C.
    Import Stringification.C.Compilers.
    Import Stringification.C.Compilers.ToString.

    Local Existing Instances ToString.C.OutputCAPI Pipeline.show_ErrorMessage.
    Local Instance : only_signed_opt := false.
    Local Instance : no_select_opt := false.
    Local Instance : static_opt := true.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : emit_primitives_opt := true.
    Local Instance : should_split_mul_opt := false.
    Local Instance : should_split_multiret_opt := false.
    Local Instance : widen_carry_opt := false.
    Local Instance : widen_bytes_opt := true. (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)

    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

    (* Time Compute *)
    (*      Show.show  *)
    (*      (Pipeline.BoundsPipelineToString *)
    (*         "fiat" "mul" *)
    (*         false (* subst01 *) *)
    (*         false (* inline *) *)
    (*         None (* fancy *) *)
    (*         possible_values *)
    (*         machine_wordsize *)
    (*         ltac:(let n := (eval cbv in n) in *)
    (*               let r := Reify (sat_mul_const_test (weight machine_wordsize 1) s n c) in *)
    (*               exact r) *)
    (*                (fun _ _ => []) *)
    (*                (Some boundsn, tt) *)
    (*                (Some boundsn, None) *)
    (*                (None, tt) *)
    (*                (None, None) *)
    (*        : Pipeline.ErrorT _). *)

    Time Compute
         Show.show
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false (* subst01 *)
            false (* inline *)
            None (* fancy *)
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) in
                  let nreductions' := (eval cbv in nreductions') in
                  let r := Reify (mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c n 3) in
                  exact r)
                   (fun _ _ => [])
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn, None)
                   (None, (None, tt))
                   (None, None)
           : Pipeline.ErrorT _).

    Time Compute
         Show.show
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false (* subst01 *)
            false (* inline *)
            None (* fancy *)
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) in
                  let nreductions' := (eval cbv in nreductions') in
                  let r := Reify (Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c n 3) in
                  exact r)
                   (fun _ _ => [])
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn, None)
                   (None, (None, tt))
                   (None, None)
           : Pipeline.ErrorT _).

    Time Compute
         Show.show
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false
            false
            None
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) in
                  let m := (eval cbv in m) in
                  let r := Reify (sat_reduce_positional (weight machine_wordsize 1) (2^machine_wordsize) s c m n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (2*n)), tt)
                   (Some (repeat bound n), None)
                   (None, tt)
                   (None, None)
           : Pipeline.ErrorT _).

  End __.

End debugging_red.

(**
     = "Success (""/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   out2: None
 */
static void mul(uint64_t out1[4], uint64_t* out2, const uint64_t arg1[4], const uint64_t arg2[4]) {
  uint64_t x1;
  uint64_t x2;
  uint64_t x3;
  uint64_t x4;
  uint64_t x5;
  uint64_t x6;
  uint64_t x7;
  uint64_t x8;
  uint64_t x9;
  uint64_t x10;
  uint64_t x11;
  uint64_t x12;
  uint64_t x13;
  uint64_t x14;
  uint64_t x15;
  uint64_t x16;
  uint64_t x17;
  uint64_t x18;
  uint64_t x19;
  uint64_t x20;
  uint64_t x21;
  uint64_t x22;
  uint64_t x23;
  uint64_t x24;
  uint64_t x25;
  uint64_t x26;
  uint64_t x27;
  uint64_t x28;
  uint64_t x29;
  uint64_t x30;
  uint64_t x31;
  uint64_t x32;
  uint64_t x33;
  uint64_t x34;
  uint64_t x35;
  uint64_t x36;
  uint64_t x37;
  uint64_t x38;
  uint64_t x39;
  uint64_t x40;
  uint64_t x41;
  uint64_t x42;
  uint64_t x43;
  uint64_t x44;
  uint64_t x45;
  uint64_t x46;
  uint64_t x47;
  uint64_t x48;
  uint64_t x49;
  uint64_t x50;
  uint64_t x51;
  uint64_t x52;
  uint64_t x53;
  uint64_t x54;
  uint64_t x55;
  uint64_t x56;
  uint64_t x57;
  uint64_t x58;
  uint64_t x59;
  uint64_t x60;
  uint64_t x61;
  uint64_t x62;
  uint64_t x63;
  uint64_t x64;
  uint64_t x65;
  uint64_t x66;
  uint64_t x67;
  fiatuint1 x68;
  uint64_t x69;
  uint64_t x70;
  fiatuint1 x71;
  uint64_t x72;
  fiatuint1 x73;
  uint64_t x74;
  uint64_t x75;
  fiatuint1 x76;
  uint64_t x77;
  fiatuint1 x78;
  uint64_t x79;
  fiatuint1 x80;
  uint64_t x81;
  fiatuint1 x82;
  uint64_t x83;
  fiatuint1 x84;
  uint64_t x85;
  fiatuint1 x86;
  uint64_t x87;
  fiatuint1 x88;
  uint64_t x89;
  fiatuint1 x90;
  uint64_t x91;
  fiatuint1 x92;
  uint64_t x93;
  fiatuint1 x94;
  uint64_t x95;
  fiatuint1 x96;
  uint64_t x97;
  fiatuint1 x98;
  uint64_t x99;
  fiatuint1 x100;
  uint64_t x101;
  fiatuint1 x102;
  uint64_t x103;
  fiatuint1 x104;
  uint64_t x105;
  fiatuint1 x106;
  uint64_t x107;
  fiatuint1 x108;
  uint64_t x109;
  fiatuint1 x110;
  uint64_t x111;
  fiatuint1 x112;
  uint64_t x113;
  fiatuint1 x114;
  uint64_t x115;
  fiatuint1 x116;
  uint64_t x117;
  fiatuint1 x118;
  uint64_t x119;
  fiatuint1 x120;
  uint64_t x121;
  fiatuint1 x122;
  uint64_t x123;
  fiatuint1 x124;
  uint64_t x125;
  fiatuint1 x126;
  uint64_t x127;
  fiatuint1 x128;
  uint64_t x129;
  fiatuint1 x130;
  uint64_t x131;
  fiatuint1 x132;
  uint64_t x133;
  fiatuint1 x134;
  uint64_t x135;
  fiatuint1 x136;
  uint64_t x137;
  fiatuint1 x138;
  uint64_t x139;
  fiatuint1 x140;
  uint64_t x141;
  fiatuint1 x142;
  uint64_t x143;
  fiatuint1 x144;
  uint64_t x145;
  fiatuint1 x146;
  uint64_t x147;
  fiatuint1 x148;
  uint64_t x149;
  fiatuint1 x150;
  uint64_t x151;
  fiatuint1 x152;
  uint64_t x153;
  fiatuint1 x154;
  uint64_t x155;
  fiatuint1 x156;
  uint64_t x157;
  fiatuint1 x158;
  uint64_t x159;
  fiatuint1 x160;
  uint64_t x161;
  fiatuint1 x162;
  uint64_t x163;
  fiatmulx_u64(&x1, &x2, (arg1[3]), (arg2[3]));
  fiatmulx_u64(&x3, &x4, (arg1[3]), (arg2[2]));
  fiatmulx_u64(&x5, &x6, (arg1[3]), (arg2[1]));
  fiatmulx_u64(&x7, &x8, (arg1[3]), (arg2[0]));
  fiatmulx_u64(&x9, &x10, (arg1[2]), (arg2[3]));
  fiatmulx_u64(&x11, &x12, (arg1[2]), (arg2[2]));
  fiatmulx_u64(&x13, &x14, (arg1[2]), (arg2[1]));
  fiatmulx_u64(&x15, &x16, (arg1[2]), (arg2[0]));
  fiatmulx_u64(&x17, &x18, (arg1[1]), (arg2[3]));
  fiatmulx_u64(&x19, &x20, (arg1[1]), (arg2[2]));
  fiatmulx_u64(&x21, &x22, (arg1[1]), (arg2[1]));
  fiatmulx_u64(&x23, &x24, (arg1[1]), (arg2[0]));
  fiatmulx_u64(&x25, &x26, (arg1[0]), (arg2[3]));
  fiatmulx_u64(&x27, &x28, (arg1[0]), (arg2[2]));
  fiatmulx_u64(&x29, &x30, (arg1[0]), (arg2[1]));
  fiatmulx_u64(&x31, &x32, (arg1[0]), (arg2[0]));
  fiatmulx_u64(&x33, &x34, UINT8_C(0x26), x2);
  fiatmulx_u64(&x35, &x36, UINT8_C(0x26), x1);
  fiatmulx_u64(&x37, &x38, UINT8_C(0x26), x4);
  fiatmulx_u64(&x39, &x40, UINT8_C(0x26), x3);
  fiatmulx_u64(&x41, &x42, UINT8_C(0x26), x6);
  fiatmulx_u64(&x43, &x44, UINT8_C(0x26), x5);
  fiatmulx_u64(&x45, &x46, UINT8_C(0x26), x8);
  fiatmulx_u64(&x47, &x48, UINT8_C(0x26), x10);
  fiatmulx_u64(&x49, &x50, UINT8_C(0x26), x9);
  fiatmulx_u64(&x51, &x52, UINT8_C(0x26), x12);
  fiatmulx_u64(&x53, &x54, UINT8_C(0x26), x11);
  fiatmulx_u64(&x55, &x56, UINT8_C(0x26), x14);
  fiatmulx_u64(&x57, &x58, UINT8_C(0x26), x18);
  fiatmulx_u64(&x59, &x60, UINT8_C(0x26), x17);
  fiatmulx_u64(&x61, &x62, UINT8_C(0x26), x20);
  fiatmulx_u64(&x63, &x64, UINT8_C(0x26), x26);
  fiatmulx_u64(&x65, &x66, UINT8_C(0x26), x34);
  fiataddcarryx_u64(&x67, &x68, 0x0, x32, x39);
  x69 = (x68 + x30);
  fiataddcarryx_u64(&x70, &x71, 0x0, x67, x41);
  fiataddcarryx_u64(&x72, &x73, x71, x69, 0x0);
  x74 = (x73 + x28);
  fiataddcarryx_u64(&x75, &x76, 0x0, x70, x44);
  fiataddcarryx_u64(&x77, &x78, x76, x72, x35);
  fiataddcarryx_u64(&x79, &x80, x78, x74, 0x0);
  fiataddcarryx_u64(&x81, &x82, 0x0, x75, x46);
  fiataddcarryx_u64(&x83, &x84, x82, x77, x37);
  fiataddcarryx_u64(&x85, &x86, x84, x79, 0x0);
  fiataddcarryx_u64(&x87, &x88, 0x0, x81, x49);
  fiataddcarryx_u64(&x89, &x90, x88, x83, x40);
  fiataddcarryx_u64(&x91, &x92, x90, x85, x33);
  fiataddcarryx_u64(&x93, &x94, 0x0, x87, x51);
  fiataddcarryx_u64(&x95, &x96, x94, x89, x42);
  fiataddcarryx_u64(&x97, &x98, x96, x91, x36);
  fiataddcarryx_u64(&x99, &x100, 0x0, x31, x65);
  fiataddcarryx_u64(&x101, &x102, x100, x93, x54);
  fiataddcarryx_u64(&x103, &x104, x102, x95, x47);
  fiataddcarryx_u64(&x105, &x106, x104, x97, x38);
  fiataddcarryx_u64(&x107, &x108, 0x0, x99, x43);
  fiataddcarryx_u64(&x109, &x110, x108, x101, x56);
  fiataddcarryx_u64(&x111, &x112, x110, x103, x50);
  fiataddcarryx_u64(&x113, &x114, x112, x105, x48);
  fiataddcarryx_u64(&x115, &x116, 0x0, x107, x45);
  fiataddcarryx_u64(&x117, &x118, x116, x109, x57);
  fiataddcarryx_u64(&x119, &x120, x118, x111, x52);
  fiataddcarryx_u64(&x121, &x122, x120, x113, x7);
  fiataddcarryx_u64(&x123, &x124, 0x0, x115, x53);
  fiataddcarryx_u64(&x125, &x126, x124, x117, x60);
  fiataddcarryx_u64(&x127, &x128, x126, x119, x58);
  fiataddcarryx_u64(&x129, &x130, x128, x121, x13);
  fiataddcarryx_u64(&x131, &x132, 0x0, x123, x55);
  fiataddcarryx_u64(&x133, &x134, x132, x125, x62);
  fiataddcarryx_u64(&x135, &x136, x134, x127, x15);
  fiataddcarryx_u64(&x137, &x138, x136, x129, x16);
  fiataddcarryx_u64(&x139, &x140, 0x0, x131, x59);
  fiataddcarryx_u64(&x141, &x142, x140, x133, x64);
  fiataddcarryx_u64(&x143, &x144, x142, x135, x21);
  fiataddcarryx_u64(&x145, &x146, x144, x137, x19);
  fiataddcarryx_u64(&x147, &x148, 0x0, x139, x61);
  fiataddcarryx_u64(&x149, &x150, x148, x141, x23);
  fiataddcarryx_u64(&x151, &x152, x150, x143, x24);
  fiataddcarryx_u64(&x153, &x154, x152, x145, x22);
  fiataddcarryx_u64(&x155, &x156, 0x0, x147, x63);
  fiataddcarryx_u64(&x157, &x158, x156, x149, x29);
  fiataddcarryx_u64(&x159, &x160, x158, x151, x27);
  fiataddcarryx_u64(&x161, &x162, x160, x153, x25);
  x163 = ((((((((((((uint64_t)x80 + x86) + (uint64_t)x92) + (uint64_t)x98) + (uint64_t)x106) + (uint64_t)x114) + (uint64_t)x122) + (uint64_t)x130) + (uint64_t)x138) + (uint64_t)x146) + (uint64_t)x154) + (uint64_t)x162);
  out1[0] = x155;
  out1[1] = x157;
  out1[2] = x159;
  out1[3] = x161;
  *out2 = x163;
}"", {| bitwidths_used := [uint1, uint64] ; addcarryx_lg_splits := [64] ; mulx_lg_splits := [64] ; cmovznz_bitwidths := [] ; value_barrier_bitwidths := [] ; typedefs_used := [] |})"
     : string
Finished transaction in 3.993 secs (3.94u,0.009s) (successful)
**)
