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

    (*
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
      pq_r. *)

    Definition sat_reduce base s c n (p : list (Z * Z)) :=
      let '(s', _) := Saturated.Rows.adjust_s weight (S (S n)) s in
      let lo_hi := Associational.split s' p in
      let mul_residue := Saturated.Associational.sat_mul base [(1, s'/s)] c in
      fst lo_hi ++ (Saturated.Associational.sat_mul_const base mul_residue (snd lo_hi)).

    Definition repeat_sat_reduce base s c (p : list (Z * Z)) n :=
      fold_right (fun _ q => sat_reduce base s c n q) p (seq 0 n).

    Definition mul_no_reduce base n (p q : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      pq.

    Definition reduce_double_wide base s c n m nreductions (p : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let r_a := repeat_sat_reduce base s c p_a nreductions in
      let r_rows := Saturated.Rows.from_associational weight m r_a in
      let r_flat := Saturated.Rows.flatten weight m r_rows in
      r_flat.

    Definition mulmod base s c n nreductions (p q : list Z) :=
      let pq := mul_no_reduce base n p q in
      let pq_f := fst pq in
      let pq_r := reduce_double_wide base s c (2*n) n nreductions pq_f in
      pq_r.
(*      let pq_f := fst pq in
      let pq_a' := Positional.to_associational weight (2*n) pq_f in
      let r_a := Saturated.Rows.repeat_sat_reduce weight base s c pq_a' nreductions in
      Saturated.Rows.flatten weight n (Saturated.Rows.from_associational weight n r_a). *)

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

    Let v : Z := 2^64 - 1.

    Let p : list Z := (repeat v n).
    Let q : list Z := (repeat v n).

    Let pq : list Z * Z:= mul_no_reduce w base n p q.
    Compute p.
    Compute pq.
    Compute (Positional.eval w n p).
    Compute (Positional.eval w n q).
    Compute (mul_no_reduce w base n p q).
    Compute (mulmod w base s c n nreductions p q).
    Compute (let p_a := Positional.to_associational w 2 p in
             let q_a := Positional.to_associational w 2 q in
             let pq_a := Saturated.Associational.sat_mul base p_a q_a in
             let pq_p := Positional.from_associational w 5 pq_a in
             pq_p).

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

    (* compiling standalone reduce *)
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
                  let r := Reify (reduce_double_wide (weight machine_wordsize 1)
                                                     (2^machine_wordsize)
                                                     s c (2*n) n 3) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (2*n)), tt)
                   (Some boundsn, None)
                   (None, tt)
                   (None, None)
           : Pipeline.ErrorT _).

  End __.

End debugging_red.

(*
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
  fiatuint1 x34;
  uint64_t x35;
  fiatuint1 x36;
  uint64_t x37;
  uint64_t x38;
  fiatuint1 x39;
  uint64_t x40;
  fiatuint1 x41;
  uint64_t x42;
  fiatuint1 x43;
  uint64_t x44;
  uint64_t x45;
  fiatuint1 x46;
  uint64_t x47;
  fiatuint1 x48;
  uint64_t x49;
  fiatuint1 x50;
  uint64_t x51;
  fiatuint1 x52;
  uint64_t x53;
  fiatuint1 x54;
  uint64_t x55;
  uint64_t x56;
  fiatuint1 x57;
  uint64_t x58;
  fiatuint1 x59;
  uint64_t x60;
  fiatuint1 x61;
  uint64_t x62;
  fiatuint1 x63;
  uint64_t x64;
  fiatuint1 x65;
  uint64_t x66;
  fiatuint1 x67;
  uint64_t x68;
  fiatuint1 x69;
  uint64_t x70;
  fiatuint1 x71;
  uint64_t x72;
  fiatuint1 x73;
  uint64_t x74;
  fiatuint1 x75;
  uint64_t x76;
  fiatuint1 x77;
  uint64_t x78;
  fiatuint1 x79;
  uint64_t x80;
  fiatuint1 x81;
  uint64_t x82;
  fiatuint1 x83;
  uint64_t x84;
  fiatuint1 x85;
  uint64_t x86;
  fiatuint1 x87;
  uint64_t x88;
  fiatuint1 x89;
  uint64_t x90;
  fiatuint1 x91;
  uint64_t x92;
  fiatuint1 x93;
  uint64_t x94;
  fiatuint1 x95;
  uint64_t x96;
  uint64_t x97;
  uint64_t x98;
  uint64_t x99;
  uint64_t x100;
  uint64_t x101;
  uint64_t x102;
  uint64_t x103;
  uint64_t x104;
  uint64_t x105;
  uint64_t x106;
  fiatuint1 x107;
  uint64_t x108;
  fiatuint1 x109;
  uint64_t x110;
  fiatuint1 x111;
  uint64_t x112;
  fiatuint1 x113;
  uint64_t x114;
  fiatuint1 x115;
  uint64_t x116;
  fiatuint1 x117;
  uint64_t x118;
  fiatuint1 x119;
  uint64_t x120;
  fiatuint1 x121;
  uint64_t x122;
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
  fiataddcarryx_u64(&x33, &x34, 0x0, x28, x7);
  fiataddcarryx_u64(&x35, &x36, x34, x26, x5);
  x37 = (x36 + x18);
  fiataddcarryx_u64(&x38, &x39, 0x0, x33, x13);
  fiataddcarryx_u64(&x40, &x41, x39, x35, x8);
  fiataddcarryx_u64(&x42, &x43, x41, x37, 0x0);
  x44 = (x43 + x10);
  fiataddcarryx_u64(&x45, &x46, 0x0, x30, x15);
  fiataddcarryx_u64(&x47, &x48, x46, x38, x16);
  fiataddcarryx_u64(&x49, &x50, x48, x40, x11);
  fiataddcarryx_u64(&x51, &x52, x50, x42, x3);
  fiataddcarryx_u64(&x53, &x54, x52, x44, 0x0);
  x55 = (x54 + x2);
  fiataddcarryx_u64(&x56, &x57, 0x0, x45, x21);
  fiataddcarryx_u64(&x58, &x59, x57, x47, x19);
  fiataddcarryx_u64(&x60, &x61, x59, x49, x14);
  fiataddcarryx_u64(&x62, &x63, x61, x51, x6);
  fiataddcarryx_u64(&x64, &x65, x63, x53, 0x0);
  fiataddcarryx_u64(&x66, &x67, x65, x55, 0x0);
  fiataddcarryx_u64(&x68, &x69, 0x0, x32, x23);
  fiataddcarryx_u64(&x70, &x71, x69, x56, x24);
  fiataddcarryx_u64(&x72, &x73, x71, x58, x22);
  fiataddcarryx_u64(&x74, &x75, x73, x60, x17);
  fiataddcarryx_u64(&x76, &x77, x75, x62, x9);
  fiataddcarryx_u64(&x78, &x79, x77, x64, x1);
  fiataddcarryx_u64(&x80, &x81, x79, x66, 0x0);
  fiataddcarryx_u64(&x82, &x83, 0x0, x68, x29);
  fiataddcarryx_u64(&x84, &x85, x83, x70, x27);
  fiataddcarryx_u64(&x86, &x87, x85, x72, x25);
  fiataddcarryx_u64(&x88, &x89, x87, x74, x20);
  fiataddcarryx_u64(&x90, &x91, x89, x76, x12);
  fiataddcarryx_u64(&x92, &x93, x91, x78, x4);
  fiataddcarryx_u64(&x94, &x95, x93, x80, 0x0);
  fiatmulx_u64(&x96, &x97, UINT8_C(0x26), x94);
  fiatmulx_u64(&x98, &x99, UINT8_C(0x26), x92);
  fiatmulx_u64(&x100, &x101, UINT8_C(0x26), x90);
  fiatmulx_u64(&x102, &x103, UINT8_C(0x26), x88);
  fiatmulx_u64(&x104, &x105, UINT8_C(0x26), x97);
  fiataddcarryx_u64(&x106, &x107, 0x0, x31, x104);
  fiataddcarryx_u64(&x108, &x109, x107, x82, x100);
  fiataddcarryx_u64(&x110, &x111, x109, x84, x98);
  fiataddcarryx_u64(&x112, &x113, x111, x86, x96);
  fiataddcarryx_u64(&x114, &x115, 0x0, x106, x102);
  fiataddcarryx_u64(&x116, &x117, x115, x108, x103);
  fiataddcarryx_u64(&x118, &x119, x117, x110, x101);
  fiataddcarryx_u64(&x120, &x121, x119, x112, x99);
  x122 = ((uint64_t)x113 + x121);
  out1[0] = x114;
  out1[1] = x116;
  out1[2] = x118;
  out1[3] = x120;
  *out2 = x122;
}"", {| bitwidths_used := [uint1, uint64] ; addcarryx_lg_splits := [64] ; mulx_lg_splits := [64] ; cmovznz_bitwidths := [] ; value_barrier_bitwidths := [] ; typedefs_used := [] |})"
     : string
Finished transaction in 5.047 secs (5.032u,0.009s) (successful)
*)

(*
"Success (""/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   out2: None
 */
static void mul(uint64_t out1[4], uint64_t* out2, const uint64_t arg1[8]) {
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
  fiatuint1 x16;
  uint64_t x17;
  fiatuint1 x18;
  uint64_t x19;
  fiatuint1 x20;
  uint64_t x21;
  fiatuint1 x22;
  uint64_t x23;
  fiatuint1 x24;
  uint64_t x25;
  fiatuint1 x26;
  uint64_t x27;
  fiatuint1 x28;
  uint64_t x29;
  fiatuint1 x30;
  uint64_t x31;
  fiatmulx_u64(&x1, &x2, UINT8_C(0x26), (arg1[7]));
  fiatmulx_u64(&x3, &x4, UINT8_C(0x26), (arg1[6]));
  fiatmulx_u64(&x5, &x6, UINT8_C(0x26), (arg1[5]));
  fiatmulx_u64(&x7, &x8, UINT8_C(0x26), (arg1[4]));
  fiatmulx_u64(&x9, &x10, UINT8_C(0x26), x2);
  x11 = (arg1[3]);
  x12 = (arg1[2]);
  x13 = (arg1[1]);
  x14 = (arg1[0]);
  fiataddcarryx_u64(&x15, &x16, 0x0, x14, x9);
  fiataddcarryx_u64(&x17, &x18, x16, x13, x5);
  fiataddcarryx_u64(&x19, &x20, x18, x12, x3);
  fiataddcarryx_u64(&x21, &x22, x20, x11, x1);
  fiataddcarryx_u64(&x23, &x24, 0x0, x15, x7);
  fiataddcarryx_u64(&x25, &x26, x24, x17, x8);
  fiataddcarryx_u64(&x27, &x28, x26, x19, x6);
  fiataddcarryx_u64(&x29, &x30, x28, x21, x4);
  x31 = ((uint64_t)x22 + x30);
  out1[0] = x23;
  out1[1] = x25;
  out1[2] = x27;
  out1[3] = x29;
  *out2 = x31;
}"", {| bitwidths_used := [uint1, uint64] ; addcarryx_lg_splits := [64] ; mulx_lg_splits := [64] ; cmovznz_bitwidths := [] ; value_barrier_bitwidths := [] ; typedefs_used := [] |})"
     : string
Finished transaction in 2.767 secs (2.76u,0.s) (successful)
*)
