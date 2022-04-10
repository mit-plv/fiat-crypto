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

Module compiling_mul.

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

End compiling_mul.

Module compiling_reduce_flatten.

  Import PreExtra.
  Import Util.LetIn.
  Import ZUtil.Definitions.
  Import Weight.

  Let s := 2^255.
  Let c := [(1, 19)].
  Let machine_wordsize := 64.
  Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
  Let m : nat := 2 * n.
  Let w : nat -> Z := weight machine_wordsize 1.
  Let base : Z := 2 ^ machine_wordsize.

  Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
  Let boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat bound (n).

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

  Section single_reduction.

    Context weight {wprops : @weight_properties weight}.

    Definition sat_reduce base s c n (p : list (Z * Z)) :=
      let '(s', _) := Saturated.Rows.adjust_s weight (S (S n)) s in
      let lo_hi := Associational.split s' p in
      let coef := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let hi := Saturated.Associational.sat_mul_const base coef (snd lo_hi) in
      let r := (fst lo_hi) ++ hi in
      r.

    (* n is input width *)
    Definition reduce1 base s c n (p : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let r_a := sat_reduce base s c n p_a in
      let r_rows := Saturated.Rows.from_associational weight n r_a in
      let r_flat := Saturated.Rows.flatten weight n r_rows in
      fst r_flat.

    Definition reduce base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) p in
      let r2 := reduce1 base s c (2*n) (r1) in
      let r3 := reduce1 base s c (2*n) (r2) in
      r3.

    Definition reduce' base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) p in
      let r2 := reduce1 base s c (2*n) (r1) in
      let r3 := reduce1 base s c (2*n) (r2) in
      r3.

    Definition mul_no_reduce base n (p q : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      fst pq.

    Definition mulmod base s c n (p q : list Z) :=
      let prod := mul_no_reduce base n p q in
      let red := reduce base s c n prod in
      red.

  End single_reduction.

  Let v := (2^64-1).
  Let p := repeat v (2*n).
  Let r' := reduce' w base s c n p.
  Compute r'.

  Let out_boundsn := (repeat bound n) ++
                                      [Some r[0~>0]%zrange] ++
                                      (repeat (Some r[0~>0]%zrange) (n-1)).
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
                let r := Reify (reduce' w base s c n) in
                exact r)
                 (fun _ _ => [])
                 (Some (repeat bound (2*n)), tt)
                 (Some out_boundsn)
                 (None, tt)
                 (None)
         : Pipeline.ErrorT _).

(* Time Compute
       Show.show
       (Pipeline.BoundsPipelineToString
          "fiat" "mul"
          false
          false
          None
          possible_values
          machine_wordsize
          ltac:(let n := (eval cbv in n) in
                let r := Reify (mulmod w base s c (2*n)) in
                exact r)
                 (fun _ _ => [])
                 (Some (repeat bound (2*n)), (Some (repeat bound (2*n)), tt))
                 (None, None)
                 (None, (None, tt))
                 (None, None)
         : Pipeline.ErrorT _). *)

  (*
     = "Success (""/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0x1], [0x0 ~> 0x0], [0x0 ~> 0x0], [0x0 ~> 0x0]]
 */
static void mul(uint64_t out1[8], const uint64_t arg1[8]) {
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
  fiatuint1 x14;
  uint64_t x15;
  fiatuint1 x16;
  uint64_t x17;
  fiatuint1 x18;
  uint64_t x19;
  uint64_t x20;
  fiatuint1 x21;
  uint64_t x22;
  fiatuint1 x23;
  uint64_t x24;
  fiatuint1 x25;
  uint64_t x26;
  fiatuint1 x27;
  uint64_t x28;
  uint64_t x29;
  uint64_t x30;
  uint64_t x31;
  fiatuint1 x32;
  uint64_t x33;
  fiatuint1 x34;
  uint64_t x35;
  fiatuint1 x36;
  uint64_t x37;
  fiatuint1 x38;
  uint64_t x39;
  uint64_t x40;
  uint64_t x41;
  fiatuint1 x42;
  uint64_t x43;
  fiatuint1 x44;
  uint64_t x45;
  fiatuint1 x46;
  uint64_t x47;
  fiatuint1 x48;
  fiatmulx_u64(&x1, &x2, UINT8_C(0x26), (arg1[7]));
  fiatmulx_u64(&x3, &x4, UINT8_C(0x26), (arg1[6]));
  fiatmulx_u64(&x5, &x6, UINT8_C(0x26), (arg1[5]));
  fiatmulx_u64(&x7, &x8, UINT8_C(0x26), (arg1[4]));
  x9 = (arg1[3]);
  x10 = (arg1[2]);
  x11 = (arg1[1]);
  x12 = (arg1[0]);
  fiataddcarryx_u64(&x13, &x14, 0x0, x11, x5);
  fiataddcarryx_u64(&x15, &x16, x14, x10, x3);
  fiataddcarryx_u64(&x17, &x18, x16, x9, x1);
  x19 = (x18 + x2);
  fiataddcarryx_u64(&x20, &x21, 0x0, x12, x7);
  fiataddcarryx_u64(&x22, &x23, x21, x13, x8);
  fiataddcarryx_u64(&x24, &x25, x23, x15, x6);
  fiataddcarryx_u64(&x26, &x27, x25, x17, x4);
  x28 = (x27 + x19);
  fiatmulx_u64(&x29, &x30, UINT8_C(0x26), x28);
  fiataddcarryx_u64(&x31, &x32, 0x0, x20, x29);
  fiataddcarryx_u64(&x33, &x34, x32, x22, 0x0);
  fiataddcarryx_u64(&x35, &x36, x34, x24, 0x0);
  fiataddcarryx_u64(&x37, &x38, x36, x26, 0x0);
  fiatmulx_u64(&x39, &x40, UINT8_C(0x26), x38);
  fiataddcarryx_u64(&x41, &x42, 0x0, x31, x39);
  fiataddcarryx_u64(&x43, &x44, x42, x33, 0x0);
  fiataddcarryx_u64(&x45, &x46, x44, x35, 0x0);
  fiataddcarryx_u64(&x47, &x48, x46, x37, 0x0);
  out1[0] = x41;
  out1[1] = x43;
  out1[2] = x45;
  out1[3] = x47;
  out1[4] = x48;
  out1[5] = 0x0;
  out1[6] = 0x0;
  out1[7] = 0x0;
}"", {| bitwidths_used := [uint1, uint64] ; addcarryx_lg_splits := [64] ; mulx_lg_splits := [64] ; cmovznz_bitwidths := [] ; value_barrier_bitwidths := [] ; typedefs_used := [] |})"
     : string
Finished transaction in 4.122 secs (4.07u,0.05s) (successful)
*)

End compiling_reduce_flatten.

Module compiling_red.

  Import PreExtra.
  Import Util.LetIn.
  Import ZUtil.Definitions.
  Import Weight.

  Section solinas_reduction.

    Context weight {wprops : @weight_properties weight}.

    Definition sat_reduce base s c n (p : list (Z * Z)) :=
      let '(s', _) := Saturated.Rows.adjust_s weight (S (S n)) s in
      let lo_hi := Associational.split s' p in
      let mul_residue := Saturated.Associational.sat_mul base [(1, s'/s)] c in
      fst lo_hi ++ (Saturated.Associational.sat_mul_const base mul_residue (snd lo_hi)).

    Definition flatten_to_positional (p : list Z * Z) :=
      fst p ++ [snd p].

    Definition sat_reduce' base s c n (p : list (Z * Z)) :=
      let '(s', _) := Saturated.Rows.adjust_s weight (S (S n)) s in
      let lo_hi := Associational.split s' p in
      let v := Saturated.Associational.sat_mul base [(1, s'/s)] c in
      let hi := Saturated.Associational.sat_mul base v (snd lo_hi) in
      let r := fst lo_hi ++ hi in
      r.

    Definition mul_no_reduce base n (p q : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      fst pq.

    Definition reduce_flatten base s c n nreductions (p : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let r_a := sat_reduce' base s c nreductions p_a in
      let r_rows := Saturated.Rows.from_associational weight n r_a in
      let r_flat := Saturated.Rows.flatten weight n r_rows in
      fst r_flat.

    Definition repeat_reduce_flatten base s c n nreductions (p : list Z) :=
      fold_right (fun _ q => reduce_flatten base s c n nreductions q) p (seq 0 nreductions).

    Definition reduce_product base s c n m nreductions (p : list Z) :=
      let r := repeat_reduce_flatten base s c n nreductions p in
      let r_a := Positional.to_associational weight n r in
      let r_r := Saturated.Rows.from_associational weight m r_a in
      let r_f := Saturated.Rows.flatten weight m r_r in
      fst r_f.

    Definition mulmod base s c n nreductions (p q : list Z) :=
      let pq := mul_no_reduce base n p q in
      let pq_r := reduce_product base s c (2*n) n nreductions pq in
      pq_r.

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
    Compute nreductions.
    Let w : nat -> Z := weight machine_wordsize 1.
    Let base : Z := 2 ^ machine_wordsize.

    Let v := 2^64-1.
    Let p := repeat v n.
    Let q := repeat v n.
    Let pq_nor := mul_no_reduce w base n p q.
    Let pq_1 := (reduce_flatten w base s c 8 3 pq_nor).
    Let pq_2 := (reduce_flatten w base s c 8 3 pq_1).
    Let pq_3 := (reduce_flatten w base s c 8 3 pq_2).
    Compute pq_nor.
    Compute pq_1.
    Compute pq_2.
    Compute pq_3.
    Let pq_red := (reduce_product w base s c (2*n) n 3 pq_nor).
    Compute pq_red.
    Let pq := mulmod w base s c n 3 p q.
    Compute pq.

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
        := repeat bound (n).

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
    (*               let r := Reify (mulmod w base s c n 5) in *)
    (*               exact r) *)
    (*                (fun _ _ => []) *)
    (*                (Some boundsn, (Some boundsn, tt)) *)
    (*                (Some boundsn, None) *)
    (*                (None, (None, tt)) *)
    (*                (None, None) *)
    (*        : Pipeline.ErrorT _). *)

    (* Time Compute *)
    (*      Show.show *)
    (*      (Pipeline.BoundsPipelineToString *)
    (*         "fiat" "mul" *)
    (*         false *)
    (*         false *)
    (*         None *)
    (*         possible_values *)
    (*         machine_wordsize *)
    (*         ltac:(let n := (eval cbv in n) in *)
    (*               let r := Reify (reduce_flatten w base s c (2*n) 3) in *)
    (*               exact r) *)
    (*                (fun _ _ => []) *)
    (*                (Some (repeat bound (2*n)), tt) *)
    (*                (Some (repeat bound (2*n))) *)
    (*                (None, tt) *)
    (*                (None) *)
    (*        : Pipeline.ErrorT _). *)

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
                  let r := Reify (reduce_product w base s c (2*n) n 3) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (2*n)), tt)
                   (Some boundsn)
                   (None, tt)
                   (None)
           : Pipeline.ErrorT _).

  End __.

End compiling_red.
