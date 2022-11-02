Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.SolinasReduction.
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
Require Import Crypto.Util.DebugMonad.
Require Import Crypto.Util.ZUtil.ModInv.

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

Local Existing Instance default_translate_to_fancy.
Local Existing Instances
      Primitives.Options.default_PipelineOptions
      Primitives.Options.default_PipelineToStringOptions
      Primitives.Options.default_SynthesisOptions
| 100.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.

Module debugging_solinas_reduction.

  Import SolinasReduction.SolinasReduction.

  Section __.

    Context (machine_wordsize := 64)
            (weight := UniformWeight.uweight machine_wordsize)
            (up_bound := 2 ^ (machine_wordsize / 4))
            {wprops : @weight_properties weight}.

    Definition dual_map {A B : Type} (f : A -> B -> bool) (l1 : list A) (l2 : list B) :=
      map (fun x => (f (fst x) (snd x))) (combine l1 l2).
    Definition fold_andb_map' {A B : Type} (f : A -> B -> bool) (ls1 : list A) (ls2 : list B) :=
      fold_right andb true (dual_map f ls1 ls2).
    Definition is_bounded_by bounds ls :=
      fold_andb_map' (fun r v'' => (fst r <=? v'') && (v'' <=? snd r)) bounds ls.

  End __.

  Section compile.

    Let s := 2^255.
    Let c := [(1, 19)].
    Let machine_wordsize := 64.
    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m : nat := 2 * n.
    Let w : nat -> Z := weight machine_wordsize 1.
    Let base : Z := 2 ^ machine_wordsize.

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let bound' := Some r[0 ~> (2^machine_wordsize +39)]%zrange.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
        := repeat bound (n).

    Import Stringification.C.Compilers.
    Import Stringification.C.Compilers.ToString.

    Local Existing Instances ToString.C.OutputCAPI Pipeline.show_ErrorMessage.

    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

    Let bounds := repeat bound n ++ [Some r[0 ~> 1]%zrange].
    Let bound1 := Some r[0~>1]%zrange.

    Time Compute
         Show.show
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false
            false
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) in
                  let r := Reify (reduce3 base s c n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (n) ++ [bound1]), tt)
                   (Some (repeat bound (n)))
                   (None, tt)
                   (None)
           : Pipeline.ErrorT _).

    Time Compute
         Show.show
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false
            false
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) in
                  let r := Reify (mulmod base s c n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (n)), (Some (repeat bound (n)), tt))
                   (Some (repeat bound (n)))
                   (None, (None, tt))
                   (None)
           : Pipeline.ErrorT _).
(*
/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: None
 */
void f(uint128 out1[4], const uint64_t arg1[4], const uint64_t arg2[4]) {
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
  uint1 x34;
  uint64_t x35;
  uint1 x36;
  uint64_t x37;
  uint64_t x38;
  uint1 x39;
  uint64_t x40;
  uint1 x41;
  uint64_t x42;
  uint1 x43;
  uint64_t x44;
  uint64_t x45;
  uint1 x46;
  uint64_t x47;
  uint1 x48;
  uint64_t x49;
  uint1 x50;
  uint64_t x51;
  uint1 x52;
  uint64_t x53;
  uint1 x54;
  uint64_t x55;
  uint64_t x56;
  uint1 x57;
  uint64_t x58;
  uint1 x59;
  uint64_t x60;
  uint1 x61;
  uint64_t x62;
  uint1 x63;
  uint64_t x64;
  uint1 x65;
  uint64_t x66;
  uint1 x67;
  uint64_t x68;
  uint1 x69;
  uint64_t x70;
  uint1 x71;
  uint64_t x72;
  uint1 x73;
  uint64_t x74;
  uint1 x75;
  uint64_t x76;
  uint1 x77;
  uint64_t x78;
  uint1 x79;
  uint64_t x80;
  uint1 x81;
  uint64_t x82;
  uint1 x83;
  uint64_t x84;
  uint1 x85;
  uint64_t x86;
  uint1 x87;
  uint64_t x88;
  uint1 x89;
  uint64_t x90;
  uint1 x91;
  uint64_t x92;
  uint1 x93;
  uint64_t x94;
  uint1 x95;
  uint64_t x96;
  uint64_t x97;
  uint64_t x98;
  uint64_t x99;
  uint64_t x100;
  uint64_t x101;
  uint64_t x102;
  uint64_t x103;
  uint64_t x104;
  uint1 x105;
  uint64_t x106;
  uint1 x107;
  uint64_t x108;
  uint1 x109;
  uint8_t x110;
  uint64_t x111;
  uint1 x112;
  uint64_t x113;
  uint1 x114;
  uint64_t x115;
  uint1 x116;
  uint64_t x117;
  uint1 x118;
  uint8_t x119;
  uint64_t x120;
  uint64_t x121;
  uint64_t x122;
  uint1 x123;
  uint64_t x124;
  uint1 x125;
  uint64_t x126;
  uint1 x127;
  uint64_t x128;
  uint1 x129;
  uint8_t x130;
  uint128 x131;
  mulx_u64(&x1, &x2, (arg1[3]), (arg2[3]));
  mulx_u64(&x3, &x4, (arg1[3]), (arg2[2]));
  mulx_u64(&x5, &x6, (arg1[3]), (arg2[1]));
  mulx_u64(&x7, &x8, (arg1[3]), (arg2[0]));
  mulx_u64(&x9, &x10, (arg1[2]), (arg2[3]));
  mulx_u64(&x11, &x12, (arg1[2]), (arg2[2]));
  mulx_u64(&x13, &x14, (arg1[2]), (arg2[1]));
  mulx_u64(&x15, &x16, (arg1[2]), (arg2[0]));
  mulx_u64(&x17, &x18, (arg1[1]), (arg2[3]));
  mulx_u64(&x19, &x20, (arg1[1]), (arg2[2]));
  mulx_u64(&x21, &x22, (arg1[1]), (arg2[1]));
  mulx_u64(&x23, &x24, (arg1[1]), (arg2[0]));
  mulx_u64(&x25, &x26, (arg1[0]), (arg2[3]));
  mulx_u64(&x27, &x28, (arg1[0]), (arg2[2]));
  mulx_u64(&x29, &x30, (arg1[0]), (arg2[1]));
  mulx_u64(&x31, &x32, (arg1[0]), (arg2[0]));
  addcarryx_u64(&x33, &x34, 0x0, x28, x7);
  addcarryx_u64(&x35, &x36, x34, x26, x5);
  x37 = (x36 + x18);
  addcarryx_u64(&x38, &x39, 0x0, x33, x13);
  addcarryx_u64(&x40, &x41, x39, x35, x8);
  addcarryx_u64(&x42, &x43, x41, x37, 0x0);
  x44 = (x43 + x10);
  addcarryx_u64(&x45, &x46, 0x0, x30, x15);
  addcarryx_u64(&x47, &x48, x46, x38, x16);
  addcarryx_u64(&x49, &x50, x48, x40, x11);
  addcarryx_u64(&x51, &x52, x50, x42, x3);
  addcarryx_u64(&x53, &x54, x52, x44, 0x0);
  x55 = (x54 + x2);
  addcarryx_u64(&x56, &x57, 0x0, x45, x21);
  addcarryx_u64(&x58, &x59, x57, x47, x19);
  addcarryx_u64(&x60, &x61, x59, x49, x14);
  addcarryx_u64(&x62, &x63, x61, x51, x6);
  addcarryx_u64(&x64, &x65, x63, x53, 0x0);
  addcarryx_u64(&x66, &x67, x65, x55, 0x0);
  addcarryx_u64(&x68, &x69, 0x0, x32, x23);
  addcarryx_u64(&x70, &x71, x69, x56, x24);
  addcarryx_u64(&x72, &x73, x71, x58, x22);
  addcarryx_u64(&x74, &x75, x73, x60, x17);
  addcarryx_u64(&x76, &x77, x75, x62, x9);
  addcarryx_u64(&x78, &x79, x77, x64, x1);
  addcarryx_u64(&x80, &x81, x79, x66, 0x0);
  addcarryx_u64(&x82, &x83, 0x0, x68, x29);
  addcarryx_u64(&x84, &x85, x83, x70, x27);
  addcarryx_u64(&x86, &x87, x85, x72, x25);
  addcarryx_u64(&x88, &x89, x87, x74, x20);
  addcarryx_u64(&x90, &x91, x89, x76, x12);
  addcarryx_u64(&x92, &x93, x91, x78, x4);
  addcarryx_u64(&x94, &x95, x93, x80, 0x0);
  mulx_u64(&x96, &x97, UINT8_C(0x26), x94);
  mulx_u64(&x98, &x99, UINT8_C(0x26), x92);
  mulx_u64(&x100, &x101, UINT8_C(0x26), x90);
  mulx_u64(&x102, &x103, UINT8_C(0x26), x88);
  addcarryx_u64(&x104, &x105, 0x0, x82, x100);
  addcarryx_u64(&x106, &x107, x105, x84, x98);
  addcarryx_u64(&x108, &x109, x107, x86, x96);
  x110 = (uint8_t)(x109 + (uint8_t)x97);
  addcarryx_u64(&x111, &x112, 0x0, x31, x102);
  addcarryx_u64(&x113, &x114, x112, x104, (uint8_t)x103);
  addcarryx_u64(&x115, &x116, x114, x106, (uint8_t)x101);
  addcarryx_u64(&x117, &x118, x116, x108, (uint8_t)x99);
  x119 = (uint8_t)(x118 + x110);
  mulx_u64(&x120, &x121, UINT8_C(0x26), x119);
  addcarryx_u64(&x122, &x123, 0x0, x111, (uint16_t)x120);
  addcarryx_u64(&x124, &x125, x123, x113, 0x0);
  addcarryx_u64(&x126, &x127, x125, x115, 0x0);
  addcarryx_u64(&x128, &x129, x127, x117, 0x0);
  cmovznz_u8(&x130, x129, 0x0, UINT8_C(0x26));
  x131 = (x130 + (uint128)x122);
  out1[0] = x131;
  out1[1] = x124;
  out1[2] = x126;
  out1[3] = x128;
}

with input bounds (Some [Some [0x0 ~> 0xffffffffffffffff], Some [0x0 ~> 0xffffffffffffffff], Some [0x0 ~> 0xffffffffffffffff], Some [0x0 ~> 0xffffffffffffffff]], Some [Some [0x0 ~> 0xffffffffffffffff], Some [0x0 ~> 0xffffffffffffffff], Some [0x0 ~> 0xffffffffffffffff], Some [0x0 ~> 0xffffffffffffffff]]).
"
     : string
Finished transaction in 8.123 secs (7.909u,0.142s) (successful)
*)

  End compile.

End debugging_solinas_reduction.

Module debugging_go_bits_add.
  Import Stringification.Go.
  Section __.
    Local Existing Instance Go.OutputGoAPI.
    Local Instance : Primitives.Options.PipelineOptions :=
      {| Primitives.Options.output_options :=
        {| relax_adc_sbb_return_carry_to_bitwidth_ := [32; 64]
        ; skip_typedefs_ := true
        ; language_specific_cast_adjustment_ := true
        |}
      ; Primitives.Options.widen_carry := true
      ; Primitives.Options.widen_bytes := true
      ; Primitives.Options.only_signed := false
      ; Primitives.Options.no_select := false
      ; Primitives.Options.should_split_mul := true (* only for x64 *)
      ; Primitives.Options.should_split_multiret := false
      |}.

    Context (s := 2^127)
            (c :=  [(1,1)])
            (machine_wordsize := 64).

    Goal True.
      pose (WordByWordMontgomery.smul (s - Associational.eval c) machine_wordsize "p256_") as v.
      vm_compute Z.sub in v.
      cbv [WordByWordMontgomery.smul] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      vm_compute in v.
      clear v.
      cbv beta delta [Pipeline.BoundsPipelineWithDebug] in k.
      rename k into k'; pose (DebugMonad.Debug.eval_result k') as k; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In DebugMonad.Debug.eval_result DebugMonad.Debug.sequence Pipeline.debug_after_rewrite DebugMonad.Debug.ret] in k.
      vm_compute Pipeline.debug_rewriting in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (v := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in v.
      repeat match goal with
             | [ H := @inl ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inl A B H') in (value of H); subst H; rename H' into H; cbv beta iota in *
             | [ H := @inr ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inr A B H') in (value of H); subst H; rename H' into H; cbv beta iota in *
             end.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (v' := DebugMonad.Debug.bind _) in (value of k) at 1.
      vm_compute in v'; subst v'; cbn [snd] in k.
      set (v' := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in v'.
      clear -k.
      repeat match goal with
             | [ H := @inl ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inl A B H') in (value of H); subst H; rename H' into H; cbv beta iota in *
             | [ H := @inr ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inr A B H') in (value of H); subst H; rename H' into H; cbv beta iota in *
             end.
      vm_compute Pipeline.no_select_size in k.
      vm_compute Pipeline.split_mul_to in k.
      vm_compute Pipeline.split_multiret_to in k.
      vm_compute Pipeline.split_multiret_to in k.
      vm_compute Pipeline.translate_to_fancy in k.
      cbv beta iota in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (v := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in v.
      clear -k.
      repeat match goal with
             | [ H := @inl ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inl A B H') in (value of H); subst H; rename H' into H; cbv beta iota in *
             | [ H := @inr ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inr A B H') in (value of H); subst H; rename H' into H; cbv beta iota in *
             end.
      vm_compute Pipeline.relax_adc_sbb_return_carry_to_bitwidth in k.
      cbv beta iota in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (v' := DebugMonad.Debug.bind _) in (value of k) at 1.
      vm_compute in v'; subst v'; cbn [snd] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (v' := Pipeline.RewriteAndEliminateDeadAndInline _ _ _ _ _ _) in (value of k).
      vm_compute in v'; clear -k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; subst v'; cbn [snd] in k.
      cbv [Pipeline.wrap_debug_rewrite] in k.
      set (v := RelaxBitwidthAdcSbb.Compilers.RewriteRules.RewriteRelaxBitwidthAdcSbb _ _ _) in (value of k).
      Notation uint64 := r[0~>18446744073709551615]%zrange.
      Import IdentifiersBasicGENERATED.Compilers.
      Import API.Compilers.
      Import APINotations.Compilers.
      (*
      Compute 2^64-1.
      Compute Z.log2(18446744073709551615+1).
      clear -v.
      vm_compute in v.
      subst v; cbv beta iota zeta in k.
      vm_compute in k.

      Import Rewriter.Util.LetIn.
      let do_set a v f :=
          lazymatch v with
          | context[let n := _ in _] => fail
          | context[dlet n := _ in _] => fail
          | _ => idtac
          end;
          first [ pose v as a; change (f a) in (value of k)
                | let a := fresh "E" in pose v as a; change (f a) in (value of k) ]
      in
      repeat
        (repeat (lazymatch (eval cbv delta [k] in k) with
                 | context T[(let a := ?v in @?f a) ?x]
                   => let G' := context T[let a := v in f a x] in change G' in (value of k)
                 end; cbv beta in k);
         match (eval cbv delta [k] in k) with
         | context T[let a := ?v in @?f a]  => do_set a v f
         | context T[dlet a := ?v in @?f a] => do_set a v f
         end; cbv beta in k).
      clear -k.
      match (eval cbv delta [E] in E) with
      | context T[@expr.APP ?a ?b ?c ?d ?e ?f]
        => pose (@expr.APP a b c d e f) as v;
             let T' := context T[v] in
             change T' in (value of E)
      end.
      Time vm_compute in v.
      cbv beta delta [Pipeline.PreBoundsPipeline] in E.
      repeat (lazymatch (eval cbv delta [E] in E) with
              | context T[(let a := ?v in @?f a) ?x]
                => let G' := context T[let a := v in f a x] in change G' in (value of E)
              end; cbv beta in E).
      let do_set a v f :=
          lazymatch v with
          | context[let n := _ in _] => fail
          | context[dlet n := _ in _] => fail
          | _ => idtac
          end;
          first [ pose v as a; change (f a) in (value of E)
                | let a := fresh "E" in pose v as a; change (f a) in (value of E) ]
      in
      repeat
        (repeat (lazymatch (eval cbv delta [E] in E) with
                 | context T[(let a := ?v in @?f a) ?x]
                   => let G' := context T[let a := v in f a x] in change G' in (value of E)
                 end; cbv beta in E);
         match (eval cbv delta [E] in E) with
         | context T[let a := ?v in @?f a]  => do_set a v f
         | context T[dlet a := ?v in @?f a] => do_set a v f
         end; cbv beta iota in * ).
      vm_compute Primitives.possible_values_of_machine_wordsize in relax_zrange.
      cbv [only_signed_opt_instance_0] in relax_zrange.
      cbv [Pipeline.opts_of_method] in E1; subst E0.
      cbv [default_low_level_rewriter_method] in E1.
      vm_compute in E1.
      Notation "'hide'" := (expr.Abs _) : expr_scope.
      Time vm_compute in E2.
      Time vm_compute in E3.
      clear -k.
      subst E7.
      Time time vm_compute in E4; time vm_compute in E5; time vm_compute in E6; time vm_compute in e; time vm_compute in E8; subst E8; time vm_compute in E'; clear -k.
      repeat match goal with
             | [ H := @inl ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inl A B H') in (value of H); subst H; rename H' into H
             | [ H := @inr ?A ?B ?v |- _ ] => let H' := fresh "E" in pose v as H'; change (@inr A B H') in (value of H); subst H; rename H' into H
             end.
      cbv beta iota in *.
      let do_set a v f :=
          lazymatch v with
          | context[let n := _ in _] => idtac v; fail
          | context[dlet n := _ in _] => idtac v; fail
          | _ => idtac
          end;
          first [ pose v as a; change (f a) in (value of k)
                | let a := fresh "k" in pose v as a; change (f a) in (value of k) ]
      in
      repeat
        (repeat (lazymatch (eval cbv delta [k] in k) with
                 | context T[(let a := ?v in @?f a) ?x]
                   => let G' := context T[let a := v in f a x] in change G' in (value of k)
                 end; cbv beta in k);
         match (eval cbv delta [k] in k) with
         | context T[let a := ?v in @?f a]  => do_set a v f
         | context T[dlet a := ?v in @?f a] => do_set a v f
         end; cbv beta iota in * ).
      HERE
      Set Printing Implicit.
             end.
      let do_set a v f :=
          lazymatch v with
          | context[let n := _ in _] => fail
          | context[dlet n := _ in _] => fail
          | _ => idtac
          end;
          first [ pose v as a; change (f a) in (value of k)
                | let a := fresh "E" in pose v as a; change (f a) in (value of k) ]
      in
      lazymatch (eval cbv delta [E] in E) with
      | context T[let a := ?v in @?f a]  => idtac a v f; do_set a v f
      | context T[dlet a := ?v in @?f a] => do_set a v f
      end.
      let do_set a v f :=
          lazymatch v with
          | context[let n := _ in _] => fail
          | context[dlet n := _ in _] => fail
          | _ => idtac
          end;
          first [ set (a := v) in (value of k); change (f a) in (value of k)
                | let a := fresh "E" in set (a := v) in (value of k); change (f a) in (value of k) ]
      in
      do 1
        (repeat (lazymatch (eval cbv delta [E] in E) with
                 | context T[(let a := ?v in @?f a) ?x]
                   => let G' := context T[let a := v in f a x] in change G' in (value of E)
                 end; cbv beta in E);
         match (eval cbv delta [E] in E) with
         | context T[let a := ?v in @?f a]  => do_set a v f
         | context T[dlet a := ?v in @?f a] => do_set a v f
         end; cbv beta in E).
      lazymatch (eval cbv delta [E] in E) with
                 | context T[(let a := ?v in @?f a) ?x]
                   => let G' := context T[let a := v in f a x] in change G' in (value of E)
                 end; cbv beta in E.
      Time vm_compute in E.
      set (k' := expr.APP _ _) in (value of E) at 1.
      Time vm_compute in E.
      vm_compute in E'.
      vm_compute in k.
      vm_compute in v.
      subst k.
      cbv beta iota in v.
      cbv [Language.Compilers.ToString.ToFunctionLines] in v.
      cbv [Go.OutputGoAPI Crypto.Util.Option.sequence_return] in v.
      cbv [Go.ToFunctionLines] in v.
      set (k := IR.OfPHOAS.ExprOfPHOAS _ _ _ _) in (value of v).
      clear v.
      cbv [IR.OfPHOAS.ExprOfPHOAS IR.OfPHOAS.ExprOfPHOAS_cps IR.OfPHOAS.ExprOfPHOAS_with_opt_outbounds_cps IR.OfPHOAS.ExprOfPHOAS_cont] in k; rename k into v.
      cbv [IR.OfPHOAS.expr_of_PHOAS IR.OfPHOAS.expr_of_PHOAS_cps IR.OfPHOAS.expr_of_PHOAS_cont] in v.
      set (k := partial.Extract _ _ _) in (value of v).
      cbv [partial.Extract] in k.
      clear v; rename k into v.
      cbv [partial.ident.extract] in v.
      cbv [partial.extract_gen] in v.
      cbv [type.app_curried] in v.
      cbv delta [partial.extract'] in v.
      cbv delta [partial.extract_gen] in v.
      cbv beta in v.
      cbv [type.app_curried] in v.
      cbv delta [partial.extract'] in v.
      cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      do 50 (cbv iota in v; cbv beta in v).
      Import Rewriter.Util.LetIn.
      repeat match (eval cbv [v] in v) with
             | Let_In ?x ?f
               => let x := (eval vm_compute in x) in
                  clear v; pose (f x) as v
             end.
      (*
      cbv beta in v.
      cbv [partial.abstract_interp_ident] in v.
      set (k := ZRange.ident.option.interp true Compilers.ident_cons) in (value of v).
      cbn in k; subst k; cbv beta in v.
      set (k := ZRange.ident.option.interp true Compilers.ident_nil) in (value of v).
      cbn in k; subst k; cbv beta in v.
      cbn [option_map] in v.
      set (l := ZRange.ident.option.interp true _) in (value of v) at 2; vm_compute in l.
      subst l.
      set (l := ZRange.ident.option.interp true _) in (value of v) at 3; vm_compute in l.
      subst l.
      set (l := ZRange.ident.option.interp true _) in (value of v) at 4; vm_compute in l.
      subst l.
       *)
      (*
      cbv [ZRange.ident.option.interp] in v.
      cbv [
      cbv beta zeta delta [Rewriter.Util.LetIn.Let_In].
      cbv [partial.extract'] in v.
      vm_compute in k.
      vm_compute in k.
      vm_compute in k; subst k.
      cbv beta iota zeta in v.
      set (v' := Go.to_function_lines _ _ _ _) in (value of v).

      clear v; rename v' into v.
      cbv [WordByWordMontgomery.add] in k.
      cbv [Primitives.possible_values_of_machine_wordsize] in k.
      cbv [widen_carry] in k.
      cbv [widen_carry_opt_instance_0] in k.
      cbv [Pipeline.BoundsPipeline Pipeline.PreBoundsPipeline] in k.
      set (k' := GeneralizeVar.ToFlat _) in (value of k).
      vm_compute in k'; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat _) in (value of k); vm_compute in k'; subst k'.
      cbv [CheckedPartialEvaluateWithBounds] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := CheckCasts.GetUnsupportedCasts _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota in k.
       *) *)
    Abort.
  End __.
End debugging_go_bits_add.

Local Existing Instance default_output_options.

Module debugging_typedefs.
  Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
  Import Stringification.C.
  Import Stringification.C.Compilers.
  Import Stringification.C.Compilers.ToString.
  Section __.
    Local Existing Instance C.OutputCAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : emit_primitives_opt := false.
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : widen_carry_opt := false.
    Local Instance : widen_bytes_opt := false.
    Local Instance : only_signed_opt := false.
    Local Instance : no_select_opt := false.
    Local Instance : should_split_mul_opt := false.
    Local Instance : should_split_multiret_opt :=false.

    Definition n := 3%nat (*5%nat*).
    Definition s := 2^127 (* 255*).
    Definition c := [(1, 1(*9*))].
    Definition machine_wordsize := 64.

    Import IR.Compilers.ToString.
    Redirect "log"
             Compute match (sadd n s c machine_wordsize "1271") return (string * Pipeline.ErrorT _) with
                     | (name, v)
                       => match Debug.eval_result v with
                          | ErrorT.Success {| Pipeline.lines := v |} => (name, ErrorT.Success (String.concat String.NewLine v))
                          | _ => _
                          end
                     end.
    Redirect "log"
             Compute Synthesize n s c machine_wordsize [] "curve" ["add"].

    Goal True.
      pose (sadd n s c machine_wordsize "1271") as v.
      cbv [sadd] in v.
      vm_compute Pipeline.BoundsPipelineWithDebug in v.
      cbv beta iota zeta in v.
      unfold Debug.bind in (value of v) at 1.
      cbn [fst snd] in v.
      cbv [Language.Compilers.ToString.ToFunctionLines] in v.
      cbv [C.OutputCAPI] in v.
      cbv [ToFunctionLines] in v.
      try (set (dbg := tree.smart_app _ _) in (value of v) at 1;
           vm_compute in dbg; subst dbg).
      vm_compute IR.OfPHOAS.ExprOfPHOAS in v.
      cbv beta iota zeta in v.
      (*vm_compute in v.*)
      set (k := ToString.OfPHOAS.input_bounds_to_string _ _) in (value of v).
      clear v.
      vm_compute in k.
    Abort.
  End __.
End debugging_typedefs.

Module debugging_21271_from_bytes.
  Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
  Import Stringification.C.
  Import Stringification.C.Compilers.
  Import Stringification.C.Compilers.ToString.
  Section __.
    Local Existing Instance C.OutputCAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : emit_primitives_opt := false.
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : widen_carry_opt := false.
    Local Instance : widen_bytes_opt := false.
    Local Instance : only_signed_opt := false.
    Local Instance : no_select_opt := false.
    Local Instance : should_split_mul_opt := false.
    Local Instance : should_split_multiret_opt :=false.

    Definition n := 3%nat (*5%nat*).
    Definition s := 2^127 (* 255*).
    Definition c := [(1, 1(*9*))].
    Definition machine_wordsize := 64.

    Import IR.Compilers.ToString.

    Goal True.
      pose (sfrom_bytes n s c machine_wordsize "1271") as v.
      cbv [sfrom_bytes] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      clear v.
      cbv [from_bytes] in k.
      cbv [Pipeline.BoundsPipelineWithDebug] in k.
      set (k' := Pipeline.PreBoundsPipeline _ _ _ _) in (value of k).
      vm_compute in k'.
      cbv beta delta [Pipeline.BoundsPipelineWithDebug] in k.
      let k' := fresh in rename k into k'; pose (DebugMonad.Debug.eval_result k') as k; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In DebugMonad.Debug.eval_result DebugMonad.Debug.sequence Pipeline.debug_after_rewrite DebugMonad.Debug.ret] in k.
      vm_compute Pipeline.debug_rewriting in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (k'' := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in k''.
      lazymatch (eval cbv [k''] in k'') with
      | @inl ?A ?B ?v => pose v as V; change k'' with (@inl A B V) in (value of k)
      end.
      cbv beta iota zeta in k.
      clear k''.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (e := GeneralizeVar.FromFlat _) in (value of k).
      vm_compute in e.
      set (k'' := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      cbv [CheckedPartialEvaluateWithBounds] in k''.
      clear -k''.
      cbv [Rewriter.Util.LetIn.Let_In] in k''.
      set (e' := (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e))) in (value of k'').
      vm_compute in e'; clear e; rename e' into e.
      set (b := (partial.Extract _ _ _)) in (value of k'').
      clear -b.
      cbv [partial.Extract partial.ident.extract partial.extract_gen type.app_curried partial.extract'] in b.
      subst e.
      cbv beta iota zeta in b.
      Import Rewriter.Util.LetIn.
      cbn [partial.abstract_interp_ident] in b.
      cbv [partial.abstract_interp_ident] in b.
      cbv [ZRange.ident.option.interp] in b.
      cbv [ZRange.ident.option.of_literal] in b.
      cbn [ZRange.ident.option.interp_Z_cast option_map] in b.
      cbv [partial.abstract_domain ZRange.type.base.option.interp type.interp ZRange.type.base.interp] in b.
      cbn [fst snd] in b.
      (do 54 try (lazymatch (eval cbv [b] in b) with
                  | dlet x := ?v in _ => let v' := (eval vm_compute in v) in change v with v' in (value of b)
                  end;
                  unfold Let_In at 1 in (value of b));
          try lazymatch (eval cbv [b] in b) with
              | dlet x := ?v in _ => let v' := (eval vm_compute in v) in change v with v' in (value of b)
              end).
      (*
      unfold Let_In at 1 in (value of b).
      lazymatch (eval cbv [b] in b) with
      | context[Crypto.Util.Option.bind ?v _] => let v' := (eval vm_compute in v) in change v with v' in (value of b)
      end.
      cbn [Crypto.Util.Option.bind] in b.
      set (k' := Operations.ZRange.land_bounds _ _) in (value of b).
      cbv [Operations.ZRange.land_bounds] in k'.
      clear -k'.*)
    Abort.
  End __.
End debugging_21271_from_bytes.

Module debugging_sat_solinas_25519.
  Section __.
    Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
    Import Stringification.C.
    Import Stringification.C.Compilers.
    Import Stringification.C.Compilers.ToString.

    (* We split these off to make things a bit easier on typeclass resolution and speed things up. *)
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

    (** ======= these are the changable parameters ====== *)
    Let s := 2^256.
    Let c := [(1, 38)].
    Let machine_wordsize := 64.
    (** ================================================= *)
    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.
    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m := s - Associational.eval c.
    (* Number of reductions is calculated as follows :
         Let i be the highest limb index of c. Then, each reduction
         decreases the number of extra limbs by (n-i-1). (The -1 comes
         from possibly having an extra high partial product at the end
         of a reduction.) So, to go from the n extra limbs we have
         post-multiplication down to 0, we need ceil (n / (n - i - 1))
         reductions.  In some cases. however, [n - i <= 1], and in
         this case, we do [n] reductions (is this enough?). *)
  Let nreductions : nat :=
    let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
    if Z.of_nat n - i <=? 1
    then n
    else Z.to_nat (Qceiling (Z.of_nat n / (Z.of_nat n - i - 1))).
    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat bound n.

    Time Redirect "log" Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) (* needs to be reduced to reify correctly *) in
                  let nreductions := (eval cbv in nreductions) (* needs to be reduced to reify correctly *) in
                  let r := Reify (@Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c n nreductions) in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn, None (* Should be: Some r[0~>0]%zrange, but bounds analysis is not good enough *) )
                   (None, (None, tt))
                   (None, None)
          : Pipeline.ErrorT _).
    (* Finished transaction in 6.9 secs (4.764u,0.001s) (successful) *)
  End __.
End debugging_sat_solinas_25519.

Module debugging_sat_solinas_25519_expanded_straightforward.
  Import PreExtra.
  Import Util.LetIn.
  Import ZUtil.Definitions.
  Module Saturated.
    Module Associational.
      Definition sat_multerm :=
        fun (s : Z) (t t' : Z * Z) =>
          dlet xy : Z * Z := Z.mul_split s (snd t) (snd t') in
          dlet _ := ident.comment ("sat_multerm", ("xy", xy)) in
          [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].
      Definition sat_mul :=
        fun (s : Z) (p q : list (Z * Z)) =>
          flat_map
            (fun t : Z * Z =>
               flat_map
                 (fun t' : Z * Z => sat_multerm s t t') q)
            p.
      Definition sat_multerm_const :=
        fun (s : Z) (t t' : Z * Z) =>
          if snd t =? 1
          then [(fst t * fst t', snd t')]
          else
            if snd t =? -1
            then [(fst t * fst t', - snd t')]
            else
              if snd t =? 0
              then []
              else
                dlet xy : Z * Z := Z.mul_split s (snd t) (snd t') in
          [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].
      Definition sat_mul_const :=
        fun (s : Z) (p q : list (Z * Z)) =>
          flat_map
            (fun t : Z * Z =>
               flat_map
                 (fun t' : Z * Z =>
                    sat_multerm_const s t t') q) p.
    End Associational.
    Module Columns.
      Definition cons_to_nth :=
        fun (i : nat) (x : Z) (xs : list (list Z)) =>
          Crypto.Util.ListUtil.update_nth i (fun y : list Z => x :: y) xs.
      Definition nils : nat -> list (list Z) := fun n => repeat [] n.
      Definition from_associational :=
        fun (weight : nat -> Z) (n : nat) (p : list (Z * Z)) =>
          fold_right
            (fun (t : Z * Z) (ls : list (list Z)) =>
               dlet p0 : nat * Z := place weight t (Init.Nat.pred n) in
                 cons_to_nth (fst p0) (snd p0) ls)
            (nils n) p.
    End Columns.
    Module Rows.
      (* if [s] is not exactly equal to a weight, we must adjust it to
         be a weight, so that rather than dividing by s and
         multiplying by c, we divide by w and multiply by c*(w/s).
         See
         https://github.com/mit-plv/fiat-crypto/issues/326#issuecomment-404135131
         for a bit more discussion *)
      Definition adjust_s :=
        fun (weight : nat -> Z) (fuel : nat) (s : Z) =>
          fold_right
            (fun (w_i : Z) '(v, found_adjustment) =>
               let res0 := (v, found_adjustment) in
               if found_adjustment : bool
               then res0
               else if w_i mod s =? 0 then (w_i, true) else res0)
            (s, false) (map weight (rev (seq 0 fuel))).
      Definition sat_reduce :=
        fun (weight : nat -> Z) (base s : Z) (c : list (Z * Z))
            (n : nat) (p : list (Z * Z)) =>
          let
            '(s', _) := adjust_s weight (S (S n)) s in
          let lo_hi := split s' p in
          fst lo_hi ++
              Associational.sat_mul_const base [
                (1, s' / s)]
              (Associational.sat_mul_const base c (snd lo_hi)).
      Definition repeat_sat_reduce :=
        fun (weight : nat -> Z) (base s : Z) (c p : list (Z * Z)) (n : nat) =>
          fold_right
            (fun (_ : nat) (q : list (Z * Z)) =>
               sat_reduce weight base s c n q) p
            (seq 0 n).
      Definition sum_rows' :=
        fun (weight : nat -> Z) (start_state : list Z * Z * nat) (row1 row2 : list Z) =>
          fold_right
            (fun (next : Z * Z) (state : list Z * Z * nat) =>
               let i := snd state in
               let low_high' :=
                   let low_high := fst state in
                   let low := fst low_high in
                   let high := snd low_high in
                   dlet sum_carry : Z * Z := Z.add_with_get_carry_full
                                               ((fun i0 : nat => weight (S i0) / weight i0) i)
                                               high (fst next) (snd next) in
               (low ++ [fst sum_carry], snd sum_carry) in
                   (low_high', S i)) start_state (rev (combine row1 row2)).
      Definition sum_rows :=
        fun (weight : nat -> Z) (row1 row2 : list Z) =>
          fst (sum_rows' weight ([], 0, 0%nat) row1 row2).
      Definition flatten' :=
        fun (weight : nat -> Z) (start_state : list Z * Z) (inp : list (list Z)) =>
          fold_right
            (fun (next_row : list Z) (state : list Z * Z) =>
               let out_carry := sum_rows weight (fst state) next_row
               in
               (fst out_carry, snd state + snd out_carry)) start_state inp.
      Definition flatten :=
        fun (weight : nat -> Z) (n : nat) (inp : list (list Z)) =>
          let default := zeros n in
          flatten' weight (hd default inp, 0)
                   (hd default (tl inp) :: tl (tl inp)).
      Definition extract_row :=
        fun inp : list (list Z) =>
          (map (fun c : list Z => tl c) inp, map (fun c : list Z => hd 0 c) inp).
      Definition from_columns' :=
        fun (n : nat) (start_state : list (list Z) * list (list Z)) =>
          fold_right
            (fun (_ : Z) (state : list (list Z) * list (list Z)) =>
               let cols'_row := extract_row (fst state) in
               (fst cols'_row, snd state ++ [snd cols'_row])) start_state
            (repeat 0 n).
      Definition from_columns :=
        fun inp : list (list Z) =>
          snd
            (from_columns' (Saturated.Rows.max_column_size inp)
                           (inp, [])).
      Definition from_associational :=
        fun (weight : nat -> Z) (n : nat) (p : list (Z * Z)) =>
          from_columns
            (Columns.from_associational weight n p).
      Definition mulmod :=
        fun (weight : nat -> Z) (base s : Z) (c : list (Z * Z))
            (n nreductions : nat) (p q : list Z) =>
          let p_a := to_associational weight n p in
          let q_a := to_associational weight n q in
          let pq_a := Associational.sat_mul base p_a q_a in
          let r_a :=
              Rows.repeat_sat_reduce weight base s c pq_a nreductions in
          Rows.flatten weight n
                       (Rows.from_associational weight n r_a).
    End Rows.
  End Saturated.

  Section __.
    Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
    Import Stringification.C.
    Import Stringification.C.Compilers.
    Import Stringification.C.Compilers.ToString.

    (* We split these off to make things a bit easier on typeclass resolution and speed things up. *)
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

    (** ======= these are the changable parameters ====== *)
    Let s := 2^256.
    Let c := [(1, 38)].
    Let machine_wordsize := 64.
    (** ================================================= *)
    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.
    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m := s - Associational.eval c.
    (* Number of reductions is calculated as follows :
         Let i be the highest limb index of c. Then, each reduction
         decreases the number of extra limbs by (n-i-1). (The -1 comes
         from possibly having an extra high partial product at the end
         of a reduction.) So, to go from the n extra limbs we have
         post-multiplication down to 0, we need ceil (n / (n - i - 1))
         reductions.  In some cases. however, [n - i <= 1], and in
         this case, we do [n] reductions (is this enough?). *)
    Let nreductions : nat :=
      let i := fold_right Z.max 0 (map (fun t => Z.log2 (fst t) / machine_wordsize) c) in
      if Z.of_nat n - i <=? 1
      then n
      else Z.to_nat (Qceiling (Z.of_nat n / (Z.of_nat n - i - 1))).
    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat bound n.

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) (* needs to be reduced to reify correctly *) in
                  let nreductions := (eval cbv in nreductions) (* needs to be reduced to reify correctly *) in
                  let r := Reify (@Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c n nreductions) in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn, None (* Should be: Some r[0~>0]%zrange, but bounds analysis is not good enough *) )
                   (None, (None, tt))
                   (None, None)
          : Pipeline.ErrorT _).
    (* Finished transaction in 6.9 secs (4.764u,0.001s) (successful) *)
  End __.
End debugging_sat_solinas_25519_expanded_straightforward.

Module debugging_sat_solinas_25519_expanded.
  Import PreExtra.
  Import Util.LetIn.
  Import ZUtil.Definitions.
  Module Saturated.
    Module Associational.
      Definition sat_multerm :=
        fun (s : Z) (t t' : Z * Z) =>
          dlet xy : Z * Z := Z.mul_split s (snd t) (snd t') in
          dlet _ := ident.comment ("sat_multerm", ("xy", xy)) in
          [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].
      Definition sat_mul :=
        fun (s : Z) (p q : list (Z * Z)) =>
          flat_map
            (fun t : Z * Z =>
               flat_map
                 (fun t' : Z * Z => sat_multerm s t t') q)
            p.
      Definition sat_multerm_const :=
        fun (s : Z) (t t' : Z * Z) =>
          if snd t =? 1
          then [(fst t * fst t', snd t')]
          else
            if snd t =? -1
            then [(fst t * fst t', - snd t')]
            else
              if snd t =? 0
              then []
              else
                dlet xy : Z * Z := Z.mul_split s (snd t) (snd t') in
          [(fst t * fst t', fst xy); (fst t * fst t' * s, snd xy)].
      Definition sat_mul_const :=
        fun (s : Z) (p q : list (Z * Z)) =>
          flat_map
            (fun t : Z * Z =>
               flat_map
                 (fun t' : Z * Z =>
                    sat_multerm_const s t t') q) p.
    End Associational.
    Module Columns.
      Definition cons_to_nth :=
        fun (i : nat) (x : Z) (xs : list (list Z)) =>
          Crypto.Util.ListUtil.update_nth i (fun y : list Z => x :: y) xs.
      Definition nils : nat -> list (list Z) := fun n => repeat [] n.
      Definition from_associational :=
        fun (weight : nat -> Z) (n : nat) (p : list (Z * Z)) =>
          fold_right
            (fun (t : Z * Z) (ls : list (list Z)) =>
               dlet p0 : nat * Z := place weight t (Init.Nat.pred n) in
                 cons_to_nth (fst p0) (snd p0) ls)
            (nils n) p.
    End Columns.
    Module Rows.
      (* if [s] is not exactly equal to a weight, we must adjust it to
         be a weight, so that rather than dividing by s and
         multiplying by c, we divide by w and multiply by c*(w/s).
         See
         https://github.com/mit-plv/fiat-crypto/issues/326#issuecomment-404135131
         for a bit more discussion *)
      Definition adjust_s :=
        fun (weight : nat -> Z) (fuel : nat) (s : Z) =>
          fold_right
            (fun (w_i : Z) '(v, found_adjustment) =>
               let res0 := (v, found_adjustment) in
               if found_adjustment : bool
               then res0
               else if w_i mod s =? 0 then (w_i, true) else res0)
            (s, false) (map weight (rev (seq 0 fuel))).
      Definition sat_reduce :=
        fun (weight : nat -> Z) (base s : Z) (c : list (Z * Z))
            (n : nat) (p : list (Z * Z)) =>
          let
            '(s', _) := adjust_s weight (S (S n)) s in
          let lo_hi := split s' p in
          fst lo_hi ++
              Associational.sat_mul_const base [
                (1, s' / s)]
              (Associational.sat_mul_const base c (snd lo_hi)).
      Definition repeat_sat_reduce :=
        fun (weight : nat -> Z) (base s : Z) (c p : list (Z * Z)) (n : nat) =>
          fold_right
            (fun (_ : nat) (q : list (Z * Z)) =>
               sat_reduce weight base s c n q) p
            (seq 0 n).
      Definition sum_rows' :=
        fun (weight : nat -> Z) (start_state : list Z * Z * nat) (row1 row2 : list Z) =>
          fold_right
            (fun (next : Z * Z) (state : list Z * Z * nat) =>
               let i := snd state in
               let low_high' :=
                   let low_high := fst state in
                   let low := fst low_high in
                   let high := snd low_high in
                   dlet sum_carry : Z * Z := Z.add_with_get_carry_full
                                               ((fun i0 : nat => weight (S i0) / weight i0) i)
                                               high (fst next) (snd next) in
               (low ++ [fst sum_carry], snd sum_carry) in
                   (low_high', S i)) start_state (rev (combine row1 row2)).
      Definition sum_rows :=
        fun (weight : nat -> Z) (row1 row2 : list Z) =>
          fst (sum_rows' weight ([], 0, 0%nat) row1 row2).
      Definition flatten' :=
        fun (weight : nat -> Z) (start_state : list Z * Z) (inp : list (list Z)) =>
          fold_right
            (fun (next_row : list Z) (state : list Z * Z) =>
               let out_carry := sum_rows weight (fst state) next_row
               in
               (fst out_carry, snd state + snd out_carry)) start_state inp.
      Definition flatten :=
        fun (weight : nat -> Z) (n : nat) (inp : list (list Z)) =>
          let default := zeros n in
          flatten' weight (hd default inp, 0)
                   (hd default (tl inp) :: tl (tl inp)).
      Definition extract_row :=
        fun inp : list (list Z) =>
          (map (fun c : list Z => tl c) inp, map (fun c : list Z => hd 0 c) inp).
      Definition from_columns' :=
        fun (n : nat) (start_state : list (list Z) * list (list Z)) =>
          fold_right
            (fun (_ : Z) (state : list (list Z) * list (list Z)) =>
               let cols'_row := extract_row (fst state) in
               (fst cols'_row, snd state ++ [snd cols'_row])) start_state
            (repeat 0 n).
      Definition from_columns :=
        fun inp : list (list Z) =>
          snd
            (from_columns' (Saturated.Rows.max_column_size inp)
                           (inp, [])).
      Definition from_associational :=
        fun (weight : nat -> Z) (n : nat) (p : list (Z * Z)) =>
          from_columns
            (Columns.from_associational weight n p).
      Definition mulmod :=
        fun (weight : nat -> Z) (base s : Z) (c : list (Z * Z))
            (n nreductions : nat) (p q : list Z) =>
          let p_a := to_associational weight n p in
          let q_a := to_associational weight n q in
          let pq_a := Associational.sat_mul base p_a q_a in
          let pq_r := fst (Rows.flatten weight (n+n) (Rows.from_associational weight (n+n) pq_a)) in

          let pq_a := to_associational weight (n+n) pq_r in
          let pq_a := Rows.sat_reduce weight base s c 1 pq_a in
          let pq_r := fst (Rows.flatten weight (n+1) (Rows.from_associational weight (n+1) pq_a)) in

          let pq_a := to_associational weight (n+1) pq_r in
          let pq_a := Rows.sat_reduce weight base s c 1 pq_a in
          let pq_r := Rows.flatten weight n (Rows.from_associational weight n pq_a) in

          pq_r.
    End Rows.
  End Saturated.

  Section __.
    Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
    Import Stringification.C.
    Import Stringification.C.Compilers.
    Import Stringification.C.Compilers.ToString.

    (* We split these off to make things a bit easier on typeclass resolution and speed things up. *)
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

    (** ======= these are the changable parameters ====== *)
    Let s := 2^256.
    Let c := [(1, 38)].
    Let machine_wordsize := 64.
    (** ================================================= *)
    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.
    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m := s - Associational.eval c.
    (* Number of reductions is calculated as follows :
         Let i be the highest limb index of c. Then, each reduction
         decreases the number of extra limbs by (n-i-1). (The -1 comes
         from possibly having an extra high partial product at the end
         of a reduction.) So, to go from the n extra limbs we have
         post-multiplication down to 0, we need ceil (n / (n - i - 1))
         reductions.  In some cases. however, [n - i <= 1], and in
         this case, we do [n] reductions (is this enough?). *)
    Let nreductions : nat := 2.
    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
      := repeat bound n.

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) (* needs to be reduced to reify correctly *) in
                  let nreductions := (eval cbv in nreductions) (* needs to be reduced to reify correctly *) in
                  let r := Reify (@Saturated.Rows.mulmod (weight machine_wordsize 1) (2^machine_wordsize) s c n nreductions) in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn, None (* Should be: Some r[0~>0]%zrange, but bounds analysis is not good enough *) )
                   (None, (None, tt))
                   (None, None)
          : Pipeline.ErrorT _).


(*
= "Success (""/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   out2: None
 */
static void mul(uint64_t out1[4], fiatuint1* out2, const uint64_t arg1[4], const uint64_t arg2[4]) {
// 16 mulx
  uint64_t x1;
  uint64_t x2;
  fiatmulx_u64(&x1, &x2, (arg1[3]), (arg2[3]));
  uint64_t x3;
  uint64_t x4;
  fiatmulx_u64(&x3, &x4, (arg1[3]), (arg2[2]));
  uint64_t x5;
  uint64_t x6;
  fiatmulx_u64(&x5, &x6, (arg1[3]), (arg2[1]));
  uint64_t x7;
  uint64_t x8;
  fiatmulx_u64(&x7, &x8, (arg1[3]), (arg2[0]));
  uint64_t x9;
  uint64_t x10;
  fiatmulx_u64(&x9, &x10, (arg1[2]), (arg2[3]));
  uint64_t x11;
  uint64_t x12;
  fiatmulx_u64(&x11, &x12, (arg1[2]), (arg2[2]));
  uint64_t x13;
  uint64_t x14;
  fiatmulx_u64(&x13, &x14, (arg1[2]), (arg2[1]));
  uint64_t x15;
  uint64_t x16;
  fiatmulx_u64(&x15, &x16, (arg1[2]), (arg2[0]));
  uint64_t x17;
  uint64_t x18;
  fiatmulx_u64(&x17, &x18, (arg1[1]), (arg2[3]));
  uint64_t x19;
  uint64_t x20;
  fiatmulx_u64(&x19, &x20, (arg1[1]), (arg2[2]));
  uint64_t x21;
  uint64_t x22;
  fiatmulx_u64(&x21, &x22, (arg1[1]), (arg2[1]));
  uint64_t x23;
  uint64_t x24;
  fiatmulx_u64(&x23, &x24, (arg1[1]), (arg2[0]));
  uint64_t x25;
  uint64_t x26;
  fiatmulx_u64(&x25, &x26, (arg1[0]), (arg2[3]));
  uint64_t x27;
  uint64_t x28;
  fiatmulx_u64(&x27, &x28, (arg1[0]), (arg2[2]));
  uint64_t x29;
  uint64_t x30;
  fiatmulx_u64(&x29, &x30, (arg1[0]), (arg2[1]));
  uint64_t x31;
  uint64_t x32;
  fiatmulx_u64(&x31, &x32, (arg1[0]), (arg2[0]));
// 30 addcarryx and some normal additions
  uint64_t x33;
  fiatuint1 x34;
  fiataddcarryx_u64(&x33, &x34, 0x0, x28, x7);
  uint64_t x35;
  fiatuint1 x36;
  fiataddcarryx_u64(&x35, &x36, x34, x26, x5);
  uint64_t x37 = (x36 + x18);
  uint64_t x38;
  fiatuint1 x39;
  fiataddcarryx_u64(&x38, &x39, 0x0, x33, x13);
  uint64_t x40;
  fiatuint1 x41;
  fiataddcarryx_u64(&x40, &x41, x39, x35, x8);
  uint64_t x42;
  fiatuint1 x43;
  fiataddcarryx_u64(&x42, &x43, x41, x37, 0x0);
  uint64_t x44 = (x43 + x10);
  uint64_t x45;
  fiatuint1 x46;
  fiataddcarryx_u64(&x45, &x46, 0x0, x30, x15);
  uint64_t x47;
  fiatuint1 x48;
  fiataddcarryx_u64(&x47, &x48, x46, x38, x16);
  uint64_t x49;
  fiatuint1 x50;
  fiataddcarryx_u64(&x49, &x50, x48, x40, x11);
  uint64_t x51;
  fiatuint1 x52;
  fiataddcarryx_u64(&x51, &x52, x50, x42, x3);
  uint64_t x53;
  fiatuint1 x54;
  fiataddcarryx_u64(&x53, &x54, x52, x44, 0x0);
  uint64_t x55 = (x54 + x2);
  uint64_t x56;
  fiatuint1 x57;
  fiataddcarryx_u64(&x56, &x57, 0x0, x45, x21);
  uint64_t x58;
  fiatuint1 x59;
  fiataddcarryx_u64(&x58, &x59, x57, x47, x19);
  uint64_t x60;
  fiatuint1 x61;
  fiataddcarryx_u64(&x60, &x61, x59, x49, x14);
  uint64_t x62;
  fiatuint1 x63;
  fiataddcarryx_u64(&x62, &x63, x61, x51, x6);
  uint64_t x64;
  fiatuint1 x65;
  fiataddcarryx_u64(&x64, &x65, x63, x53, 0x0);
  uint64_t x66;
  fiatuint1 x67;
  fiataddcarryx_u64(&x66, &x67, x65, x55, 0x0);
  uint64_t x68;
  fiatuint1 x69;
  fiataddcarryx_u64(&x68, &x69, 0x0, x32, x23);
  uint64_t x70;
  fiatuint1 x71;
  fiataddcarryx_u64(&x70, &x71, x69, x56, x24);
  uint64_t x72;
  fiatuint1 x73;
  fiataddcarryx_u64(&x72, &x73, x71, x58, x22);
  uint64_t x74;
  fiatuint1 x75;
  fiataddcarryx_u64(&x74, &x75, x73, x60, x17);
  uint64_t x76;
  fiatuint1 x77;
  fiataddcarryx_u64(&x76, &x77, x75, x62, x9);
  uint64_t x78;
  fiatuint1 x79;
  fiataddcarryx_u64(&x78, &x79, x77, x64, x1);
  uint64_t x80;
  fiatuint1 x81;
  fiataddcarryx_u64(&x80, &x81, x79, x66, 0x0);
  uint64_t x82;
  fiatuint1 x83;
  fiataddcarryx_u64(&x82, &x83, 0x0, x68, x29);
  uint64_t x84;
  fiatuint1 x85;
  fiataddcarryx_u64(&x84, &x85, x83, x70, x27);
  uint64_t x86;
  fiatuint1 x87;
  fiataddcarryx_u64(&x86, &x87, x85, x72, x25);
  uint64_t x88;
  fiatuint1 x89;
  fiataddcarryx_u64(&x88, &x89, x87, x74, x20);
  uint64_t x90;
  fiatuint1 x91;
  fiataddcarryx_u64(&x90, &x91, x89, x76, x12);
  uint64_t x92;
  fiatuint1 x93;
  fiataddcarryx_u64(&x92, &x93, x91, x78, x4);
  uint64_t x94;
  fiatuint1 x95;
  fiataddcarryx_u64(&x94, &x95, x93, x80, 0x0);
  uint64_t x96;
  uint64_t x97;
  fiatmulx_u64(&x96, &x97, UINT8_C(0x26), x94);
  uint64_t x98;
  uint64_t x99;
  fiatmulx_u64(&x98, &x99, UINT8_C(0x26), x92);
  uint64_t x100;
  uint64_t x101;
  fiatmulx_u64(&x100, &x101, UINT8_C(0x26), x90);
  uint64_t x102;
  uint64_t x103;
  fiatmulx_u64(&x102, &x103, UINT8_C(0x26), x88);
  uint64_t x104;
  fiatuint1 x105;
  fiataddcarryx_u64(&x104, &x105, 0x0, x82, x100);
  uint64_t x106;
  fiatuint1 x107;
  fiataddcarryx_u64(&x106, &x107, x105, x84, x98);
  uint64_t x108;
  fiatuint1 x109;
  fiataddcarryx_u64(&x108, &x109, x107, x86, x96);
  uint64_t x110 = (x109 + x97);
  uint64_t x111;
  fiatuint1 x112;
  fiataddcarryx_u64(&x111, &x112, 0x0, x31, x102);
  uint64_t x113;
  fiatuint1 x114;
  fiataddcarryx_u64(&x113, &x114, x112, x104, x103);
  uint64_t x115;
  fiatuint1 x116;
  fiataddcarryx_u64(&x115, &x116, x114, x106, x101);
  uint64_t x117;
  fiatuint1 x118;
  fiataddcarryx_u64(&x117, &x118, x116, x108, x99);
  uint64_t x119 = (x118 + x110);
  uint64_t x120;
  uint64_t x121;
  fiatmulx_u64(&x120, &x121, UINT8_C(0x26), x119);
  uint64_t x122;
  fiatuint1 x123;
  fiataddcarryx_u64(&x122, &x123, 0x0, x111, x120);
  uint64_t x124;
  fiatuint1 x125;
  fiataddcarryx_u64(&x124, &x125, x123, x113, 0x0);
  uint64_t x126;
  fiatuint1 x127;
  fiataddcarryx_u64(&x126, &x127, x125, x115, 0x0);
  uint64_t x128;
  fiatuint1 x129;
  fiataddcarryx_u64(&x128, &x129, x127, x117, 0x0);
  out1[0] = x122;
  out1[1] = x124;
  out1[2] = x126;
  out1[3] = x128;
  *out2 = x129;
}"", {| bitwidths_used := [uint1, uint64] ; addcarryx_lg_splits := [64] ; mulx_lg_splits := [64] ; cmovznz_bitwidths := [] |})"%string
     : string
*)



    (* Finished transaction in 6.9 secs (4.764u,0.001s) (successful) *)
  End __.
End debugging_sat_solinas_25519_expanded.

(*Require Import Crypto.Bedrock.Stringification.*)
Module debugging_p256_mul_bedrock2.
  Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
  Import Stringification.C.
  Import Stringification.C.Compilers.
  Import Stringification.C.Compilers.ToString.
  Section __.
    Local Existing Instance (*OutputBedrock2API*) C.OutputCAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : emit_primitives_opt := false.
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : widen_carry_opt := true.
    Local Instance : widen_bytes_opt := true.
    Local Instance : only_signed_opt := false.
    Local Instance : no_select_opt := false.
    Local Instance : should_split_mul_opt := true.
    Local Instance : should_split_multiret_opt := true.

    Definition m := (2^64 - 1)%Z. (*(2^256 - 2^224 + 2^192 + 2^96 - 1)%Z.*)
    Definition machine_wordsize := 64.

    Import IR.Compilers.ToString.

    Goal True.
      pose (smul m machine_wordsize "p256") as v.
      Import IdentifiersBasicGENERATED.Compilers.
      cbv [smul] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      vm_compute in v.
      clear v.
      cbv [mul] in k.
      cbv -[Pipeline.BoundsPipelineWithDebug WordByWordMontgomeryReificationCache.WordByWordMontgomery.reified_mul_gen] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline Rewriter.Util.LetIn.Let_In] in k.
      let k' := fresh in rename k into k'; epose (DebugMonad.Debug.eval_result k') as k; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In DebugMonad.Debug.eval_result DebugMonad.Debug.sequence Pipeline.debug_after_rewrite DebugMonad.Debug.ret] in k.
      vm_compute Pipeline.debug_rewriting in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (k' := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in k'.
      subst k'; cbv beta iota zeta in k.
      cbv [Pipeline.RewriteAndEliminateDeadAndInline] in k.
      (*
      set (k' := ArithWithCasts.Compilers.RewriteRules.RewriteArithWithCasts _ _ _) in (value of k).
      vm_compute in k'.
      Notation uint64 := (expr.Ident (ident_Literal r[0 ~> 18446744073709551615]%zrange)).
      Notation "'(uint64)' x" := (#ident_Z_cast @ uint64 @ x)%expr (at level 0) : expr_scope.
      Notation "'(uint64,uint64)' x" := (#ident_Z_cast2 @ (uint64, uint64) @ x)%expr (at level 0) : expr_scope.
      subst k'; cbv beta iota zeta in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := UnderLets.LetBindReturn _ _) in (value of k) at 1.
      vm_compute in k'; subst k'.
      set (k' := ArithWithCasts.Compilers.RewriteRules.RewriteArithWithCasts _ _ _) in (value of k).
      vm_compute in k'.
      subst k'; cbv beta iota zeta in k.
      set (k' := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in k'.
      subst k'; cbv beta iota zeta in k.
      set (k' := MulSplit.Compilers.RewriteRules.RewriteMulSplit _ _ _ _) in (value of k) at 1.
      vm_compute in k'.
      subst k'.
      set (k' := MultiRetSplit.Compilers.RewriteRules.RewriteMultiRetSplit _ _ _ _) in (value of k) at 2.
      vm_compute in k'.
      vm_compute in k.
      vm_compute in k'.
      Import IdentifiersBasicGENERATED.Compilers.
      subst k'; cbv beta iota zeta in k.
       *)
    Abort.
  End __.
End debugging_p256_mul_bedrock2.

Module debugging_25519_to_bytes_bedrock2.
  Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
  Import Stringification.C.
  Import Stringification.C.Compilers.
  Import Stringification.C.Compilers.ToString.
  Section __.
    Local Existing Instance C.OutputCAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : emit_primitives_opt := false.
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : widen_carry_opt := true.
    Local Instance : widen_bytes_opt := true.
    Local Instance : only_signed_opt := false.
    Local Instance : no_select_opt := false.
    Local Instance : should_split_mul_opt := true.
    Local Instance : should_split_multiret_opt := true.

    Definition n := 2%nat (*5%nat*).
    Definition s := 2^127 (* 255*).
    Definition c := [(1, 1(*9*))].
    Definition machine_wordsize := 64.

    Import IR.Compilers.ToString.

    Goal True.
      pose (sto_bytes n s c machine_wordsize "curve25519") as v.
      cbv [sto_bytes] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      clear v.
      (*
      cbv [to_bytes] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline] in k.
      set (k' := Arith.Compilers.RewriteRules.RewriteArith _ _ _) in (value of k).
      vm_compute in k'.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k'' := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in k''.
      set (uint64 := r[0 ~> 18446744073709551615]%zrange) in (value of k'').
      subst k''.
      cbv beta iota zeta in k.
      set (k'' := Pipeline.RewriteAndEliminateDeadAndInline _ _ _ _ _ _) in (value of k).
      vm_compute in k''.
      Compute Z.log2 9223372036854775808.
      clear -k''.
      set (k'' := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      vm_compute in k''.
      subst k''.
      cbv beta iota zeta in k.
      subst k'.
      set (v := split_multiret_to machine_wordsize) in (value of k); vm_compute in v; subst v.
      set (v := split_mul_to machine_wordsize) in (value of k); vm_compute in v; subst v.
      cbv beta iota zeta in k.
      set (k' := MulSplit.Compilers.RewriteRules.RewriteMulSplit _ _ _ _) in (value of k).
      vm_compute in k'.
      cbv [Pipeline.RewriteAndEliminateDeadAndInline] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k'' := MultiRetSplit.Compilers.RewriteRules.RewriteMultiRetSplit _ _ _ k') in (value of k).
      clear k.
      evar (varT : Type); evar (var : varT); subst varT.
      evar (xT : Type); evar (x : xT); subst xT.
      pose ((*Option.invert_Some*) (option_map (fun f => f x) (invert_expr.invert_Abs (k'' var)))) as k; subst k'' var x.
      cbv [option_map Option.invert_Some invert_expr.invert_Abs MultiRetSplit.Compilers.RewriteRules.RewriteMultiRetSplit] in k.
      cbv [Rewriter.Compilers.RewriteRules.Make.GoalType.rewrite_head_gen] in k.
      set (v := ProofsCommon.Compilers.RewriteRules.GoalType.DefaultOptionType.use_precomputed_functions _) in (value of k); vm_compute in v; subst v.
      set (v := ProofsCommon.Compilers.RewriteRules.GoalType.DefaultOptionType.use_decision_tree _) in (value of k); vm_compute in v; subst v.
      cbv [Rewriter.Compilers.RewriteRules.Compile.Rewrite] in k.
      cbv [Rewriter.Compilers.RewriteRules.Make.GoalType.rewrite_head] in k.
      cbv [Rewriter.Compilers.RewriteRules.Compile.rewrite] in k.
      set (fuel := 6%nat) in (value of k).
      cbn [Rewriter.Compilers.RewriteRules.Compile.repeat_rewrite] in k.
      set (k'' := k' _) in (value of k).
      match (eval cbv delta [k'] in k') with
      | fun var : ?T => expr.Abs ?f
        => evar (var' : T);
             pose (match var' return _ with var => f end) as F; subst var';
               assert (k'' = expr.Abs F) by reflexivity; clearbody k''; subst k''
      end.
      cbn [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in k.
      cbn [Rewriter.Compilers.RewriteRules.Compile.reify] in k.
      set (v := F _) in (value of k).
      clear k'.
      match (eval cbv delta [F] in F) with
      | fun x : ?T => ?f
        => evar (x' : T);
             pose (match x' return _ with x => f end) as f'; subst x';
               assert (v = f') by refine eq_refl; clearbody v; subst F v
      end.
      match (eval cbv delta [f'] in f') with
      | expr.LetIn ?v ?f =>
        pose v as V; pose f as F;
          assert (f' = expr.LetIn V F) by refine eq_refl; clearbody f'; subst f'; rename F into f'
      end.
      cbn [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in k;
        cbv [Rewriter.Compilers.RewriteRules.Compile.splice_value_with_lets Rewriter.Compilers.RewriteRules.Compile.splice_under_lets_with_value Rewriter.Compilers.RewriteRules.Compile.reify_and_let_binds_cps] in k.
      set (k'' := Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup _ _ _) in (value of k).
      vm_compute in k''.
      subst k''.
      cbn [UnderLets.splice] in k.
      set (k' := UnderLets.reify_and_let_binds_base_cps _ _ _ _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbn [UnderLets.splice] in k.
      subst V.
      match (eval cbv delta [f'] in f') with
      | fun x : ?T => expr.LetIn ?v ?f =>
        pose (fun x : T => v) as V; pose (fun x : T => f) as F;
          assert (f' = fun x : T => expr.LetIn (V x) (F x)) by refine eq_refl; clearbody f'; subst f'; rename F into f'
      end.
      cbn [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in k;
        cbv [Rewriter.Compilers.RewriteRules.Compile.splice_value_with_lets Rewriter.Compilers.RewriteRules.Compile.splice_under_lets_with_value Rewriter.Compilers.RewriteRules.Compile.reify_and_let_binds_cps] in k.
      subst V.
      cbn [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in k.
      cbn [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in k;
        cbv [Rewriter.Compilers.RewriteRules.Compile.splice_value_with_lets Rewriter.Compilers.RewriteRules.Compile.splice_under_lets_with_value Rewriter.Compilers.RewriteRules.Compile.reify_and_let_binds_cps] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      cbv [Rewriter.Compilers.RewriteRules.Compile.Base_value] in k.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      unfold MultiRetSplit.Compilers.RewriteRules.rewrite_head in (value of k) at 1.
      cbn [IdentifiersGENERATED.Compilers.pattern.ident.raw_invert_bind_args] in k;
        cbv [Option.sequence_return Option.bind] in k.
      cbn [UnderLets.splice] in k.
      cbn [Rewriter.Compilers.RewriteRules.Compile.reflect] in k.
      cbn [UnderLets.splice] in k.
      unfold MultiRetSplit.Compilers.RewriteRules.rewrite_head in (value of k) at 1.
      cbn [IdentifiersGENERATED.Compilers.pattern.ident.raw_invert_bind_args] in k;
        cbv [Option.sequence_return Option.bind] in k.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _ _) in (value of k) at 1.
      set (v' := v _) in (value of k); subst v; rename v' into v.
      cbn [UnderLets.to_expr] in k.
      lazymatch (eval cbv delta [k] in k) with
      | Some (expr.LetIn ?V (fun v : ?T => ?f))
        => evar (v' : T); pose (match v' return _ with v => f end) as F;
             subst v'
      end.
      clear k; rename F into k.
      set (v' := v _) in (value of k); subst v; rename v' into v.
      cbv beta iota zeta in v.
      Import Util.Option.
      set (uint64 := r[0 ~> 18446744073709551615]%zrange) in (value of v).
      Arguments type.base {_ _}.
      Arguments type.arrow {_ _ _}.
      set (b := expr.App _ _) in (value of v) at 3.
      cbn [MultiRetSplit.Compilers.RewriteRules.rewrite_head] in v.
      Ltac separate H do_subst :=
        lazymatch (eval cbv delta [H] in H) with
        | expr.App ?x ?y => let x' := fresh in
                            let y' := fresh in
                            set (x' := x) in (value of H);
                            set (y' := y) in (value of H);
                            separate x' true; separate y' false;
                            lazymatch do_subst with
                            | true => subst H
                            | false => idtac
                            end
        | _ => idtac
        end.
      separate b false.
      subst b.
      cbv beta iota in v.
      subst H5.
      clear -v.
      cbv beta iota in v.
      subst H9 H10 H8.
      subst H6.
      cbv beta iota in v.
      subst H11 H12 H7.
      subst H4.
      cbv beta iota in v.
      revert v; repeat match goal with H : _ |- _ => clear H end; intro v.
      subst H18 H22 H14.
      subst H2.
      cbv beta iota in v.
      subst H24 H28 H1.
      subst H0.
      cbv beta iota in v.
      cbn [IdentifiersGENERATED.Compilers.pattern.ident.raw_invert_bind_args Option.bind Option.sequence_return Option.sequence] in v.
      cbn [Rewriter.Compilers.pattern.type.unify_extracted Rewriter.Compilers.pattern.base.unify_extracted] in v.
      cbn [IdentifiersGENERATED.Compilers.pattern.ident.raw_invert_bind_args Option.bind Option.sequence_return Option.sequence] in v.
      cbn [type.type_beq base.type.type_beq andb] in v.
      cbn [IdentifiersGENERATED.Compilers.pattern.ident.unify] in v.
      cbn [Option.bind] in v.
      cbv [type.try_make_transport_cps base.try_make_transport_cps type.try_make_transport_cpsv Compilers.try_make_base_transport_cps Compilers.eta_base_cps Compilers.eta_base_cps_gen proj1_sig Compilers.base_eq_dec Compilers.base_rec Compilers.base_rect Rewriter.Util.CPSNotations.cpsreturn id eq_rect Rewriter.Util.CPSNotations.cps_option_bind Rewriter.Util.CPSNotations.cpsbind Rewriter.Util.CPSNotations.cpscall] in v.
      set (k' := andb _ _) in (value of v).
      Compute is_bounded_by_bool (2 ^ 64) (Operations.ZRange.normalize uint64).
      vm_compute in k'.
      do 9 (unfold IdentifiersGENERATED.Compilers.pattern.ident.raw_invert_bind_args in (value of v) at 1;
            c
            unfold Option.bind in (value of v) at 1).
         do 5 (unfold IdentifiersGENERATED.Compilers.pattern.ident.raw_invert_bind_args in (value of v) at 1;
            unfold Option.bind in (value of v) at 1).
      do 5 (unfold IdentifiersGENERATED.Compilers.pattern.ident.raw_invert_bind_args in (value of v) at 1;
            unfold Option.bind in (value of v) at 1).
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      unfold Option.bind in (value of v) at 1.
      cbn [Option.bind] in v.
      cbn [
      vm_compute in v.

      set (idc := Compilers.ident_Z_sub_with_get_borrow) in (value of b).

      subst b.

      cbv beta iota in v.
      cbv beta delta [MultiRetSplit.Compilers.RewriteRules.rewrite_head] in v.

      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      vm_compute in v.
      subst v.
      cbn [UnderLets.splice] in k.



      cbn [Rewriter.Compilers.RewriteRules.Compile.repeat_rewrite] in k.


      subst k'; cbv beta in k''.
      cbv [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in k.
      cbv [Rewriter.Compilers.RewriteRules.Compile.splice_value_with_lets] in k.
      cbv [Rewriter.Compilers.RewriteRules.Compile.splice_under_lets_with_value] in k.
      cbv [Rewriter.Compilers.RewriteRules.Compile.reify] in k.
      subst k'.
      cbv beta iota zeta in k.
      set (v := fun x => UnderLets.to_expr _) in (value of k); clear k.
      evar (xT : Type); evar (x : varT); subst
      epose (var : _).
      set (v := MultiRetSplit.Compilers.RewriteRules.rewrite_head _ _ _ _ _) in (value of k'').

      Print Rewriter.Compilers.RewriteRules.Compile.repeat_rewrite.
      cbv [Rewriter.Compilers.RewriteRules.Compile.repeat_rewrite] in k''.
      cbv [Rewriter.Compilers.RewriteRules.Compile.rewrite_bottomup] in k''.
      vm_compute in k''.
      cbv [split_multiret_to split_mul_to] in k.
      cbv [should_split_multiret should_split_mul] in k.

      vm_
      vm_compute in k.
      subst k.
      cbv beta iota zeta in v.
      set (k := Language.Compilers.ToString.ToFunctionLines _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in (value of v).
      clear v.
      cbv [Language.Compilers.ToString.ToFunctionLines] in k.
      cbv [Java.OutputJavaAPI] in k.
      cbv [Language.Compilers.ToString.ToFunctionLines] in k.
      cbv [Java.ToFunctionLines] in k.
      set (k' := IR.OfPHOAS.ExprOfPHOAS _ _ _ _) in (value of k).
      clear k.
      cbv [IR.OfPHOAS.ExprOfPHOAS] in k'.
      cbv [IR.OfPHOAS.expr_of_PHOAS] in k'.
      set (k := IR.OfPHOAS.var_data_of_bounds _ _ _ _) in (value of k').
      vm_compute in k.
      subst k.
      cbv beta iota zeta in k'.
      cbv [IR.OfPHOAS.expr_of_PHOAS'] in k'.
      set (k := IR.OfPHOAS.var_data_of_bounds _ _ _ _) in (value of k').
      vm_compute in k.
      subst k.
      cbv beta iota zeta in k'.
      cbv [invert_expr.invert_Abs] in k'.
      cbv [IR.OfPHOAS.expr_of_base_PHOAS] in k'.
      set (k := IR.OfPHOAS.make_assign_expr_of_PHOAS _ _) in (value of k') at 1.
      cbv [IR.OfPHOAS.make_assign_expr_of_PHOAS] in k.
      clear k'.
      set (k' := type.try_transport _ _ _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota zeta in k.
      set (k' := invert_expr.invert_App_Z_cast2 _) in (value of k).
      vm_compute in k'.

      subst k'.
      cbv beta iota zeta in k.
      set (k' := invert_expr.invert_AppIdent_curried _) in (value of k); vm_compute in k'; subst k'.
      cbv beta iota in k.
      set (k' := IR.OfPHOAS.arith_expr_of_PHOAS_args _) in (value of k).
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS_args] in k'.
      (*clear k.
      set (k := IR.OfPHOAS.arith_expr_of_base_PHOAS _ _) in (value of k') at 1.
      cbv [Language.Compilers.ToString.int.option.None] in k.
      cbv [IR.OfPHOAS.arith_expr_for_base] in k.
      cbv [IR.OfPHOAS.arith_expr_of_base_PHOAS] in k.
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS] in k.
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS_ident] in k.
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS_literal_Z] in k.
      vm_compute in k.*)
      vm_compute in k'.
      subst k'.
      cbv beta iota zeta in k.
      set (k' := Crypto.Util.Option.bind _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := Language.Compilers.ToString.int.of_zrange_relaxed _) in (value of k) at 1; vm_compute in k'; subst k'.
      set (k' := Language.Compilers.ToString.int.of_zrange_relaxed _) in (value of k) at 1; vm_compute in k'; subst k'.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.result_upcast _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.result_upcast _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.result_upcast _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      (*cbv
      vm_compute in k.
      vm_compute in k'.
      vm_compute in k'.
      cbv -[Language.Compilers.ToString.ToFunctionLines] in v.
      clear v.
      cbv [to_bytes] in k.
      cbv [Primitives.possible_values_of_machine_wordsize] in k.
      cbv [Primitives.possible_values_of_machine_wordsize_with_bytes] in k.
      cbv [widen_bytes] in k.
      cbv [widen_bytes_opt_instance_0] in k.
      cbv [widen_carry] in k.
      cbv [widen_carry_opt_instance_0] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat _) in (value of k); vm_compute in k'; subst k'.
      cbv [CheckedPartialEvaluateWithBounds] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat (GeneralizeVar.ToFlat _)) in (value of k).
      vm_compute in k'.
      subst k'.
      set (k' := CheckCasts.GetUnsupportedCasts _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota in k.
      set (k' := ZRange.type.base.option.is_tighter_than _ _) in (value of k).
      vm_compute in k'; subst k'.
      cbv beta iota in k.
      set (k' := ZRange.type.base.option.is_tighter_than _ _) in (value of k).
      vm_compute in k'; subst k'.
      cbv beta iota in k.
      cbv [split_multiret_to] in k.
      cbv [should_split_multiret] in k.
      cbv [should_split_multiret_opt_instance_0] in k.
      cbv [split_mul_to] in k.
      cbv [should_split_mul] in k.
      cbv [should_split_mul_opt_instance_0] in k.
      cbv [only_signed_opt_instance_0] in k.
      set (k' := GeneralizeVar.FromFlat (GeneralizeVar.ToFlat _)) in (value of k) at 2.
      vm_compute in k'.
      subst k'.
      set (k' := GeneralizeVar.FromFlat (GeneralizeVar.ToFlat _)) in (value of k) at 1.
      vm_compute in k'.
      subst k'.
      set (k' := PartialEvaluateWithBounds _ _ _ _ _) in (value of k).
      vm_compute in k'.
      subst k'.*)
*)
    Abort.
  End __.
End debugging_25519_to_bytes_bedrock2.

Local Instance : should_split_multiret_opt := false.
Local Instance : split_multiret_to_opt := None.

Module debugging_25519_to_bytes_java.
  Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
  Import Stringification.Java.
  Section __.
    Local Existing Instance Java.OutputJavaAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : emit_primitives_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := true.
    Local Instance : widen_carry_opt := true.
    Local Instance : widen_bytes_opt := true.
    Local Instance : only_signed_opt := true.
    Local Instance : no_select_opt := false.
    Local Instance : should_split_mul_opt := false. (* only for x64 *)

    Definition n := 2%nat (*10%nat*).
    Definition s := 2^51 (* 255*).
    Definition c := [(1, 19)].
    Definition machine_wordsize := 32.

    Import IR.Compilers.ToString.

    Goal True.
      pose (sto_bytes n s c machine_wordsize "curve25519") as v.
      cbv [sto_bytes] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      vm_compute in k.
      subst k.
      cbv beta iota zeta in v.
      let k' := fresh in rename v into k'; pose (DebugMonad.Debug.eval_result (snd k')) as v; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In DebugMonad.Debug.eval_result DebugMonad.Debug.sequence Pipeline.debug_after_rewrite DebugMonad.Debug.ret] in v.
      vm_compute Pipeline.debug_rewriting in v.
      unfold DebugMonad.Debug.bind in (value of v) at 1; cbn [snd] in v.
      set (k := Language.Compilers.ToString.ToFunctionLines _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in (value of v).
      clear v.
      cbv [Language.Compilers.ToString.ToFunctionLines] in k.
      cbv [Java.OutputJavaAPI] in k.
      cbv [Language.Compilers.ToString.ToFunctionLines] in k.
      cbv [Java.ToFunctionLines] in k.
      set (k' := IR.OfPHOAS.ExprOfPHOAS _ _ _ _ _ _) in (value of k).
      clear k.
      cbv [IR.OfPHOAS.ExprOfPHOAS IR.OfPHOAS.ExprOfPHOAS_cps IR.OfPHOAS.ExprOfPHOAS_with_opt_outbounds_cps IR.OfPHOAS.ExprOfPHOAS_cont] in k'.
      cbv [IR.OfPHOAS.expr_of_PHOAS IR.OfPHOAS.expr_of_PHOAS_cps IR.OfPHOAS.expr_of_PHOAS_cont] in k'.
      set (k := IR.OfPHOAS.var_data_of_bounds_and_typedefs _ _ _ _ _) in (value of k').
      vm_compute in k.
      subst k.
      cbv beta iota zeta in k'.
      cbv [IR.OfPHOAS.expr_of_PHOAS' IR.OfPHOAS.expr_of_PHOAS'_cps IR.OfPHOAS.expr_of_PHOAS'_cont] in k'.
      set (k := IR.OfPHOAS.var_data_of_bounds_and_typedefs _ _ _ _ _) in (value of k').
      vm_compute in k.
      subst k.
      cbv beta iota zeta in k'.
      cbv [invert_expr.invert_Abs] in k'.
      cbv [IR.OfPHOAS.expr_of_base_PHOAS] in k'.
      set (k := IR.OfPHOAS.make_assign_expr_of_PHOAS _ _) in (value of k') at 1.
      cbv [IR.OfPHOAS.make_assign_expr_of_PHOAS] in k.
      clear k'.
      set (k' := type.try_transport _ _ _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota zeta in k.
      set (k' := invert_expr.invert_App_Z_cast2 _) in (value of k).
      vm_compute in k'.

      subst k'.
      cbv beta iota zeta in k.
      set (k' := invert_expr.invert_AppIdent_curried _) in (value of k); vm_compute in k'; subst k'.
      cbv beta iota in k.
      set (k' := IR.OfPHOAS.arith_expr_of_PHOAS_args _) in (value of k).
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS_args] in k'.
      (*clear k.
      set (k := IR.OfPHOAS.arith_expr_of_base_PHOAS _ _) in (value of k') at 1.
      cbv [Language.Compilers.ToString.int.option.None] in k.
      cbv [IR.OfPHOAS.arith_expr_for_base] in k.
      cbv [IR.OfPHOAS.arith_expr_of_base_PHOAS] in k.
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS] in k.
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS_ident] in k.
      cbv [IR.OfPHOAS.arith_expr_of_PHOAS_literal_Z] in k.
      vm_compute in k.*)
      vm_compute in k'.
      subst k'.
      cbv beta iota zeta in k.
      set (k' := Crypto.Util.Option.bind _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := Language.Compilers.ToString.int.of_zrange_relaxed _) in (value of k) at 1; vm_compute in k'; subst k'.
      set (k' := Language.Compilers.ToString.int.of_zrange_relaxed _) in (value of k) at 1; vm_compute in k'; subst k'.
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      (*
      set (k' := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.result_upcast _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.result_upcast _ _) in (value of k) at 1; vm_compute in k'; subst k'.
      cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.result_upcast _ _) in (value of k) at 1; vm_compute in k'; subst k'.
       *)
      (*cbv
      vm_compute in k.
      vm_compute in k'.
      vm_compute in k'.
      cbv -[Language.Compilers.ToString.ToFunctionLines] in v.
      clear v.
      cbv [to_bytes] in k.
      cbv [Primitives.possible_values_of_machine_wordsize] in k.
      cbv [Primitives.possible_values_of_machine_wordsize_with_bytes] in k.
      cbv [widen_bytes] in k.
      cbv [widen_bytes_opt_instance_0] in k.
      cbv [widen_carry] in k.
      cbv [widen_carry_opt_instance_0] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat _) in (value of k); vm_compute in k'; subst k'.
      cbv [CheckedPartialEvaluateWithBounds] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat (GeneralizeVar.ToFlat _)) in (value of k).
      vm_compute in k'.
      subst k'.
      set (k' := CheckCasts.GetUnsupportedCasts _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota in k.
      set (k' := ZRange.type.base.option.is_tighter_than _ _) in (value of k).
      vm_compute in k'; subst k'.
      cbv beta iota in k.
      set (k' := ZRange.type.base.option.is_tighter_than _ _) in (value of k).
      vm_compute in k'; subst k'.
      cbv beta iota in k.
      cbv [split_multiret_to] in k.
      cbv [should_split_multiret] in k.
      cbv [should_split_multiret_opt_instance_0] in k.
      cbv [split_mul_to] in k.
      cbv [should_split_mul] in k.
      cbv [should_split_mul_opt_instance_0] in k.
      cbv [only_signed_opt_instance_0] in k.
      set (k' := GeneralizeVar.FromFlat (GeneralizeVar.ToFlat _)) in (value of k) at 2.
      vm_compute in k'.
      subst k'.
      set (k' := GeneralizeVar.FromFlat (GeneralizeVar.ToFlat _)) in (value of k) at 1.
      vm_compute in k'.
      subst k'.
      set (k' := PartialEvaluateWithBounds _ _ _ _ _) in (value of k).
      vm_compute in k'.
      subst k'.*)
    Abort.
  End __.
End debugging_25519_to_bytes_java.

Local Instance : only_signed_opt := false.
Local Instance : no_select_opt := false.
Local Instance : no_select_size_opt := None.

Module debugging_p256_uint1.
  Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
  Import Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
  Import Stringification.Java.
  Section __.
    Local Existing Instance Java.OutputJavaAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : emit_primitives_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := true.
    Local Instance : widen_carry_opt := true.
    Local Instance : widen_bytes_opt := true.
    Local Instance : should_split_mul_opt := false. (* only for x64 *)

    Context (m : Z := 2^256 - 2^224 + 2^192 + 2^96 - 1)
            (machine_wordsize : Z := 128).

    Goal True.
      pose (smul m machine_wordsize "p256") as v.
      cbv [smul] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      cbv [WordByWordMontgomery.mul] in k.
      cbv [Primitives.possible_values_of_machine_wordsize] in k.
      cbv [widen_carry] in k.
      cbv [widen_carry_opt_instance_0] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      clear v.
      let k' := fresh in rename k into k'; pose (DebugMonad.Debug.eval_result k') as k; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In DebugMonad.Debug.eval_result DebugMonad.Debug.sequence Pipeline.debug_after_rewrite DebugMonad.Debug.ret] in k.
      vm_compute Pipeline.debug_rewriting in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      match (eval cbv delta [k] in k) with
      | context[CheckedPartialEvaluateWithBounds _ _ _ _ ?e _ _]
        => set (k' := e) in (value of k)
      end; vm_compute in k'; subst k'.
      cbv [CheckedPartialEvaluateWithBounds] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat (GeneralizeVar.ToFlat _)) in (value of k).
      vm_compute in k'.
      subst k'.
      set (k' := CheckCasts.GetUnsupportedCasts _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota in k.
      set (k' := ZRange.type.base.option.is_tighter_than _ _) in (value of k).
      vm_compute in k'; subst k'.
      cbv beta iota in k.
      cbv [split_mul_to] in k.
      cbv [should_split_mul] in k.
      cbv [should_split_mul_opt_instance_0] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (k' := ZRange.type.base.option.is_tighter_than _ _) in (value of k).
      vm_compute in k'; subst k'.
      cbv beta iota in k.
      cbv [split_mul_to] in k.
      cbv [should_split_mul] in k.
      cbv [should_split_mul_opt_instance_0] in k.
      cbv [split_multiret_to should_split_multiret should_split_multiret_opt_instance_0] in k.
      vm_compute ZRange.type.base.option.is_tighter_than in k.
      cbv beta iota zeta in k.
      set (k' := PartialEvaluateWithBounds _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in k'.
    Abort.
  End __.
End debugging_p256_uint1.

Module debugging_go_build0.
  Import Stringification.Go.
  Section __.
    Local Existing Instance Go.OutputGoAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := false.
    Local Instance : inline_opt := false.
    Local Instance : inline_internal_opt := false.
    Local Instance : emit_primitives_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := true.
    Local Instance : widen_carry_opt := true.
    Local Instance : widen_bytes_opt := true.
    Local Instance : should_split_mul_opt := true. (* only for x64 *)

    Context (n : nat := 3%nat)
            (s : Z := 2^448)
            (c : list (Z * Z) := [(2^224,1);(1,1)])
            (machine_wordsize : Z := 512/3).
    (*
    Goal True.
      pose (scarry_mul n s c machine_wordsize "p448_") as v.
      cbv [scarry_mul] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      vm_compute in k.
      subst k.
      cbv beta iota in v.
      cbv [Language.Compilers.ToString.ToFunctionLines] in v.
      cbv [Go.OutputGoAPI Crypto.Util.Option.sequence_return] in v.
      cbv [Go.ToFunctionLines] in v.
      set (k := IR.OfPHOAS.ExprOfPHOAS _ _ _ _) in (value of v).
      clear v.
      cbv [IR.OfPHOAS.ExprOfPHOAS IR.OfPHOAS.ExprOfPHOAS_cps IR.OfPHOAS.ExprOfPHOAS_with_opt_outbounds_cps IR.OfPHOAS.ExprOfPHOAS_cont] in k; rename k into v.
      cbv [IR.OfPHOAS.expr_of_PHOAS IR.OfPHOAS.expr_of_PHOAS_cps IR.OfPHOAS.expr_of_PHOAS_cont] in v.
      set (k := partial.Extract _ _ _) in (value of v).
      cbv [partial.Extract] in k.
      clear v; rename k into v.
      cbv [partial.ident.extract] in v.
      cbv [partial.extract_gen] in v.
      cbv [type.app_curried] in v.
      cbv delta [partial.extract'] in v.
      cbv delta [partial.extract_gen] in v.
      cbv beta in v.
      cbv [type.app_curried] in v.
      cbv delta [partial.extract'] in v.
      cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      cbv iota in v; cbv beta in v.
      do 50 (cbv iota in v; cbv beta in v).
      Import Rewriter.Util.LetIn.
      repeat match (eval cbv [v] in v) with
             | Let_In ?x ?f
               => let x := (eval vm_compute in x) in
                  clear v; pose (f x) as v
             end.
      (*
      cbv beta in v.
      cbv [partial.abstract_interp_ident] in v.
      set (k := ZRange.ident.option.interp true Compilers.ident_cons) in (value of v).
      cbn in k; subst k; cbv beta in v.
      set (k := ZRange.ident.option.interp true Compilers.ident_nil) in (value of v).
      cbn in k; subst k; cbv beta in v.
      cbn [option_map] in v.
      set (l := ZRange.ident.option.interp true _) in (value of v) at 2; vm_compute in l.
      subst l.
      set (l := ZRange.ident.option.interp true _) in (value of v) at 3; vm_compute in l.
      subst l.
      set (l := ZRange.ident.option.interp true _) in (value of v) at 4; vm_compute in l.
      subst l.
       *)
      (*
      cbv [ZRange.ident.option.interp] in v.
      cbv [
      cbv beta zeta delta [Rewriter.Util.LetIn.Let_In].
      cbv [partial.extract'] in v.
      vm_compute in k.
      vm_compute in k.
      vm_compute in k; subst k.
      cbv beta iota zeta in v.
      set (v' := Go.to_function_lines _ _ _ _) in (value of v).

      clear v; rename v' into v.
      cbv [WordByWordMontgomery.add] in k.
      cbv [Primitives.possible_values_of_machine_wordsize] in k.
      cbv [widen_carry] in k.
      cbv [widen_carry_opt_instance_0] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline] in k.
      set (k' := GeneralizeVar.ToFlat _) in (value of k).
      vm_compute in k'; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat _) in (value of k); vm_compute in k'; subst k'.
      cbv [CheckedPartialEvaluateWithBounds] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := CheckCasts.GetUnsupportedCasts _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota in k.
       *)
    Abort.
     *)
  End __.
End debugging_go_build0.

Module debugging_go_build.
  Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
  Import Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
  Import Stringification.Go.
  Section __.
    Local Existing Instance Go.OutputGoAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := false.
    Local Instance : inline_opt := false.
    Local Instance : inline_internal_opt := false.
    Local Instance : emit_primitives_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := true.
    Local Instance : widen_carry_opt := true.
    Local Instance : widen_bytes_opt := true.
    Local Instance : should_split_mul_opt := true. (* only for x64 *)

    Context (m : Z := 2^256 - 2^224 + 2^192 + 2^96 - 1)
            (machine_wordsize : Z := 64).

    (*
    Goal True.
      pose (sadd m machine_wordsize "p256") as v.
      cbv [sadd] in v.
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      cbv [WordByWordMontgomery.add] in k.
      cbv [Primitives.possible_values_of_machine_wordsize] in k.
      cbv [widen_carry] in k.
      cbv [widen_carry_opt_instance_0] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline] in k.
      set (k' := GeneralizeVar.ToFlat _) in (value of k).
      vm_compute in k'; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := GeneralizeVar.FromFlat _) in (value of k); vm_compute in k'; subst k'.
      cbv [CheckedPartialEvaluateWithBounds] in k.
      cbv [Rewriter.Util.LetIn.Let_In] in k.
      set (k' := CheckCasts.GetUnsupportedCasts _) in (value of k).
      vm_compute in k'.
      subst k'.
      cbv beta iota in k.
      set (k' := partial.Extract _ _ _) in (value of k).
      vm_compute in k'.
      subst k'.
      set (k' := ZRange.type.base.option.is_tighter_than _ _) in (value of k).
      vm_compute in k'; subst k'.
      cbv beta iota in k.
      cbv [split_mul_to] in k.
      cbv [should_split_mul] in k.
      cbv [should_split_mul_opt_instance_0] in k.
      set (k' := PartialEvaluateWithBounds _ _ _ _ _ _) in (value of k).
      vm_compute in k'.
      subst k'.
      vm_compute in k.
      Notation "'λ'" := (expr.Abs _).
      Notation "'LET'" := (expr.LetIn _ _).
      subst k.
      cbv beta iota zeta in v.
      Arguments String.append !_ !_ / .
      cbn [String.append List.map List.app String.concat] in v.
      cbv [Language.Compilers.ToString.ToFunctionLines] in v.
      cbv [Crypto.Util.Option.sequence_return] in v.
      cbv [Go.OutputGoAPI] in v.
      cbn [type.map_for_each_lhs_of_arrow] in v.
      cbv [Go.ToFunctionLines] in v.
      set (k := IR.OfPHOAS.ExprOfPHOAS _ _ _ _) in (value of v).
      clear v.
      rename k into v.
      cbn [type.final_codomain] in v.
      cbn [Language.Compilers.ToString.OfPHOAS.var_data type.for_each_lhs_of_arrow] in v.
      cbn [Language.Compilers.ToString.OfPHOAS.base_var_data] in v.
      cbv [IR.OfPHOAS.ExprOfPHOAS IR.OfPHOAS.ExprOfPHOAS_cps IR.OfPHOAS.ExprOfPHOAS_with_opt_outbounds_cps IR.OfPHOAS.ExprOfPHOAS_cont] in v.
      cbn [IR.OfPHOAS.expr_of_PHOAS IR.OfPHOAS.expr_of_PHOAS_cps IR.OfPHOAS.expr_of_PHOAS_cont] in v.
      cbv [IR.OfPHOAS.expr_of_PHOAS IR.OfPHOAS.expr_of_PHOAS_cps IR.OfPHOAS.expr_of_PHOAS_cont] in v.
      set (k := IR.OfPHOAS.var_data_of_bounds _ _ _) in (value of v).
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      cbn [IR.OfPHOAS.expr_of_PHOAS' IR.OfPHOAS.expr_of_PHOAS'_cps IR.OfPHOAS.expr_of_PHOAS'_cont] in v.
      set (k := IR.OfPHOAS.var_data_of_bounds _ _ _) in (value of v).
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := IR.OfPHOAS.var_data_of_bounds _ _ _) in (value of v).
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      cbv [Show.show] in v.
      cbv [Language.Compilers.ToString.PHOAS.type.show] in v.
      cbn [Language.Compilers.ToString.PHOAS.type.show_type Language.Compilers.ToString.PHOAS.type.base.show] in v.
      cbv [Language.Compilers.ToString.PHOAS.type.base.show] in v.
      cbn [Language.Compilers.ToString.PHOAS.type.base.show_type Show.maybe_wrap_parens] in v.
      cbv [Show.show] in v.
      cbn [Language.Compilers.ToString.PHOAS.type.base.show_base] in v.
      cbn [String.append List.map List.app String.concat] in v.
      unfold invert_expr.invert_Abs at 1 in (value of v).
      unfold invert_expr.invert_Abs at 1 in (value of v).
      Time set (F := expr.LetIn _ _) in (value of v).
      Arguments IR.OfPHOAS.make_assign_expr_of_PHOAS _ / .
      Arguments Pos.to_nat !_ / .
      Ltac bar v F X :=
        (time (try lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
                   end;
               lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
               clear F; rename F' into F; subst X;
               cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v);
         time (repeat lazymatch (eval cbv [v] in v) with
                      | context C[match ?f ?x with _ => _ end]
                        => let f' := Tactics.Head.head f in
                           let fx := constr:(f x) in
                           (*idtac fx "(" f' ")";*)
                           let do_vm _ := lazymatch (eval cbv [v] in v) with
                                          | context C[fx]
                                            => pose fx as k;
                                               clear v;
                                               let C' := context C[k] in
                                               pose C' as v;
                                               (vm_compute in k; subst k; cbv beta iota in v)
                                          end in
                           lazymatch f' with
                           | @type.try_transport => do_vm ()
                           | @invert_expr.invert_App_Z_cast2 => do_vm ()
                           | @invert_expr.invert_App_Z_cast => do_vm ()
                           | @invert_expr.invert_App_curried => do_vm ()
                           | @Option.bind => do_vm ()
                           | @Crypto.Util.Option.bind => do_vm ()
                           | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                           | @IR.OfPHOAS.bounds_check => do_vm ()
                           | @fst => do_vm ()
                           | @snd => do_vm ()
                           | _ => progress cbn [f'] in v
                           end
                      end;
               repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v);
               cbn -[F] in v));
        time (repeat match (eval cbv [v] in v) with
                     | context C[match match ?x with inl l => @?LX l | inr r => @?RX r end with inl l' => @?L l' | inr r' => @?R r' end]
                       => let C' := context C[match x with inl l => match LX l with inl l' => L l' | inr r' => R r' end | inr r => match RX r with inl l' => L l' | inr r' => R r' end end] in
                          let C' := (eval cbv beta iota zeta in C') in
                          clear v; pose C' as v
                     end).
      Arguments IR.name_infos.adjust_dead : simpl never.
      do 3 bar v F X.
      do 1 bar v F X.
      time (try lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
                end;
            lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
            clear F; rename F' into F; subst X;
            cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v).
      cbn [IR.OfPHOAS.make_assign_expr_of_PHOAS] in v.
      do 4 lazymatch (eval cbv [v] in v) with
           | context C[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                let fx := constr:(f x) in
                (*idtac fx "(" f' ")";*)
                let do_vm _ := lazymatch (eval cbv [v] in v) with
                               | context C[fx]
                                 => pose fx as k;
                                      clear v;
                                      let C' := context C[k] in
                                      pose C' as v;
                                        (vm_compute in k; subst k; cbv beta iota in v)
                               end in
                lazymatch f' with
                | @type.try_transport => do_vm ()
                | @invert_expr.invert_App_Z_cast2 => do_vm ()
                | @invert_expr.invert_App_Z_cast => do_vm ()
                | @invert_expr.invert_App_curried => do_vm ()
                | @Option.bind => do_vm ()
                | @Crypto.Util.Option.bind => do_vm ()
                | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                | @IR.OfPHOAS.bounds_check => do_vm ()
                | @fst => do_vm ()
                | @snd => do_vm ()
                | _ => progress cbn [f'] in v
                end
           end.
      (*do 1 bar v F X.
      Set Printing Depth 10000000.
      do 2 bar v F X.
      do 2 bar v F X.
      lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
      end;
        lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
        clear F; rename F' into F; subst X;
          cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v.
      cbn [IR.OfPHOAS.make_assign_expr_of_PHOAS] in v.*)
      (*
      do 4 lazymatch (eval cbv [v] in v) with
           | context C[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                let fx := constr:(f x) in
                (*idtac fx "(" f' ")";*)
                let do_vm _ := lazymatch (eval cbv [v] in v) with
                               | context C[fx]
                                 => pose fx as k;
                                      clear v;
                                      let C' := context C[k] in
                                      pose C' as v;
                                        (vm_compute in k; subst k; cbv beta iota in v)
                               end in
                lazymatch f' with
                | @type.try_transport => do_vm ()
                | @invert_expr.invert_App_Z_cast2 => do_vm ()
                | @invert_expr.invert_App_Z_cast => do_vm ()
                | @invert_expr.invert_App_curried => do_vm ()
                | @invert_expr.invert_AppIdent_curried => do_vm ()
                | @Option.bind => do_vm ()
                | @Crypto.Util.Option.bind => do_vm ()
                | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                | @IR.OfPHOAS.bounds_check => do_vm ()
                | @fst => do_vm ()
                | @snd => do_vm ()
                | _ => progress cbn [f'] in v
                end
           end.
      set (k := Language.Compilers.ToString.int.type_beq _ _) in (value of v).
      vm_compute in k.
      subst k.
      cbv iota in v; cbv beta in v.
      subst k; cbv beta iota in v.
      do 4 lazymatch (eval cbv [v] in v) with
           | context C[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                let fx := constr:(f x) in
                (*idtac fx "(" f' ")";*)
                let do_vm _ := lazymatch (eval cbv [v] in v) with
                               | context C[fx]
                                 => pose fx as k;
                                      clear v;
                                      let C' := context C[k] in
                                      pose C' as v;
                                        (vm_compute in k; subst k; cbv beta iota in v)
                               end in
                lazymatch f' with
                | @type.try_transport => do_vm ()
                | @invert_expr.invert_App_Z_cast2 => do_vm ()
                | @invert_expr.invert_App_Z_cast => do_vm ()
                | @invert_expr.invert_App_curried => do_vm ()
                | @Option.bind => do_vm ()
                | @Crypto.Util.Option.bind => do_vm ()
                | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                | @IR.OfPHOAS.bounds_check => do_vm ()
                | @Language.Compilers.ToString.int.of_zrange_relaxed => do_vm ()
                | @fst => do_vm ()
                | @snd => do_vm ()
                | _ => progress cbn [f'] in v
                end
           end.
      do 1 lazymatch (eval cbv [v] in v) with
           | context C[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                let fx := constr:(f x) in
                (*idtac fx "(" f' ")";*)
                let do_vm _ := lazymatch (eval cbv [v] in v) with
                               | context C[fx]
                                 => pose fx as k;
                                      clear v;
                                      let C' := context C[k] in
                                      pose C' as v;
                                        (vm_compute in k; subst k; cbv beta iota in v)
                               end in
                lazymatch f' with
                | @type.try_transport => do_vm ()
                | @invert_expr.invert_App_Z_cast2 => do_vm ()
                | @invert_expr.invert_App_Z_cast => do_vm ()
                | @invert_expr.invert_App_curried => do_vm ()
                | @Option.bind => do_vm ()
                | @Crypto.Util.Option.bind => do_vm ()
                | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                | @IR.OfPHOAS.bounds_check => do_vm ()
                | @Language.Compilers.ToString.int.of_zrange_relaxed => do_vm ()
                | @NatUtil.nat_beq => do_vm ()
                | @fst => do_vm ()
                | @snd => do_vm ()
                | _ => progress cbn [f'] in v
                end
           end.

      set (k := IR.OfPHOAS.arith_expr_of_base_PHOAS _ _) in (value of v).
      clear v; rename k into v.
      cbv [IR.OfPHOAS.arith_expr_of_base_PHOAS] in v.
      vm_compute in k.
      subst k; cbv beta iota in v.
      cbn [IR.OfPHOAS.arith_expr_of_base_PHOAS] in v.
      set (k :=
      cbn -[F] in v.

      do 1 bar v F X.
      Notation "'LL'" := expr.LetIn.

      subst X; cbn -[F] in v.
      lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
      end.
      Time match (eval cbv [F] in F) with context G[expr.LetIn ?x ?f] => set (F' := f) in (value of F); set (X := x) in (value of F) end;
        subst F; rename F' into F.
      cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v.
      set (k := IR.OfPHOAS.make_assign_expr_of_PHOAS _ _ _ _ _ _) in (value of v).
      clear v.
      subst X.
      cbv [IR.OfPHOAS.make_assign_expr_of_PHOAS] in k.
      set (k' := type.try_transport _ _ _ _) in (value of k).
      vm_compute in k'; subst k'; cbv beta iota zeta in k.
      set (k' := invert_expr.invert_App_Z_cast _) in (value of k); vm_compute in k'.
      subst k'; cbv beta iota zeta in k.
      set (k' := invert_expr.invert_AppIdent_curried _) in (value of k); vm_compute in k'.
      subst k'; cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.arith_expr_of_PHOAS_args _) in (value of k).
      vm_compute in k'.
      subst k'; cbv beta iota zeta in k.
      set (k' := IR.OfPHOAS.arith_expr_of_base_PHOAS _ _) in (value of k).
      vm_compute in k'.
      subst k'; cbv beta iota zeta in k.
      rename k into v.
      lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
      end.
      Time match (eval cbv [F] in F) with context G[expr.LetIn ?x ?f] => set (F' := f) in (value of F); set (X := x) in (value of F) end;
        subst F; rename F' into F.
      cbn -[F] in v.
      subst X.
      cbv [IR.OfPHOAS.make_assign_expr_of_PHOAS] in v.
      cbn -[F] in v.
      About base.try_make_transport_cps.
      Arguments base.try_make_transport_cps _ _ _ !_ !_ / .
      cbn -[F] in v.
      cbn -[F] in v.
      lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
      end.
      lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
        clear F; rename F' into F.
      subst X.
      cbn -[F] in v.
      lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
      end;
        lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
        clear F; rename F' into F; subst X.
      cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v.
      cbv [IR.OfPHOAS.make_assign_expr_of_PHOAS] in v.
      set (k := type.try_transport _ _ _ _) in (value of v).
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := invert_expr.invert_App_Z_cast2 _) in (value of v); vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := invert_expr.invert_AppIdent_curried _) in (value of v);
        vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := IR.OfPHOAS.arith_expr_of_PHOAS_args _) in (value of v);
        vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := Crypto.Util.Option.bind _ _) in (value of v).
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := IR.OfPHOAS.bounds_check _ _ _ _ _ _) in (value of v).
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := fst _) in (value of v) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      set (k := snd _) in (value of v) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in v.
      repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v).
      cbn -[F] in v.
      lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
      end;
        lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
        clear F; rename F' into F; subst X.
      do 2 lazymatch (eval cbv [v] in v) with
           | context[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                lazymatch f' with
                | _ => cbn [f'] in v
                end
           end.
      do 1 lazymatch (eval cbv [v] in v) with
           | context[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                lazymatch f' with
                | @type.try_transport => set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v
                | _ => cbn [f'] in v
                end
           end.
      do 3 lazymatch (eval cbv [v] in v) with
           | context[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                let do_vm _ := set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v in
                lazymatch f' with
                | @type.try_transport => do_vm ()
                | @invert_expr.invert_App_Z_cast2 => do_vm ()
                | @invert_expr.invert_App_curried => do_vm ()
                | _ => progress cbn [f'] in v
                end
           end.
      do 2 lazymatch (eval cbv [v] in v) with
           | context[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                let do_vm _ := set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v in
                lazymatch f' with
                | @type.try_transport => do_vm ()
                | @invert_expr.invert_App_Z_cast2 => do_vm ()
                | @invert_expr.invert_App_curried => do_vm ()
                | @Option.bind => do_vm ()
                | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                | _ => progress cbn [f'] in v
                end
           end.
      do 1 lazymatch (eval cbv [v] in v) with
           | context[match ?f ?x with _ => _ end]
             => let f' := Tactics.Head.head f in
                let do_vm _ := set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v in
                lazymatch f' with
                | @type.try_transport => do_vm ()
                | @invert_expr.invert_App_Z_cast2 => do_vm ()
                | @invert_expr.invert_App_curried => do_vm ()
                | @Option.bind => do_vm ()
                | @Crypto.Util.Option.bind => do_vm ()
                | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                | _ => progress cbn [f'] in v
                end
           end.
      Time do 6 lazymatch (eval cbv [v] in v) with
                | context[match ?f ?x with _ => _ end]
                  => let f' := Tactics.Head.head f in
                     let do_vm _ := (set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v) in
                     lazymatch f' with
                     | @type.try_transport => do_vm ()
                     | @invert_expr.invert_App_Z_cast2 => do_vm ()
                     | @invert_expr.invert_App_curried => do_vm ()
                     | @Option.bind => do_vm ()
                     | @Crypto.Util.Option.bind => do_vm ()
                     | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                     | @IR.OfPHOAS.bounds_check => do_vm ()
                     | @fst => do_vm ()
                     | @snd => do_vm ()
                     | _ => progress cbn [f'] in v
                     end
                end.
      repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v).
      cbn -[F] in v.
      lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
      end;
        lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
        clear F; rename F' into F; subst X.
      cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v.
      Time do 2 lazymatch (eval cbv [v] in v) with
                | context[match ?f ?x with _ => _ end]
                  => let f' := Tactics.Head.head f in
                     let fx := constr:(f x) in
                     idtac fx "(" f' ")";
                     let do_vm _ := (set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v) in
                     lazymatch f' with
                     | @type.try_transport => do_vm ()
                     | @invert_expr.invert_App_Z_cast2 => do_vm ()
                     | @invert_expr.invert_App_curried => do_vm ()
                     | @Option.bind => do_vm ()
                     | @Crypto.Util.Option.bind => do_vm ()
                     | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                     | @IR.OfPHOAS.bounds_check => do_vm ()
                     | @fst => do_vm ()
                     | @snd => do_vm ()
                     | _ => progress cbn [f'] in v
                     end
                end.
      Time do 2 lazymatch (eval cbv [v] in v) with
                | context[match ?f ?x with _ => _ end]
                  => let f' := Tactics.Head.head f in
                     let fx := constr:(f x) in
                     idtac fx "(" f' ")";
                     let do_vm _ := (set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v) in
                     lazymatch f' with
                     | @type.try_transport => do_vm ()
                     | @invert_expr.invert_App_Z_cast2 => do_vm ()
                     | @invert_expr.invert_App_curried => do_vm ()
                     | @Option.bind => do_vm ()
                     | @Crypto.Util.Option.bind => do_vm ()
                     | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                     | @IR.OfPHOAS.bounds_check => do_vm ()
                     | @fst => do_vm ()
                     | @snd => do_vm ()
                     | _ => progress cbn [f'] in v
                     end
                end.
      Time do 2 lazymatch (eval cbv [v] in v) with
                | context[match ?f ?x with _ => _ end]
                  => let f' := Tactics.Head.head f in
                     let fx := constr:(f x) in
                     idtac fx "(" f' ")";
                     let do_vm _ := (set (k := f x) in (value of v); vm_compute in k; subst k; cbv beta iota in v) in
                     lazymatch f' with
                     | @type.try_transport => do_vm ()
                     | @invert_expr.invert_App_Z_cast2 => do_vm ()
                     | @invert_expr.invert_App_curried => do_vm ()
                     | @Option.bind => do_vm ()
                     | @Crypto.Util.Option.bind => do_vm ()
                     | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                     | @IR.OfPHOAS.bounds_check => do_vm ()
                     | @fst => do_vm ()
                     | @snd => do_vm ()
                     | _ => progress cbn [f'] in v
                     end
                end.
      Time repeat lazymatch (eval cbv [v] in v) with
                  | context C[match ?f ?x with _ => _ end]
                    => let f' := Tactics.Head.head f in
                       let fx := constr:(f x) in
                       (*idtac fx "(" f' ")";*)
                       let do_vm _ := lazymatch (eval cbv [v] in v) with
                                      | context C[fx]
                                        => pose fx as k;
                                             clear v;
                                             let C' := context C[k] in
                                             pose C' as v;
                                               (vm_compute in k; subst k; cbv beta iota in v)
                                      end in
                       lazymatch f' with
                       | @type.try_transport => do_vm ()
                       | @invert_expr.invert_App_Z_cast2 => do_vm ()
                       | @invert_expr.invert_App_curried => do_vm ()
                       | @Option.bind => do_vm ()
                       | @Crypto.Util.Option.bind => do_vm ()
                       | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                       | @IR.OfPHOAS.bounds_check => do_vm ()
                       | @fst => do_vm ()
                       | @snd => do_vm ()
                       | _ => progress cbn [f'] in v
                       end
                  end;
        repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v);
        cbn -[F] in v.
      do 2 (time (lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
                  end;
                  lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
                  clear F; rename F' into F; subst X;
                  cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v);
            time (repeat lazymatch (eval cbv [v] in v) with
                         | context C[match ?f ?x with _ => _ end]
                           => let f' := Tactics.Head.head f in
                              let fx := constr:(f x) in
                              (*idtac fx "(" f' ")";*)
                              let do_vm _ := lazymatch (eval cbv [v] in v) with
                                             | context C[fx]
                                               => pose fx as k;
                                                  clear v;
                                                  let C' := context C[k] in
                                                  pose C' as v;
                                                  (vm_compute in k; subst k; cbv beta iota in v)
                                             end in
                              lazymatch f' with
                              | @type.try_transport => do_vm ()
                              | @invert_expr.invert_App_Z_cast2 => do_vm ()
                              | @invert_expr.invert_App_curried => do_vm ()
                              | @Option.bind => do_vm ()
                              | @Crypto.Util.Option.bind => do_vm ()
                              | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                              | @IR.OfPHOAS.bounds_check => do_vm ()
                              | @fst => do_vm ()
                              | @snd => do_vm ()
                              | _ => progress cbn [f'] in v
                              end
                         end;
                  repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v);
                  cbn -[F] in v)).
      do 4 (time (lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
                  end;
                  lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
                  clear F; rename F' into F; subst X;
                  cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v);
            time (repeat lazymatch (eval cbv [v] in v) with
                         | context C[match ?f ?x with _ => _ end]
                           => let f' := Tactics.Head.head f in
                              let fx := constr:(f x) in
                              (*idtac fx "(" f' ")";*)
                              let do_vm _ := lazymatch (eval cbv [v] in v) with
                                             | context C[fx]
                                               => pose fx as k;
                                                  clear v;
                                                  let C' := context C[k] in
                                                  pose C' as v;
                                                  (vm_compute in k; subst k; cbv beta iota in v)
                                             end in
                              lazymatch f' with
                              | @type.try_transport => do_vm ()
                              | @invert_expr.invert_App_Z_cast2 => do_vm ()
                              | @invert_expr.invert_App_curried => do_vm ()
                              | @Option.bind => do_vm ()
                              | @Crypto.Util.Option.bind => do_vm ()
                              | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                              | @IR.OfPHOAS.bounds_check => do_vm ()
                              | @fst => do_vm ()
                              | @snd => do_vm ()
                              | _ => progress cbn [f'] in v
                              end
                         end;
                  repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v);
                  cbn -[F] in v)).
      Set Printing Depth 10000000.
      Ltac foo v F X :=
        (time (lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
               end;
               lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
               clear F; rename F' into F; subst X;
               cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v);
         time (repeat lazymatch (eval cbv [v] in v) with
                      | context C[match ?f ?x with _ => _ end]
                        => let f' := Tactics.Head.head f in
                           let fx := constr:(f x) in
                           (*idtac fx "(" f' ")";*)
                           let do_vm _ := lazymatch (eval cbv [v] in v) with
                                          | context C[fx]
                                            => pose fx as k;
                                               clear v;
                                               let C' := context C[k] in
                                               pose C' as v;
                                               (vm_compute in k; subst k; cbv beta iota in v)
                                          end in
                           lazymatch f' with
                           | @type.try_transport => do_vm ()
                           | @invert_expr.invert_App_Z_cast2 => do_vm ()
                           | @invert_expr.invert_App_curried => do_vm ()
                           | @Option.bind => do_vm ()
                           | @Crypto.Util.Option.bind => do_vm ()
                           | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                           | @IR.OfPHOAS.bounds_check => do_vm ()
                           | @fst => do_vm ()
                           | @snd => do_vm ()
                           | _ => progress cbn [f'] in v
                           end
                      end;
               repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v);
               cbn -[F] in v));
        time (repeat match (eval cbv [v] in v) with
                     | context C[match match ?x with inl l => @?LX l | inr r => @?RX r end with inl l' => @?L l' | inr r' => @?R r' end]
                       => let C' := context C[match x with inl l => match LX l with inl l' => L l' | inr r' => R r' end | inr r => match RX r with inl l' => L l' | inr r' => R r' end end] in
                          let C' := (eval cbv beta iota zeta in C') in
                          clear v; pose C' as v
                     end).
      do 2 foo v F X.
      Import ListNotations.
      do 4 foo v F X.
      Ltac bar v F X :=
        (time (lazymatch (eval cbv [v] in v) with context[F ?x] => pose (F x) as F'; change (F x) with F' in (value of v); subst F; rename F' into F; cbv beta iota zeta in F, v
               end;
               lazymatch (eval cbv [F] in F) with @expr.LetIn ?b ?i ?v ?A ?B ?x ?f => pose f as F'; pose x as X; change F with (@expr.LetIn b i v A B X F') in * end;
               clear F; rename F' into F; subst X;
               cbn [IR.OfPHOAS.expr_of_base_PHOAS] in v);
         time (repeat lazymatch (eval cbv [v] in v) with
                      | context C[match ?f ?x with _ => _ end]
                        => let f' := Tactics.Head.head f in
                           let fx := constr:(f x) in
                           (*idtac fx "(" f' ")";*)
                           let do_vm _ := lazymatch (eval cbv [v] in v) with
                                          | context C[fx]
                                            => pose fx as k;
                                               clear v;
                                               let C' := context C[k] in
                                               pose C' as v;
                                               (vm_compute in k; subst k; cbv beta iota in v)
                                          end in
                           lazymatch f' with
                           | @type.try_transport => do_vm ()
                           | @invert_expr.invert_App_Z_cast2 => do_vm ()
                           | @invert_expr.invert_App_curried => do_vm ()
                           | @Option.bind => do_vm ()
                           | @Crypto.Util.Option.bind => do_vm ()
                           | @IR.OfPHOAS.arith_expr_of_PHOAS_args => do_vm ()
                           | @IR.OfPHOAS.bounds_check => do_vm ()
                           | @fst => do_vm ()
                           | @snd => do_vm ()
                           | _ => progress cbn [f'] in v
                           end
                      end;
               repeat (set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v);
               cbn -[F] in v)).
      bar v F X.
      match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end.
      bar v F X.
      match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end.
      bar v F X.
      match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end.
      do 5 (bar v F X;
            match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end).
      do 5 (bar v F X;
            match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end).
      do 5 (bar v F X;
            match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end).
      do 5 (bar v F X;
            match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end).
      do 50 (bar v F X;
            match (eval cbv [v] in v) with match ?x with _ => _ end => clear v; pose x as v end).
      Notation "'LL'" := expr.LetIn.

      vm_compute in v.
      Set Printing All.
      do 4 foo v F X.
      do 16 foo v F X.
      do 4 foo v F X.
      Arguments

      set (k := option_map _ _) in (value of v) at 1; vm_compute in k; subst k; cbv beta iota in v.
      cbn [fst snd] in k.
      clear v.
      Arguments Z.pow_pos _ / .
      Arguments Language.Compilers.ToString.int.of_zrange_relaxed _ / .
      Arguments Language.Compilers.ToString.int.union _ / .
      Arguments Language.Compilers.ToString.int.bitwidth_of _ / .
      Arguments Language.Compilers.ToString.int.lgbitwidth_of _ / .
      cbn [Z.pow Z.sub Z.add Z.mul Z.pow_pos Pos.iter Pos.mul Z.opp Z.pos_sub Pos.pred_double Pos.add Pos.succ Z.log2_up Z.compare Z.eqb Z.ltb Z.eqb Pos.compare Pos.compare_cont Z.pred Z.log2 Z.succ Pos.size Z.max Z.leb Z.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_nat Pos.iter Z.mul Pos.of_succ_nat Z.max Z.min
                 Language.Compilers.ToString.int.of_zrange_relaxed
                 option_map
                 lower upper
                 Language.Compilers.ToString.int.union Language.Compilers.ToString.int.to_zrange Language.Compilers.ToString.int.is_signed Language.Compilers.ToString.int.bitwidth_of Language.Compilers.ToString.int.lgbitwidth_of
                 Operations.ZRange.union
          ] in k.
      cbn [Z.pow Z.sub Z.add Z.mul Z.pow_pos Pos.iter Pos.mul Z.opp Z.pos_sub Pos.pred_double Pos.add Pos.succ Z.log2_up Z.compare Z.eqb Z.ltb Z.eqb Pos.compare Pos.compare_cont Z.pred Z.log2 Z.succ Pos.size Z.max Z.leb Z.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_nat Pos.iter Z.mul Pos.of_succ_nat] in k.
      cbn [Operations.ZRange.union lower upper] in k.
      cbn [Z.pow Z.sub Z.add Z.mul Z.pow_pos Pos.iter Pos.mul Z.opp Z.pos_sub Pos.pred_double Pos.add Pos.succ Z.log2_up Z.compare Z.eqb Z.ltb Z.eqb Pos.compare Pos.compare_cont Z.pred Z.log2 Z.succ Pos.size Z.max Z.leb Z.to_nat Pos.to_nat Pos.iter_op Nat.add Z.of_nat Pos.iter Z.mul Pos.of_succ_nat Z.max Z.min] in k.
      cbn [Language.Compilers.ToString.int.of_zrange_relaxed lower upper] in k.
      cbn [] in k.
      .

      cbn in k.
      cbn in k.
      subst k; cbv beta iota zeta in v.
      set (k := option_map _ _) in (value of v) at 1; vm_compute in k.
      subst k; cbv beta iota zeta in v.
      cbn -[F] in v.
      subst X
      vm_compute in k.
      vm_compute in k.
      subst k; cbv beta iota zeta in v.

      vm
      set (k := (1 + 1)%Z) in (value of v).
      vm_compute in v.
      vm_compute in k.
      cbn [String


      vm_compute in v.
      pose (match snd v as v' return match v' with ErrorT.Error _ => _ | _ => _ end with
            | ErrorT.Error v => v
            | _ => I
            end) as v'.
      vm_compute in v'; clear v.
      pose (Show.show_lines false v') as s.
      cbv [Show.show_lines] in s.
      cbv [Pipeline.show_lines_ErrorMessage] in s.
      lazymatch (eval cbv [v'] in v') with context[fun var => @?F var] => set (F' := F) in (value of v') end.
      subst v'.
      cbv beta iota zeta in s.
      cbv [Show.maybe_wrap_parens_lines Show.show_lines Language.Compilers.ToString.PHOAS.expr.show_lines_Expr] in s.
      cbn [List.app] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_lines_Expr] in s.
      subst F'; cbv beta iota zeta in s.
      match (eval cbv [s] in s) with context G[expr.Abs ?f] => set (F := f) in (value of s) end.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_lines_expr] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_eta_cps] in s.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in s.
      lazymatch (eval cbv [s] in s) with context[F ?v] => pose (F v) as F'; change (F v) with F' in (value of s); subst F; rename F' into F; cbv beta iota zeta in F, s
      end.
      match (eval cbv [F] in F) with context G[expr.Abs ?f] => set (F' := f) in (value of F) end;
        subst F; rename F' into F.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in s.
      set (k := Decimal.decimal_string_of_pos 1) in (value of s); vm_compute in k; subst k.
      set (k := Decimal.decimal_string_of_pos _) in (value of s); vm_compute in k; subst k.
      cbn [String.append] in s.
      set (k := Pos.succ 1) in (value of s); vm_compute in k; subst k.
      set (k := Pos.succ _) in (value of s); vm_compute in k; subst k.
      cbn [String.append List.map List.app] in s.
      lazymatch (eval cbv [s] in s) with context[F ?v] => pose (F v) as F'; change (F v) with F' in (value of s); subst F; rename F' into F; cbv beta iota zeta in F, s
      end.
      match (eval cbv [F] in F) with context G[expr.LetIn ?x ?f] => set (F' := f) in (value of F); set (X := x) in (value of F) end;
        subst F; rename F' into F.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in s.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_expr_lines] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_eta_cps] in s.
      set (k := Decimal.decimal_string_of_pos _) in (value of s); vm_compute in k; subst k.
      set (k := Pos.succ _) in (value of s); vm_compute in k; subst k.
      cbn [String.append List.map List.app] in s.
      repeat match (eval cbv [s] in s) with
             | context C[let '(c, d) := let '(a, b) := ?x in @?F a b in @?G c d]
               => let C' := context C[let '(a, b) := x in let '(c, d) := F a b in G c d] in
                  clear s; pose C' as s; cbv beta iota zeta in s
             end.
      vm_compute in s.
      set (XX := Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps' _ _ X) in (value of s).
      clear s.
      subst X.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in XX.

      set (k := Decimal.decimal_string_of_pos _) in (value of XX); vm_compute in k; subst k.
      cbn [String.append List.map List.app] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_expr_lines] in XX.
      repeat match (eval cbv [XX] in XX) with
             | context C[let '(c, d) := let '(a, b) := ?x in @?F a b in @?G c d]
               => let C' := context C[let '(a, b) := x in let '(c, d) := F a b in G c d] in
                  clear XX; pose C' as XX; cbv beta iota zeta in XX
             end.
      unfold Language.Compilers.ToString.PHOAS.expr.show_eta_cps at 1 in (value of XX).
      cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in XX.
      cbn [String.append List.map List.app String.concat] in XX.
      repeat match (eval cbv [XX] in XX) with
             | context C[let '(c, d) := let '(a, b) := ?x in @?F a b in @?G c d]
               => let C' := context C[let '(a, b) := x in let '(c, d) := F a b in G c d] in
                  clear XX; pose C' as XX; cbv beta iota zeta in XX
             end.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_expr_lines] in XX.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_eta_cps] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in XX.
      cbv [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in XX.
      set (k := Language.Compilers.ToString.PHOAS.expr.show_expr_lines _ _ _ _ _) in (value of XX) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in XX.
      set (k := Language.Compilers.ToString.PHOAS.expr.show_expr_lines _ _ _ _ _) in (value of XX) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in XX.
      set (k := Language.Compilers.ToString.PHOAS.expr.show_expr_lines _ _ _ _ _) in (value of XX) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in XX.
      set (k := Language.Compilers.ToString.PHOAS.ident.show_ident_lvl _ _ _) in (value of XX).
      cbn in k.
      subst k; cbv beta iota zeta in XX.
      cbv [Ascii.NewLine] in XX.
      cbn [String.append List.map List.app String.concat] in XX.*)
    Abort.
     *)
  End __.
End debugging_go_build.

Module debugging_go_output.
  Import Crypto.PushButtonSynthesis.WordByWordMontgomery.
  Import Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
  Import Stringification.Go.
  Section __.
    Local Existing Instance Go.OutputGoAPI.
    Local Instance static : static_opt := false.
    Local Instance : internal_static_opt := false.
    Local Instance : inline_opt := false.
    Local Instance : inline_internal_opt := false.
    Local Instance : emit_primitives_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := true.
    Local Instance : widen_carry_opt := true.
    Local Instance : widen_bytes_opt := true.
    Local Instance : should_split_mul_opt := true. (* only for x64 *)

    Context (m : Z := 2^256 - 2^224 + 2^192 + 2^96 - 1)
            (machine_wordsize : Z := 64).

    (*
    Goal True.
      pose (smul m machine_wordsize "p256") as v.
      cbv [smul] in v.
      vm_compute in v.
      pose (match snd v as v' return match v' with ErrorT.Error _ => _ | _ => _ end with
            | ErrorT.Error v => v
            | _ => I
            end) as v'.
      vm_compute in v'; clear v.
      pose (Show.show_lines false v') as s.
      cbv [Show.show_lines] in s.
      cbv [Pipeline.show_lines_ErrorMessage] in s.
      (*
      lazymatch (eval cbv [v'] in v') with context[fun var => @?F var] => set (F' := F) in (value of v') end.
      subst v'.
      cbv beta iota zeta in s.
      cbv [Show.maybe_wrap_parens_lines Show.show_lines Language.Compilers.ToString.PHOAS.expr.show_lines_Expr] in s.
      cbn [List.app] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_lines_Expr] in s.
      subst F'; cbv beta iota zeta in s.
      match (eval cbv [s] in s) with context G[expr.Abs ?f] => set (F := f) in (value of s) end.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_lines_expr] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_eta_cps] in s.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in s.
      Notation "'λ'" := (expr.Abs _).
      Notation "'LET'" := (expr.LetIn _ _).
      lazymatch (eval cbv [s] in s) with context[F ?v] => pose (F v) as F'; change (F v) with F' in (value of s); subst F; rename F' into F; cbv beta iota zeta in F, s
      end.
      match (eval cbv [F] in F) with context G[expr.Abs ?f] => set (F' := f) in (value of F) end;
        subst F; rename F' into F.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in s.
      set (k := Decimal.decimal_string_of_pos 1) in (value of s); vm_compute in k; subst k.
      set (k := Decimal.decimal_string_of_pos _) in (value of s); vm_compute in k; subst k.
      Arguments String.append !_ !_ / .
      cbn [String.append] in s.
      set (k := Pos.succ 1) in (value of s); vm_compute in k; subst k.
      set (k := Pos.succ _) in (value of s); vm_compute in k; subst k.
      cbn [String.append List.map List.app] in s.
      lazymatch (eval cbv [s] in s) with context[F ?v] => pose (F v) as F'; change (F v) with F' in (value of s); subst F; rename F' into F; cbv beta iota zeta in F, s
      end.
      match (eval cbv [F] in F) with context G[expr.LetIn ?x ?f] => set (F' := f) in (value of F); set (X := x) in (value of F) end;
        subst F; rename F' into F.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in s.
      progress cbn [Language.Compilers.ToString.PHOAS.expr.show_expr_lines] in s.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_eta_cps] in s.
      set (k := Decimal.decimal_string_of_pos _) in (value of s); vm_compute in k; subst k.
      set (k := Pos.succ _) in (value of s); vm_compute in k; subst k.
      cbn [String.append List.map List.app] in s.
      repeat match (eval cbv [s] in s) with
             | context C[let '(c, d) := let '(a, b) := ?x in @?F a b in @?G c d]
               => let C' := context C[let '(a, b) := x in let '(c, d) := F a b in G c d] in
                  clear s; pose C' as s; cbv beta iota zeta in s
             end.
      vm_compute in s.
      set (XX := Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps' _ _ X) in (value of s).
      clear s.
      subst X.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in XX.

      set (k := Decimal.decimal_string_of_pos _) in (value of XX); vm_compute in k; subst k.
      cbn [String.append List.map List.app] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_expr_lines] in XX.
      repeat match (eval cbv [XX] in XX) with
             | context C[let '(c, d) := let '(a, b) := ?x in @?F a b in @?G c d]
               => let C' := context C[let '(a, b) := x in let '(c, d) := F a b in G c d] in
                  clear XX; pose C' as XX; cbv beta iota zeta in XX
             end.
      unfold Language.Compilers.ToString.PHOAS.expr.show_eta_cps at 1 in (value of XX).
      cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in XX.
      cbn [String.append List.map List.app String.concat] in XX.
      repeat match (eval cbv [XX] in XX) with
             | context C[let '(c, d) := let '(a, b) := ?x in @?F a b in @?G c d]
               => let C' := context C[let '(a, b) := x in let '(c, d) := F a b in G c d] in
                  clear XX; pose C' as XX; cbv beta iota zeta in XX
             end.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_expr_lines] in XX.
      cbv [Language.Compilers.ToString.PHOAS.expr.show_eta_cps] in XX.
      cbn [Language.Compilers.ToString.PHOAS.expr.show_eta_abs_cps'] in XX.
      cbv [Language.Compilers.ToString.PHOAS.expr.get_eta_cps_args] in XX.
      set (k := Language.Compilers.ToString.PHOAS.expr.show_expr_lines _ _ _ _ _) in (value of XX) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in XX.
      set (k := Language.Compilers.ToString.PHOAS.expr.show_expr_lines _ _ _ _ _) in (value of XX) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in XX.
      set (k := Language.Compilers.ToString.PHOAS.expr.show_expr_lines _ _ _ _ _) in (value of XX) at 1.
      vm_compute in k.
      subst k; cbv beta iota zeta in XX.
      set (k := Language.Compilers.ToString.PHOAS.ident.show_ident_lvl _ _ _) in (value of XX).
      cbn in k.
      subst k; cbv beta iota zeta in XX.
      cbv [Ascii.NewLine] in XX.
      cbn [String.append List.map List.app String.concat] in XX.*)
    Abort.
    *)
  End __.
End debugging_go_output.

Import Stringification.C.
Import Stringification.C.Compilers.

Local Existing Instance ToString.C.OutputCAPI.
Local Instance static : static_opt := true.
Local Instance : internal_static_opt := true.
Local Instance : inline_opt := true.
Local Instance : inline_internal_opt := true.
Local Instance : use_mul_for_cmovznz_opt := false.
Local Instance : emit_primitives_opt := true.

Module debugging_remove_mul_split_to_C_uint1_carry.
  Import PreExtra.
  Import LetIn.
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
      := Partition.partition (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
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

    Redirect "log"
      Compute
      Pipeline.BoundsPipelineToString
      "" (* prefix *)
      "mul"
      false (* subst01 *)
      false (* inline *)
      possible_values
      machine_wordsize
      ltac:(let r := Reify ((fun f g => dlet _ := ident.comment ("foo", f, g) in carry_mulmod limbwidth_num limbwidth_den s c n idxs f g)) in
            exact r)
             (fun _ _ => []) (* comment *)
             (Some loose_bounds, (Some loose_bounds, tt))
             (Some tight_bounds)
             (None, (None, tt))
             None
      : Pipeline.ErrorT _
    .
(* /*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 *   arg2: [[0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664], [0x0 ~> 0x1a666666666664]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc], [0x0 ~> 0x8cccccccccccc]]
 */
static void mul(uint64_t out1[5], const uint64_t arg1[5], const uint64_t arg2[5]) {
  /* (""foo"", arg1[0] :: arg1[1] :: arg1[2] :: arg1[3] :: arg1[4] :: [], arg2[0] :: arg2[1] :: arg2[2] :: arg2[3] :: arg2[4] :: []) */
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
      := Partition.partition (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
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
                           ((#uint64)%expr @ ($$x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x2 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x3 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[2]]))%expr_pat * ##19))))%expr_pat in
          expr_let x4 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[1]]))%expr_pat * ##19))))%expr_pat in
          expr_let x5 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x6 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x7 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[2]]))%expr_pat * ##19))))%expr_pat in
          expr_let x8 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[2]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x9 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($$x [[2]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x10 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[1]])) @
                            ((#uint64)%expr @ (((#uint64)%expr @ ($$x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x11 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[4]])) @ ((#uint64)%expr @ ($$x0 [[0]]))))%expr_pat in
          expr_let x12 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[3]])) @ ((#uint64)%expr @ ($$x0 [[1]]))))%expr_pat in
          expr_let x13 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[3]])) @ ((#uint64)%expr @ ($$x0 [[0]]))))%expr_pat in
          expr_let x14 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[2]])) @ ((#uint64)%expr @ ($$x0 [[2]]))))%expr_pat in
          expr_let x15 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[2]])) @ ((#uint64)%expr @ ($$x0 [[1]]))))%expr_pat in
          expr_let x16 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[2]])) @ ((#uint64)%expr @ ($$x0 [[0]]))))%expr_pat in
          expr_let x17 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[1]])) @ ((#uint64)%expr @ ($$x0 [[3]]))))%expr_pat in
          expr_let x18 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[1]])) @ ((#uint64)%expr @ ($$x0 [[2]]))))%expr_pat in
          expr_let x19 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[1]])) @ ((#uint64)%expr @ ($$x0 [[1]]))))%expr_pat in
          expr_let x20 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[1]])) @ ((#uint64)%expr @ ($$x0 [[0]]))))%expr_pat in
          expr_let x21 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[0]])) @ ((#uint64)%expr @ ($$x0 [[4]]))))%expr_pat in
          expr_let x22 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[0]])) @ ((#uint64)%expr @ ($$x0 [[3]]))))%expr_pat in
          expr_let x23 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[0]])) @ ((#uint64)%expr @ ($$x0 [[2]]))))%expr_pat in
          expr_let x24 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[0]])) @ ((#uint64)%expr @ ($$x0 [[1]]))))%expr_pat in
          expr_let x25 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($$x [[0]])) @ ((#uint64)%expr @ ($$x0 [[0]]))))%expr_pat in
          expr_let x26 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x7)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x4))))%expr_pat in
          expr_let x27 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x26)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x7)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x4))))%expr_pat in
          expr_let x28 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x9)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x26))))%expr_pat in
          expr_let x29 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x28)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x9)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x27))))%expr_pat in
          expr_let x30 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x10)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x28))))%expr_pat in
          expr_let x31 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x30)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x10)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x29))))%expr_pat in
          expr_let x32 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x25)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x30))))%expr_pat in
          expr_let x33 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x32)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x25)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x31))))%expr_pat in
          expr_let x34 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $$x32))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @
                                 ((#uint64)%expr @ ((#ident.fst)%expr @ $$x33)) @ ##13))%expr_pat))%expr_pat in
          expr_let x35 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $$x32))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x36 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x12)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x11))))%expr_pat in
          expr_let x37 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x36)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x12)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x11))))%expr_pat in
          expr_let x38 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x14)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x36))))%expr_pat in
          expr_let x39 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x38)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x14)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x37))))%expr_pat in
          expr_let x40 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x17)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x38))))%expr_pat in
          expr_let x41 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x40)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x17)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x39))))%expr_pat in
          expr_let x42 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x21)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x40))))%expr_pat in
          expr_let x43 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x42)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x21)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x41))))%expr_pat in
          expr_let x44 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x13)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x1))))%expr_pat in
          expr_let x45 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x44)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x13)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x1))))%expr_pat in
          expr_let x46 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x15)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x44))))%expr_pat in
          expr_let x47 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x46)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x15)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x45))))%expr_pat in
          expr_let x48 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x18)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x46))))%expr_pat in
          expr_let x49 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x48)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x18)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x47))))%expr_pat in
          expr_let x50 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x22)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x48))))%expr_pat in
          expr_let x51 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x50)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x22)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x49))))%expr_pat in
          expr_let x52 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x5)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x2))))%expr_pat in
          expr_let x53 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x52)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x5)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x2))))%expr_pat in
          expr_let x54 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x16)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x52))))%expr_pat in
          expr_let x55 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x54)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x16)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x53))))%expr_pat in
          expr_let x56 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x19)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x54))))%expr_pat in
          expr_let x57 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x56)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x19)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x55))))%expr_pat in
          expr_let x58 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x23)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x56))))%expr_pat in
          expr_let x59 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x58)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x23)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x57))))%expr_pat in
          expr_let x60 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x6)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x3))))%expr_pat in
          expr_let x61 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x60)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x6)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x3))))%expr_pat in
          expr_let x62 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x8)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x60))))%expr_pat in
          expr_let x63 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x62)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x8)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x61))))%expr_pat in
          expr_let x64 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x20)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x62))))%expr_pat in
          expr_let x65 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x64)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x20)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x63))))%expr_pat in
          expr_let x66 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x24)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x64))))%expr_pat in
          expr_let x67 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x66)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $$x24)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x65))))%expr_pat in
          expr_let x68 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $$x34) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $$x66))))%expr_pat in
          expr_let x69 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $$x68))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x67))%expr_pat))%expr_pat in
          expr_let x70 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $$x68))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $$x69) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x71 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $$x68))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x72 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $$x70) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $$x58))))%expr_pat in
          expr_let x73 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $$x72))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x59))%expr_pat))%expr_pat in
          expr_let x74 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $$x72))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $$x73) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x75 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $$x72))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x76 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $$x74) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $$x50))))%expr_pat in
          expr_let x77 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $$x76))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x51))%expr_pat))%expr_pat in
          expr_let x78 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $$x76))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $$x77) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x79 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $$x76))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x80 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $$x78) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $$x42))))%expr_pat in
          expr_let x81 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $$x80))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $$x43))%expr_pat))%expr_pat in
          expr_let x82 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $$x80))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $$x81) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x83 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $$x80))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x84 := ((#uint64)%expr @ (((#uint64)%expr @ $$x82)%expr_pat * ##19))%expr_pat in
          expr_let x85 := ((#uint64)%expr @
                           (((#uint64)%expr @ $$x35)%expr_pat + ((#uint64)%expr @ $$x84)%expr_pat))%expr_pat in
          expr_let x86 := ((#uint64)%expr @ (((#uint64)%expr @ $$x85)%expr_pat >> ##51))%expr_pat in
          expr_let x87 := ((#uint64)%expr @ (((#uint64)%expr @ $$x85)%expr_pat &' ##2251799813685247))%expr_pat in
          expr_let x88 := ((#uint64)%expr @
                           (((#uint64)%expr @ $$x86)%expr_pat + ((#uint64)%expr @ $$x71)%expr_pat))%expr_pat in
          expr_let x89 := ((#uint64)%expr @ (((#uint64)%expr @ $$x88)%expr_pat >> ##51))%expr_pat in
          expr_let x90 := ((#uint64)%expr @ (((#uint64)%expr @ $$x88)%expr_pat &' ##2251799813685247))%expr_pat in
          expr_let x91 := ((#uint64)%expr @
                           (((#uint64)%expr @ $$x89)%expr_pat + ((#uint64)%expr @ $$x75)%expr_pat))%expr_pat in
          [((#uint64)%expr @ $$x87)%expr_pat; ((#uint64)%expr @ $$x90)%expr_pat;
          ((#uint64)%expr @ $$x91)%expr_pat; ((#uint64)%expr @ $$x79)%expr_pat;
          ((#uint64)%expr @ $$x83)%expr_pat])
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
    Let r' := Z.modinv r m.
    Let m' := Eval vm_compute in Z.modinv (-m) r.

    Local Notation saturated_bounds := (Primitives.saturated_bounds n machine_wordsize).

    Definition bounds : list (ZRange.type.option.interp base.type.Z)
      := saturated_bounds (*List.map (fun u => Some r[0~>u]%zrange) upperbounds*).

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
      false (* inline *)
      None
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
      set (k := Pipeline.BoundsPipelineWithDebug _ _ _ _ _) in (value of v).
      clear v.
      cbv [mul] in k.
      Import WordByWordMontgomeryReificationCache.
      cbv -[Pipeline.BoundsPipelineWithDebug reified_mul_gen] in k.
      cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline LetIn.Let_In] in k.
      let k' := fresh in rename k into k'; epose (DebugMonad.Debug.eval_result k') as k; subst k'.
      cbv [Rewriter.Util.LetIn.Let_In DebugMonad.Debug.eval_result DebugMonad.Debug.sequence Pipeline.debug_after_rewrite DebugMonad.Debug.ret] in k.
      vm_compute Pipeline.debug_rewriting in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (v := CheckedPartialEvaluateWithBounds _ _ _ _ _ _ _) in (value of k).
      Notation INL := (inl _).
      vm_compute in v.
      Notation IDD := (id _).
      lazymatch (eval cbv [v] in v) with
      | @inl ?A ?B ?x => pose (id x) as v'; change v with (@inl A B v') in (value of k); clear v
      end.
      cbv beta iota in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      unfold DebugMonad.Debug.bind in (value of k) at 1; cbn [snd] in k.
      set (v := Pipeline.RewriteAndEliminateDeadAndInline _ _ _ _ _ _) in (value of k) at 1.
      vm_compute in v; clear v';
      lazymatch (eval cbv [v] in v) with
      | ?x => pose (id x) as v'; change v with v' in (value of k); clear v
      end.
      cbv beta iota in k.
      (*
      set (v'' := MulSplit.Compilers.RewriteRules.RewriteMulSplit _ _ _ _) in (value of k).
      vm_compute in v; clear v';
      lazymatch (eval cbv [v] in v) with
      | ?x => pose (id x) as v'; change v with v' in (value of v''); clear v
      end.
      cbv [id] in v'.
      vm_compute in v''.
       *)
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
      := Partition.partition (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
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
         true [64; 128]
         ltac:(let r := Reify (fun f g
                               => (  (addmod limbwidth_num limbwidth_den n f g)
                              )) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true [64; 128]
         ltac:(let r := Reify (fun f g
                               => (  (add (weight limbwidth_num limbwidth_den) n f g)
                              )) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true [64; 128]
         ltac:(let r := Reify (fun f g
                               => let a_a := to_associational (weight limbwidth_num limbwidth_den) n f in
                                  let b_a := to_associational (weight limbwidth_num limbwidth_den) n g in from_associational (weight limbwidth_num limbwidth_den) n (a_a ++ b_a)
                              ) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true [64; 128]
         ltac:(let r := Reify (fun f (g : list Z)
                               => let a_a := to_associational (weight limbwidth_num limbwidth_den) n f in
                                  a_a) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Redirect "log" Compute
      (Pipeline.BoundsPipeline
         true [64; 128]
         ltac:(let r := Reify (fun (f g : list Z)
                               => let a_a := combine (map (weight limbwidth_num limbwidth_den) (seq 0 n)) f in
                                  a_a) in
               exact r)
                (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
                ZRange.type.base.option.None).

    Definition foo := (Pipeline.BoundsPipeline
                         true [64; 128]
                         ltac:(let r := Reify (combine [1; 2] [1; 2]) in
                               exact r)
                                tt
                                ZRange.type.base.option.None).

  (*
  Goal True.
    pose foo as X; cbv [foo] in X.
    clear -X.
    cbv [Pipeline.BoundsPipelineWithDebug Pipeline.PreBoundsPipeline LetIn.Let_In] in X.
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
    := Partition.partition (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
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
        true [64; 128]
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
       false (* inline *)
       possible_values machine_wordsize
       ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n [3; 7; 4; 0; 5; 1; 6; 2; 7; 3; 4; 0]%nat)) in
             exact r)
              (fun _ _ => []) (* comment *)
              (Some loose_bounds, (Some loose_bounds, tt))
              (Some tight_bounds)
              (None, (None, tt))
              None
    : Pipeline.ErrorT _.

  Time Redirect "log" Compute
       Pipeline.BoundsPipeline
       false (* subst01 *)
       possible_values
       ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n [3; 7; 4; 0; 5; 1; 6; 2; 7; 3; 4; 0]%nat)) in
             exact r)
              (Some loose_bounds, (Some loose_bounds, tt))
              (Some tight_bounds).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n [3; 7; 4; 0; 5; 1; 6; 2; 7; 3; 4; 0]%nat)) in
              exact r)
               (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
               ZRange.type.base.option.None).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n []%nat)) in
              exact r)
               (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
               ZRange.type.base.option.None).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
        ltac:(let r := Reify (fun f g
                              => (  (mulmod (weight limbwidth_num limbwidth_den) s c n f g)
                                    )) in
              exact r)
               (Some (repeat (@None _) n), (Some (repeat (@None _) n), tt))
               ZRange.type.base.option.None).

  Time Redirect "log" Compute
     (Pipeline.BoundsPipeline
        true [64; 128]
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
