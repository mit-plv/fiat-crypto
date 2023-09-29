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
Require Import Crypto.Arithmetic.WeightStream.
Require Import Crypto.Arithmetic.SaturatedPseudoMersenne.
Require Import Crypto.Arithmetic.P256ADX.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Crypto.PushButtonSynthesis.Primitives.
Require Crypto.Stringification.C.
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

Module debugging_scheduled_saturated_arithmetic.
  Section __.
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
    Let machine_wordsize := 64.
    (** ================================================= *)
    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

    Let n : nat := 4.
    Let boundsn : list (ZRange.type.option.interp base.type.Z) := repeat (Some r[0 ~> (2^machine_wordsize - 1)]%zrange) n.

    Import IdentifiersBasicGENERATED.Compilers.
    Import API.Compilers.
    Import APINotations.Compilers.

    Import WeightStream.Saturated.
    Import SaturatedPseudoMersenne.

    Definition bound (_ : Datatypes.nat) := Z.to_pos (2^64).

    Goal True.
    assert_fails (idtac;
      let e := constr:(weight (fun _ => 10)%positive 2) in
      let e := eval cbv [stream.map weight] in e in
      (* let e := eval cbv delta [stream.prefixes] in e in *)
      (* idtac e; *)
      let r := Reify e in pose r).
    assert_succeeds (idtac;
      let e := constr:(weight (fun _ => 10)%positive 2) in
      let e := eval cbv [stream.map weight] in e in
      let e := eval cbv delta [stream.prefixes] in e in
      (* idtac e; *)
      let r := Reify e in pose r).
    Abort.

    Goal True.
    pose (
         (Pipeline.BoundsPipelineWithDebug
            false (* subst01 *)
            possible_values
            ltac:(
              let e := constr:((fun xs ys => addmod bound 38 xs (map Z.opp ys))) in
              let r := Reify e in
              exact r)
              (Some boundsn, (Some boundsn, tt))
              (Some boundsn)
         )) as k.
    vm_compute in k.
    Abort.

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_add"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(
                  let e := constr:(addmod bound 38) in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn)
                   (None, (None, tt))
                   (None)).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_sub"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(
                  let e := constr:(submod bound 38) in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn)
                   (None, (None, tt))
                   (None)).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_scmul"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let e := constr:(fun ys x =>
                    let (lo, hi) := add_mul_small bound [] x ys in
                    reduce bound 1%nat 38 lo [hi]
                  ) in
                  let e := eval cbv delta [reduce reduce' add_mul_small product_scan stream.map weight stream.prefixes] in e in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some (r[0 ~>2^58-1]%zrange), tt))
                   (Some boundsn)
                   (None, (None, tt))
                   (None)).
         (* with add_mul_limb Check eq_refl true : (0x97ffffffffffffda <=? 0xffffffffffffffda) = true. *)

    Goal (Z.to_nat (weight bound 4/(2^255-19))) = 2%nat. trivial. all: fail. Abort.

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_canon"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let e := constr:(fun x => dlet x := x in condsubs bound 2 x (encode bound 4 (2^255-19))) in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, tt)
                   (Some boundsn)
                   (None, tt)
                   (None)).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_select"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let e := constr:(select) in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some (r[0 ~>1]%zrange), (Some boundsn, (Some boundsn, tt)))
                   (Some boundsn)
                   (None, (None, (None, tt)))
                   (None)).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_cswap"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let e := constr:(cswap') in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some (r[0 ~>1]%zrange), (Some boundsn, (Some boundsn, tt)))
                   ((Some boundsn, Some boundsn))
                   (None, (None, (None, tt)))
                   (None, None)).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_divmod255"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) (* needs to be reduced to reify correctly *) in
                  let r := Reify (fun xs => divmodw bound xs (2^255)) in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, tt)
                   (Some (r[0 ~>1]%zrange), Some boundsn)
                   (None, tt)
                   (None, None)).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (Pipeline.BoundsPipelineToString
            "fiat_" "fe4_mul_no_reduce"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let e := constr:(mul bound) in
            let e := eval cbv delta [mulmod mul add_mul add_mul_limb_ product_scan_ add_mul_small product_scan' reduce' product_scan stream.map weight stream.prefixes] in e in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (*
                   (Some (boundsn++boundsn))
                    *) None
                   (None, (None, tt))
                   (None)
          : Pipeline.ErrorT _).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (
         Pipeline.BoundsPipelineToString
            "fiat_" "fe4_mul"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(
                  let e := constr:(mulmod bound 4 38) in
                  let e := eval cbv delta [mulmod mul add_mul add_mul_limb_ product_scan_ add_mul_small product_scan' reduce' product_scan stream.map weight stream.prefixes] in e in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (*
                   (Some boundsn)
                    *) None
                   (None, (None, tt))
                   (None)
          : Pipeline.ErrorT _).

Import P256ADX.

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (
         Pipeline.BoundsPipelineToString
            "fiat_" "sqr4"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(
                  let e := constr:(sqr4) in
                  let e := eval cbv delta [sqr4 two_steps_of_p256_montgomery_reduction p256_mul mul add_mul add_mul_limb_ add_mul_limb_ reduce' product_scan product_scan_ stream.map weight stream.prefixes] in e in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, tt)
                   (Some (boundsn++boundsn))
                   (None, tt)
                   (None)
          : Pipeline.ErrorT _).

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (
         Pipeline.BoundsPipelineToString
            "fiat_" "p256red2w"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(let e := constr:(two_steps_of_p256_montgomery_reduction) in
                  let e := eval cbv delta [p256_sqr sqr4 two_steps_of_p256_montgomery_reduction p256_mul mul add_mul add_mul_limb_ product_scan product_scan_ stream.map weight stream.prefixes stream.firstn condsub] in e in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some (repeat (Some r[0 ~> (2^64 - 1)]%zrange) 6), tt)
                   (Some (repeat (Some r[0 ~> (2^64 - 1)]%zrange) 4 ++ [(Some r[0 ~> 2]%zrange)]))
                   (None, tt)
                   None
          : Pipeline.ErrorT _).
         (*
  fiat_mulx_u64(&x1, &x2, UINT64_C(0x100000000), (arg1[0]));
  fiat_addcarryx_u64(&x3, &x4, 0x0, (arg1[1]), x1);
  fiat_mulx_u64(&x5, &x6, UINT64_C(0x100000000), x3);
  fiat_addcarryx_u64(&x7, &x8, x4, (arg1[2]), x2);
  fiat_addcarryx_u64(&x9, &x10, 0imbx0, x7, x5);
  fiat_mulx_u64(&x11, &x12, UINT64_C(0xffffffff00000001), (arg1[0]));
  fiat_addcarryx_u64(&x13, &x14, x8, (arg1[3]), x6);
  fiat_addcarryx_u64(&x15, &x16, x10, x13, x11);
  fiat_mulx_u64(&x17, &x18, UINT64_C(0xffffffff00000001), x3);
  fiat_addcarryx_u64(&x19, &x20, x14, (arg1[4]), x12);
  fiat_addcarryx_u64(&x21, &x22, x16, x19, x17);
  fiat_addcarryx_u64(&x23, &x24, x20, (arg1[5]), x18);
  fiat_addcarryx_u64(&x25, &x26, x22, x23, 0x0);
  x27 = ((uint64_t)x24 + x26);
  out1[0] = x9;
  out1[1] = x15;
  out1[2] = x21;
  out1[3] = x25;
  out1[4] = x27;
          *)

    Time Redirect "log"
         Compute
         Show.show (* [show] for pretty-printing of the AST without needing lots of imports *)
         (
         Pipeline.BoundsPipelineToString
            "fiat_" "p256_mul"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(
                  let e := constr:(p256_mul') in
                  let e := eval cbv delta [p256_sqr sqr4 two_steps_of_p256_montgomery_reduction p256_mul' mul add_mul add_mul_limb_ product_scan product_scan_ stream.map weight stream.prefixes stream.firstn condsub] in e in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, (Some boundsn, tt))
                   (Some boundsn)
                   (None, (None, tt))
                   (None)
          : Pipeline.ErrorT _).
(*fiat_mulx_u64(&x3, &x4, (arg1[0]), (arg2[0]));
  fiat_mulx_u64(&x5, &x6, (arg1[0]), (arg2[1]));
  fiat_addcarryx_u64(&x7, &x8, 0x0, x4, x5);
  fiat_mulx_u64(&x9, &x10, (arg1[0]), (arg2[2]));
  fiat_addcarryx_u64(&x11, &x12, x8, x6, x9);
  fiat_mulx_u64(&x13, &x14, (arg1[0]), (arg2[3]));
  fiat_addcarryx_u64(&x15, &x16, x12, x10, x13);
  x17 = (x16 + x14);
  fiat_mulx_u64(&x18, &x19, (arg1[1]), (arg2[0]));
  fiat_addcarryx_u64(&x20, &x21, 0x0, x7, x18);
  fiat_mulx_u64(&x22, &x23, (arg1[1]), (arg2[1]));
  fiat_addcarryx_u64(&x24, &x25, 0x0, x11, x19);
  fiat_addcarryx_u64(&x26, &x27, x21, x24, x22);
  fiat_mulx_u64(&x28, &x29, (arg1[1]), (arg2[2]));
  fiat_addcarryx_u64(&x30, &x31, x25, x15, x23);
  fiat_addcarryx_u64(&x32, &x33, x27, x30, x28);
  fiat_mulx_u64(&x34, &x35, (arg1[1]), (arg2[3]));
  fiat_addcarryx_u64(&x36, &x37, x31, x17, x29);
  fiat_addcarryx_u64(&x38, &x39, x33, x36, x34);
  x40 = (x37 + x35);
  fiat_addcarryx_u64(&x41, &x42, x39, x40, 0x0);
  fiat_mulx_u64(&x43, &x44, UINT64_C(0x100000000), x3);
  fiat_addcarryx_u64(&x45, &x46, 0x0, x20, x43);
  fiat_mulx_u64(&x47, &x48, UINT64_C(0x100000000), x45);
  fiat_addcarryx_u64(&x49, &x50, x46, x26, x44);
  fiat_addcarryx_u64(&x51, &x52, 0x0, x49, x47);
  fiat_mulx_u64(&x53, &x54, UINT64_C(0xffffffff00000001), x3);
  fiat_addcarryx_u64(&x55, &x56, x50, x32, x48);
  fiat_addcarryx_u64(&x57, &x58, x52, x55, x53);
  fiat_mulx_u64(&x59, &x60, UINT64_C(0xffffffff00000001), x45);
  fiat_addcarryx_u64(&x61, &x62, x56, x38, x54);
  fiat_addcarryx_u64(&x63, &x64, x58, x61, x59);
  fiat_addcarryx_u64(&x65, &x66, x62, x41, x60);
  fiat_addcarryx_u64(&x67, &x68, x64, x65, 0x0);
  x69 = ((uint64_t)x68 + x66);
  fiat_mulx_u64(&x70, &x71, x1, (arg2[0]));
  fiat_addcarryx_u64(&x72, &x73, 0x0, x51, x70);
  fiat_mulx_u64(&x74, &x75, x1, (arg2[1]));
  fiat_addcarryx_u64(&x76, &x77, 0x0, x57, x71);
  fiat_addcarryx_u64(&x78, &x79, x73, x76, x74);
  fiat_mulx_u64(&x80, &x81, x1, (arg2[2]));
  fiat_addcarryx_u64(&x82, &x83, x77, x63, x75);
  fiat_addcarryx_u64(&x84, &x85, x79, x82, x80);
  fiat_mulx_u64(&x86, &x87, x1, (arg2[3]));
  fiat_addcarryx_u64(&x88, &x89, x83, x67, x81);
  fiat_addcarryx_u64(&x90, &x91, x85, x88, x86);
  x92 = (x89 + x87);
  fiat_addcarryx_u64(&x93, &x94, x91, x92, 0x0);
  fiat_addcarryx_u64(&x95, &x96, 0x0, x69, x93);
  fiat_mulx_u64(&x97, &x98, x2, (arg2[0]));
  fiat_addcarryx_u64(&x99, &x100, 0x0, x78, x97);
  fiat_mulx_u64(&x101, &x102, x2, (arg2[1]));
  fiat_addcarryx_u64(&x103, &x104, 0x0, x84, x98);
  fiat_addcarryx_u64(&x105, &x106, x100, x103, x101);
  fiat_mulx_u64(&x107, &x108, x2, (arg2[2]));
  fiat_addcarryx_u64(&x109, &x110, x104, x90, x102);
  fiat_addcarryx_u64(&x111, &x112, x106, x109, x107);
  fiat_mulx_u64(&x113, &x114, x2, (arg2[3]));
  fiat_addcarryx_u64(&x115, &x116, x110, x95, x108);
  fiat_addcarryx_u64(&x117, &x118, x112, x115, x113);
  x119 = (x116 + x114);
  fiat_addcarryx_u64(&x120, &x121, x118, x119, 0x0);
  fiat_addcarryx_u64(&x122, &x123, 0x0, x96, x120);
  fiat_mulx_u64(&x124, &x125, UINT64_C(0x100000000), x72);
  fiat_addcarryx_u64(&x126, &x127, 0x0, x99, x124);
  fiat_mulx_u64(&x128, &x129, UINT64_C(0x100000000), x126);
  fiat_addcarryx_u64(&x130, &x131, x127, x105, x125);
  fiat_addcarryx_u64(&x132, &x133, 0x0, x130, x128);
  fiat_mulx_u64(&x134, &x135, UINT64_C(0xffffffff00000001), x72);
  fiat_addcarryx_u64(&x136, &x137, x131, x111, x129);
  fiat_addcarryx_u64(&x138, &x139, x133, x136, x134);
  fiat_mulx_u64(&x140, &x141, UINT64_C(0xffffffff00000001), x126);
  fiat_addcarryx_u64(&x142, &x143, x137, x117, x135);
  fiat_addcarryx_u64(&x144, &x145, x139, x142, x140);
  fiat_addcarryx_u64(&x146, &x147, x143, x122, x141);
  fiat_addcarryx_u64(&x148, &x149, x145, x146, 0x0);
  x150 = ((uint64_t)x147 + x123);
  x151 = (x149 + x150);
  fiat_subborrowx_u64(&x152, &x153, 0x0, x132, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x154, &x155, x153, x138, UINT32_C(0xffffffff));
  fiat_subborrowx_u64(&x156, &x157, x155, x144, 0x0);
  fiat_subborrowx_u64(&x158, &x159, x157, x148, UINT64_C(0xffffffff00000001));
  fiat_subborrowx_u64(&x160, &x161, x159, x151, 0x0);
  fiat_cmovznz_u64(&x162, x161, x152, x132);
  fiat_cmovznz_u64(&x163, x161, x154, x138);
  fiat_cmovznz_u64(&x164, x161, x156, x144);
  fiat_cmovznz_u64(&x165, x161, x158, x148);
  out1[0] = x162;
  out1[1] = x163;
  out1[2] = x164;
  out1[3] = x165; *)

    (*
    Require Stringification.JSON.
    Local Existing Instance JSON.JSON.OutputJSONAPI.
    *)
    From bedrock2 Require Import PrintString.
    Goal False.
      let t := constr:(match
         (
         Pipeline.BoundsPipelineToString
            "fiat_" "p256_sqr"
            false (* subst01 *)
            false (* inline *)
            possible_values
            machine_wordsize
            ltac:(
                  let e := constr:(p256_sqr') in
                  let e := eval cbv delta [p256_sqr' sqr4 two_steps_of_p256_montgomery_reduction p256_mul mul add_mul add_mul_limb_ product_scan product_scan_ stream.map weight stream.prefixes stream.firstn condsub] in e in
                  let r := Reify e in
                  exact r)
                   (fun _ _ => []) (* comment *)
                   (Some boundsn, tt)
                   (Some boundsn)
                   (None, tt)
                   (None)
          : Pipeline.ErrorT _)
          with ErrorT.Success s => fst s | _ => "" end
        ) in
      let t := eval vm_compute in t in
      print_string t.
(*fiat_mulx_u64(&x1, &x2, (arg1[1]), (arg1[2]));
  fiat_mulx_u64(&x3, &x4, (arg1[0]), (arg1[1]));
  fiat_mulx_u64(&x5, &x6, (arg1[0]), (arg1[2]));
  fiat_addcarryx_u64(&x7, &x8, 0x0, x4, x5);
  fiat_mulx_u64(&x9, &x10, (arg1[0]), (arg1[3]));
  fiat_addcarryx_u64(&x11, &x12, 0x0, x1, x6);
  fiat_addcarryx_u64(&x13, &x14, x8, x11, x9);
  fiat_mulx_u64(&x15, &x16, (arg1[1]), (arg1[3]));
  fiat_addcarryx_u64(&x17, &x18, x12, x2, x10);
  fiat_addcarryx_u64(&x19, &x20, x14, x17, x15);
  fiat_mulx_u64(&x21, &x22, (arg1[2]), (arg1[3]));
  x23 = (x18 + x16);
  fiat_addcarryx_u64(&x24, &x25, x20, x23, x21);
  x26 = (x25 + x22);
  fiat_addcarryx_u64(&x27, &x28, 0x0, x3, x3);
  fiat_addcarryx_u64(&x29, &x30, x28, x7, x7);
  fiat_addcarryx_u64(&x31, &x32, x30, x13, x13);
  fiat_addcarryx_u64(&x33, &x34, x32, x19, x19);
  fiat_addcarryx_u64(&x35, &x36, x34, x24, x24);
  fiat_addcarryx_u64(&x37, &x38, x36, x26, x26);
  fiat_mulx_u64(&x39, &x40, (arg1[3]), (arg1[3]));
  fiat_mulx_u64(&x41, &x42, (arg1[2]), (arg1[2]));
  fiat_mulx_u64(&x43, &x44, (arg1[1]), (arg1[1]));
  fiat_mulx_u64(&x45, &x46, (arg1[0]), (arg1[0]));
  fiat_addcarryx_u64(&x47, &x48, 0x0, x27, x46);
  fiat_addcarryx_u64(&x49, &x50, x48, x29, x43);
  fiat_addcarryx_u64(&x51, &x52, x50, x31, x44);
  fiat_addcarryx_u64(&x53, &x54, x52, x33, x41);
  fiat_addcarryx_u64(&x55, &x56, x54, x35, x42);
  fiat_addcarryx_u64(&x57, &x58, x56, x37, x39);
  fiat_addcarryx_u64(&x59, &x60, x58, x38, x40);
  fiat_mulx_u64(&x61, &x62, UINT64_C(0x100000000), x45);
  fiat_addcarryx_u64(&x63, &x64, 0x0, x47, x61);
  fiat_mulx_u64(&x65, &x66, UINT64_C(0x100000000), x63);
  fiat_addcarryx_u64(&x67, &x68, x64, x49, x62);
  fiat_addcarryx_u64(&x69, &x70, 0x0, x67, x65);
  fiat_mulx_u64(&x71, &x72, UINT64_C(0xffffffff00000001), x45);
  fiat_addcarryx_u64(&x73, &x74, x68, x51, x66);
  fiat_addcarryx_u64(&x75, &x76, x70, x73, x71);
  fiat_mulx_u64(&x77, &x78, UINT64_C(0xffffffff00000001), x63);
  fiat_addcarryx_u64(&x79, &x80, x74, x53, x72);
  fiat_addcarryx_u64(&x81, &x82, x76, x79, x77);
  fiat_addcarryx_u64(&x83, &x84, x80, x55, x78);
  fiat_addcarryx_u64(&x85, &x86, x82, x83, 0x0);
  fiat_addcarryx_u64(&x87, &x88, x84, x57, 0x0);
  fiat_addcarryx_u64(&x89, &x90, x86, x87, 0x0);
  fiat_addcarryx_u64(&x91, &x92, x88, x59, 0x0);
  fiat_addcarryx_u64(&x93, &x94, x90, x91, 0x0);
  x95 = ((uint64_t)x94 + x92);
  fiat_mulx_u64(&x96, &x97, UINT64_C(0x100000000), x69);
  fiat_addcarryx_u64(&x98, &x99, 0x0, x75, x96);
  fiat_mulx_u64(&x100, &x101, UINT64_C(0x100000000), x98);
  fiat_addcarryx_u64(&x102, &x103, x99, x81, x97);
  fiat_addcarryx_u64(&x104, &x105, 0x0, x102, x100);
  fiat_mulx_u64(&x106, &x107, UINT64_C(0xffffffff00000001), x69);
  fiat_addcarryx_u64(&x108, &x109, x103, x85, x101);
  fiat_addcarryx_u64(&x110, &x111, x105, x108, x106);
  fiat_mulx_u64(&x112, &x113, UINT64_C(0xffffffff00000001), x98);
  fiat_addcarryx_u64(&x114, &x115, x109, x89, x107);
  fiat_addcarryx_u64(&x116, &x117, x111, x114, x112);
  fiat_addcarryx_u64(&x118, &x119, x115, x93, x113);
  fiat_addcarryx_u64(&x120, &x121, x117, x118, 0x0);
  x122 = (x119 + x95);
  x123 = (x121 + x122);
  fiat_subborrowx_u64(&x124, &x125, 0x0, x104, UINT64_C(0xffffffffffffffff));
  fiat_subborrowx_u64(&x126, &x127, x125, x110, UINT32_C(0xffffffff));
  fiat_subborrowx_u64(&x128, &x129, x127, x116, 0x0);
  fiat_subborrowx_u64(&x130, &x131, x129, x120, UINT64_C(0xffffffff00000001));
  fiat_subborrowx_u64(&x132, &x133, x131, x123, 0x0);
  fiat_cmovznz_u64(&x134, x133, x124, x104);
  fiat_cmovznz_u64(&x135, x133, x126, x110);
  fiat_cmovznz_u64(&x136, x133, x128, x116);
  fiat_cmovznz_u64(&x137, x133, x130, x120);
  out1[0] = x134;
  out1[1] = x135;
  out1[2] = x136;
   out1[3] = x137;*)
    Abort.


  End __.
End debugging_scheduled_saturated_arithmetic.
