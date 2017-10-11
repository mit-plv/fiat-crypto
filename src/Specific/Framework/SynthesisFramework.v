Require Import Crypto.Specific.Framework.ArithmeticSynthesis.BasePackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.DefaultsPackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.FreezePackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.KaratsubaPackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.LadderstepPackage.
Require Import Crypto.Specific.Framework.ArithmeticSynthesis.MontgomeryPackage.
Require Import Crypto.Specific.Framework.CurveParametersPackage.
Require Import Crypto.Specific.Framework.ReificationTypesPackage.
Require Import Crypto.Specific.Framework.MontgomeryReificationTypesPackage.
Require Import Crypto.Specific.Framework.Packages.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Util.TagList.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Specific.Framework.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.

Module Export Exports.
  Export ArithmeticSynthesis.Defaults.Exports.
  Export ArithmeticSynthesis.Freeze.Exports.
End Exports.

(* Alisases for exporting *)
Module Type PrePackage := PrePackage.
Module Tag.
  Notation Context := Tag.Context (only parsing).
End Tag.

Module Export MakeSynthesisTactics.
  Ltac add_Synthesis_package pkg curve extra_prove_mul_eq extra_prove_square_eq :=
    let CP := get_fill_CurveParameters curve in
    let P_default_mul _ := default_mul CP in
    let P_extra_prove_mul_eq := extra_prove_mul_eq in
    let P_default_square _ := default_square CP in
    let P_extra_prove_square_eq := extra_prove_square_eq in
    let pkg := Tag.local_update pkg TAG.CP CP in
    let pkg := add_CurveParameters_package pkg in
    let pkg := Tag.strip_local pkg in
    let pkg := add_Base_package pkg in
    let pkg := add_ReificationTypes_package pkg in
    let pkg := add_Karatsuba_package pkg in
    let pkg := add_Montgomery_package pkg in
    let pkg := add_MontgomeryReificationTypes_package pkg in
    (* N.B. freeze is a "default" and must come after montgomery, which disables it *)
    let pkg := add_Freeze_package pkg in
    (* N.B. the Defaults must come after other possible ways of adding the _sig lemmas *)
    let pkg := add_Defaults_package pkg P_default_mul P_extra_prove_mul_eq P_default_square P_extra_prove_square_eq in
    (* N.B. Ladderstep must come after Defaults *)
    let pkg := add_Ladderstep_package pkg in
    pkg.

  Ltac get_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq :=
    let pkg := constr:(Tag.empty) in
    add_Synthesis_package pkg curve extra_prove_mul_eq extra_prove_square_eq.

  Ltac make_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq :=
    let pkg := get_Synthesis_package curve extra_prove_mul_eq extra_prove_square_eq in
    exact pkg.
End MakeSynthesisTactics.

Module PackageSynthesis (PKG : PrePackage).
  Module CP := MakeCurveParametersPackage PKG.
  Module BP := MakeBasePackage PKG.
  Module DP := MakeDefaultsPackage PKG.
  Module RP := MakeReificationTypesPackage PKG.
  Module FP := MakeFreezePackage PKG.
  Module LP := MakeLadderstepPackage PKG.
  Module KP := MakeKaratsubaPackage PKG.
  Module MP := MakeMontgomeryPackage PKG.
  Module MRP := MakeMontgomeryReificationTypesPackage PKG.
  Include CP.
  Include BP.
  Include DP.
  Include RP.
  Include FP.
  Include LP.
  Include KP.
  Include MP.
  Include MRP.

  Ltac synthesize_with_carry do_rewrite get_op_sig :=
    let carry_sig := get_carry_sig () in
    let op_sig := get_op_sig () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    start_preglue;
    [ do_rewrite op_sig carry_sig; cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen allowable_bit_widths default.
  Ltac synthesize_2arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_2sig_add_carry get_op_sig.
  Ltac synthesize_1arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_1sig_add_carry get_op_sig.

  Ltac synthesize_montgomery get_op_sig get_op_bounded :=
    let phi := get_phi_for_preglue () in
    let op_sig := get_op_sig () in
    let op_bounded := get_op_bounded () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    let do_red _ :=
        lazymatch (eval cbv [phi] in phi) with
        | (fun x => ?montgomery_to_F (?meval (?feBW_of_feBW_small _)))
          => cbv [feBW_of_feBW_small meval]
        end in
    start_preglue;
    do_red ();
    [ do_rewrite_with_sig_by op_sig op_sig_side_conditions_t;
      cbv_runtime
    | .. ];
    fin_preglue;
    factor_out_bounds_and_strip_eval op_bounded op_sig_side_conditions_t;
    refine_reflectively_gen allowable_bit_widths anf.

  Ltac synthesize_2arg_choice get_op_sig get_op_bounded :=
    let montgomery := get_montgomery () in
    lazymatch (eval vm_compute in montgomery) with
    | true => synthesize_montgomery get_op_sig get_op_bounded
    | false => synthesize_2arg_with_carry get_op_sig
    end.
  Ltac synthesize_1arg_choice get_op_sig get_op_bounded :=
    let montgomery := get_montgomery () in
    lazymatch (eval vm_compute in montgomery) with
    | true => synthesize_montgomery get_op_sig get_op_bounded
    | false => synthesize_1arg_with_carry get_op_sig
    end.

  Ltac synthesize_mul _ := synthesize_2arg_choice get_mul_sig get_mul_bounded.
  Ltac synthesize_add _ := synthesize_2arg_choice get_add_sig get_add_bounded.
  Ltac synthesize_sub _ := synthesize_2arg_choice get_sub_sig get_sub_bounded.
  Ltac synthesize_opp _ := synthesize_1arg_choice get_opp_sig get_opp_bounded.
  Ltac synthesize_square _ := synthesize_1arg_with_carry get_square_sig.
  Ltac synthesize_freeze _ :=
    let freeze_sig := get_freeze_sig () in
    let feBW_bounded := get_feBW_bounded () in
    let freeze_allowable_bit_widths := get_freeze_allowable_bit_widths () in
    start_preglue;
    [ do_rewrite_with_sig_by freeze_sig ltac:(fun _ => apply feBW_bounded); cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen freeze_allowable_bit_widths anf.
  Ltac synthesize_xzladderstep _ :=
    let Mxzladderstep_sig := get_Mxzladderstep_sig () in
    let a24_sig := get_a24_sig () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    start_preglue;
    [ unmap_map_tuple ();
      do_rewrite_with_sig_1arg Mxzladderstep_sig;
      cbv [Mxzladderstep XZ.M.xzladderstep a24_sig]; cbn [proj1_sig];
      do_set_sigs ();
      cbv_runtime
    | .. ];
    finish_conjoined_preglue ();
    refine_reflectively_gen allowable_bit_widths default.
  Ltac synthesize_nonzero _ :=
    let op_sig := get_nonzero_sig () in
    let allowable_bit_widths := get_allowable_bit_widths () in
    nonzero_preglue op_sig ltac:(fun _ => cbv_runtime);
    refine_reflectively_gen allowable_bit_widths anf.
End PackageSynthesis.
