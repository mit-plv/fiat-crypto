Require Import Crypto.Specific.ArithmeticSynthesisFramework.
Require Import Crypto.Specific.ReificationTypes.
Require Import Crypto.Specific.LadderstepSynthesisFramework.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Util.BoundedWord.
Require Import Crypto.Specific.IntegrationTestTemporaryMiscCommon.
Require Import Crypto.Compilers.Z.Bounds.Pipeline.
Require Crypto.Specific.CurveParameters.

Module Export Exports.
  Export ArithmeticSynthesisFramework.Exports.
End Exports.

Module MakeSynthesisTactics (Curve : CurveParameters.CurveParameters).
  Module AS := MakeArithmeticSynthesisTestTactics Curve.

  Ltac get_synthesis_package _ :=
    let arithmetic_synthesis_pkg := AS.get_ArithmeticSynthesis_package () in
    lazymatch arithmetic_synthesis_pkg with
    | (?sz, ?bitwidth, ?s, ?c, ?carry_chain1, ?carry_chain2, ?a24, ?coef_div_modulus, ?m, ?wt, ?sz2, ?m_enc, ?coef, ?coef_mod, ?sz_nonzero, ?wt_nonzero, ?wt_nonneg, ?wt_divides, ?wt_divides', ?wt_divides_chain1, ?wt_divides_chain2, ?zero_sig, ?one_sig, ?a24_sig, ?add_sig, ?sub_sig, ?opp_sig, ?mul_sig, ?square_sig, ?carry_sig, ?wt_pos, ?wt_multiples, ?freeze_sig, ?ring)
      => let reification_types_pkg := get_ReificationTypes_package wt sz m wt_nonneg AS.P.upper_bound_of_exponent in
         let ladderstep_pkg := get_Ladderstep_package sz wt m add_sig sub_sig mul_sig square_sig carry_sig in
         constr:((arithmetic_synthesis_pkg, reification_types_pkg, ladderstep_pkg))
    end.
  Ltac make_synthesis_package _ :=
    lazymatch goal with
    | [ |- { T : _ & _ } ]
      => first [ eexists (_, _, _)
               | eexists (_, _)
               | eexists ]
    | [ |- _ ] => idtac
    end;
    let pkg := get_synthesis_package () in
    exact pkg.
End MakeSynthesisTactics.

Local Notation eta2 x := (fst x, snd x) (only parsing).
Local Notation eta3 x := (eta2 (fst x), snd x) (only parsing).

Notation Synthesis_package'_Type :=
  { ABC : _ & let '(a, b, c) := eta3 ABC in (a * b * c)%type } (only parsing).

Module Type SynthesisPrePackage.
  Parameter Synthesis_package' : Synthesis_package'_Type.
  Parameter Synthesis_package : let '(a, b, c) := eta3 (projT1 Synthesis_package') in (a * b * c)%type.
End SynthesisPrePackage.

Module PackageSynthesis (Curve : CurveParameters.CurveParameters) (P : SynthesisPrePackage).
  Module CP := CurveParameters.FillCurveParameters Curve.

  Module PP <: ReificationTypesPrePackage <: ArithmeticSynthesisPrePackage <: LadderstepPrePackage.
    Definition ArithmeticSynthesis_package := Eval compute in let '(a, b, c) := P.Synthesis_package in a.
    Definition ArithmeticSynthesis_package' : { T : _ & T } := existT _ _ ArithmeticSynthesis_package.
    Definition ReificationTypes_package := Eval compute in let '(a, b, c) := P.Synthesis_package in b.
    Definition ReificationTypes_package' : { T : _ & T } := existT _ _ ReificationTypes_package.
    Definition Ladderstep_package := Eval compute in let '(a, b, c) := P.Synthesis_package in c.
    Definition Ladderstep_package' : { T : _ & T } := existT _ _ Ladderstep_package.
  End PP.
  Module RT := MakeReificationTypes PP.
  Module AS := MakeArithmeticSynthesisTest PP.
  Module LS := MakeLadderstep PP.
  Include RT.
  Include AS.
  Include LS.

  Ltac synthesize_with_carry do_rewrite get_op_sig :=
    let carry_sig := get_carry_sig () in
    let op_sig := get_op_sig () in
    start_preglue;
    [ do_rewrite op_sig carry_sig; cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen CP.allowable_bit_widths default.
  Ltac synthesize_2arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_2sig_add_carry get_op_sig.
  Ltac synthesize_1arg_with_carry get_op_sig :=
    synthesize_with_carry do_rewrite_with_1sig_add_carry get_op_sig.

  Ltac synthesize_mul _ := synthesize_2arg_with_carry get_mul_sig.
  Ltac synthesize_add _ := synthesize_2arg_with_carry get_add_sig.
  Ltac synthesize_sub _ := synthesize_2arg_with_carry get_sub_sig.
  Ltac synthesize_square _ := synthesize_1arg_with_carry get_square_sig.
  Ltac synthesize_freeze _ :=
    let freeze_sig := get_freeze_sig () in
    let feBW_bounded := get_feBW_bounded () in
    start_preglue;
    [ do_rewrite_with_sig_by freeze_sig ltac:(fun _ => apply feBW_bounded); cbv_runtime
    | .. ];
    fin_preglue;
    refine_reflectively_gen CP.freeze_allowable_bit_widths anf.
  Ltac synthesize_xzladderstep _ :=
    let Mxzladderstep_sig := get_Mxzladderstep_sig () in
    let a24_sig := get_a24_sig () in
    start_preglue;
    [ unmap_map_tuple ();
      do_rewrite_with_sig_1arg Mxzladderstep_sig;
      cbv [Mxzladderstep XZ.M.xzladderstep a24_sig]; cbn [proj1_sig];
      do_set_sigs ();
      cbv_runtime
    | .. ];
    finish_conjoined_preglue ();
    refine_reflectively_gen CP.allowable_bit_widths default.
End PackageSynthesis.
