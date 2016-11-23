Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Export Crypto.SpecificGen.GF5211_32.
Require Import Crypto.SpecificGen.GF5211_32BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Reflection.Z.Interpretations64.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.SpecificGen.GF5211_32Reflective.Common.
Require Import Crypto.SpecificGen.GF5211_32Reflective.Reified.AddCoordinates.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

Time Definition radd_coordinates : Expr9_4Op := Eval vm_compute in radd_coordinatesW.

Declare Reduction asm_interp_add_coordinates
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE interp_9_4expr
            radd_coordinates
            curry_binop_fe5211_32W curry_unop_fe5211_32W curry_unop_wire_digitsW curry_9op_fe5211_32W
            WordW.interp_op WordW.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            mapf_interp_flat_type map_interp WordW.interp_base_type MapInterp mapf_interp word64ize rword64ize
            Interp interp interp_flat_type interpf interpf_step interp_flat_type fst snd].
Ltac asm_interp_add_coordinates
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE interp_9_4expr
            radd_coordinates
            curry_binop_fe5211_32W curry_unop_fe5211_32W curry_unop_wire_digitsW curry_9op_fe5211_32W
            WordW.interp_op WordW.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            mapf_interp_flat_type map_interp WordW.interp_base_type MapInterp mapf_interp word64ize rword64ize
            Interp interp interp_flat_type interpf interp_flat_type fst snd].


Time Definition interp_radd_coordinates : SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> SpecificGen.GF5211_32BoundedCommon.fe5211_32W
                                          -> Tuple.tuple SpecificGen.GF5211_32BoundedCommon.fe5211_32W 4
  := Eval asm_interp_add_coordinates in interp_9_4expr (rword64ize radd_coordinates).
(*Print interp_radd_coordinates.*)
Time Definition interp_radd_coordinates_correct : interp_radd_coordinates = interp_9_4expr radd_coordinates := eq_refl.

Lemma radd_coordinates_correct_and_bounded : op9_4_correct_and_bounded radd_coordinates add_coordinates.
Proof. exact_no_check radd_coordinatesW_correct_and_bounded. Time Qed.
