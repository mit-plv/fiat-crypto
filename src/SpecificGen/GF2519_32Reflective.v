Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Export Crypto.SpecificGen.GF2519_32.
Require Import Crypto.SpecificGen.GF2519_32BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Reflection.Z.Interpretations64.RelationsCombinations.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.SpecificGen.GF2519_32Reflective.Common.
Require Import Crypto.SpecificGen.GF2519_32Reflective.Reified.
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

Definition radd : ExprBinOp := Eval vm_compute in rcarry_addW.
Definition rsub : ExprBinOp := Eval vm_compute in rcarry_subW.
Definition rmul : ExprBinOp := Eval vm_compute in rmulW.
Definition ropp : ExprUnOp := Eval vm_compute in rcarry_oppW.
Definition rprefreeze : ExprUnOp := Eval vm_compute in rprefreezeW.
Definition rge_modulus : ExprUnOpFEToZ := Eval vm_compute in rge_modulusW.
Definition rpack : ExprUnOpFEToWire := Eval vm_compute in rpackW.
Definition runpack : ExprUnOpWireToFE := Eval vm_compute in runpackW.

Declare Reduction asm_interp
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE interp_9_4expr
            radd rsub rmul ropp rprefreeze rge_modulus rpack runpack
            curry_binop_fe2519_32W curry_unop_fe2519_32W curry_unop_wire_digitsW curry_9op_fe2519_32W
            WordW.interp_op WordW.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            mapf_interp_flat_type map_interp WordW.interp_base_type MapInterp mapf_interp word64ize rword64ize
            Interp interp interp_flat_type interpf interpf_step interp_flat_type fst snd].
Ltac asm_interp
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE interp_9_4expr
            radd rsub rmul ropp rprefreeze rge_modulus rpack runpack
            curry_binop_fe2519_32W curry_unop_fe2519_32W curry_unop_wire_digitsW curry_9op_fe2519_32W
            WordW.interp_op WordW.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            mapf_interp_flat_type map_interp WordW.interp_base_type MapInterp mapf_interp word64ize rword64ize
            Interp interp interp_flat_type interpf interp_flat_type fst snd].


Definition interp_radd : SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W
  := Eval asm_interp in interp_bexpr (rword64ize radd).
(*Print interp_radd.*)
Definition interp_radd_correct : interp_radd = interp_bexpr radd := eq_refl.
Definition interp_rsub : SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W
  := Eval asm_interp in interp_bexpr (rword64ize rsub).
(*Print interp_rsub.*)
Definition interp_rsub_correct : interp_rsub = interp_bexpr rsub := eq_refl.
Definition interp_rmul : SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W
  := Eval asm_interp in interp_bexpr (rword64ize rmul).
(*Print interp_rmul.*)
Definition interp_rmul_correct : interp_rmul = interp_bexpr rmul := eq_refl.
Definition interp_ropp : SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W
  := Eval asm_interp in interp_uexpr (rword64ize ropp).
(*Print interp_ropp.*)
Definition interp_ropp_correct : interp_ropp = interp_uexpr ropp := eq_refl.
Definition interp_rprefreeze : SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W
  := Eval asm_interp in interp_uexpr (rword64ize rprefreeze).
(*Print interp_rprefreeze.*)
Definition interp_rprefreeze_correct : interp_rprefreeze = interp_uexpr rprefreeze := eq_refl.

Definition interp_rge_modulus : SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.word64
  := Eval asm_interp in interp_uexpr_FEToZ (rword64ize rge_modulus).
Definition interp_rge_modulus_correct : interp_rge_modulus = interp_uexpr_FEToZ rge_modulus := eq_refl.

Definition interp_rpack : SpecificGen.GF2519_32BoundedCommon.fe2519_32W -> SpecificGen.GF2519_32BoundedCommon.wire_digitsW
  := Eval asm_interp in interp_uexpr_FEToWire (rword64ize rpack).
Definition interp_rpack_correct : interp_rpack = interp_uexpr_FEToWire rpack := eq_refl.

Definition interp_runpack : SpecificGen.GF2519_32BoundedCommon.wire_digitsW -> SpecificGen.GF2519_32BoundedCommon.fe2519_32W
  := Eval asm_interp in interp_uexpr_WireToFE (rword64ize runpack).
Definition interp_runpack_correct : interp_runpack = interp_uexpr_WireToFE runpack := eq_refl.

Lemma radd_correct_and_bounded : binop_correct_and_bounded radd carry_add.
Proof. exact rcarry_addW_correct_and_bounded. Qed.
Lemma rsub_correct_and_bounded : binop_correct_and_bounded rsub carry_sub.
Proof. exact rcarry_subW_correct_and_bounded. Qed.
Lemma rmul_correct_and_bounded : binop_correct_and_bounded rmul mul.
Proof. exact rmulW_correct_and_bounded. Qed.
Lemma ropp_correct_and_bounded : unop_correct_and_bounded ropp carry_opp.
Proof. exact rcarry_oppW_correct_and_bounded. Qed.
Lemma rprefreeze_correct_and_bounded : unop_correct_and_bounded rprefreeze prefreeze.
Proof. exact rprefreezeW_correct_and_bounded. Qed.
Lemma rge_modulus_correct_and_bounded : unop_FEToZ_correct rge_modulus ge_modulus.
Proof. exact rge_modulusW_correct_and_bounded. Qed.
Lemma rpack_correct_and_bounded : unop_FEToWire_correct_and_bounded rpack pack.
Proof. exact rpackW_correct_and_bounded. Qed.
Lemma runpack_correct_and_bounded : unop_WireToFE_correct_and_bounded runpack unpack.
Proof. exact runpackW_correct_and_bounded. Qed.
