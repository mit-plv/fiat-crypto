Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Export Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.Z.Interpretations.
Require Import Crypto.Reflection.Z.Reify.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Specific.GF25519Reflective.Common.
Require Import Crypto.Specific.GF25519Reflective.Reified.
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
Definition rfreeze : ExprUnOp := Eval vm_compute in rfreezeW.
Definition rge_modulus : ExprUnOpFEToZ := Eval vm_compute in rge_modulusW.
Definition rpack : ExprUnOpFEToWire := Eval vm_compute in rpackW.
Definition runpack : ExprUnOpWireToFE := Eval vm_compute in runpackW.

Declare Reduction asm_interp
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE
            radd rsub rmul ropp rfreeze rge_modulus rpack runpack
            curry_binop_fe25519W curry_unop_fe25519W curry_unop_wire_digitsW
            Word64.interp_op Word64.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            Interp interp interp_flat_type interpf interp_flat_type fst snd].
Ltac asm_interp
  := cbv beta iota delta
         [id
            interp_bexpr interp_uexpr interp_uexpr_FEToWire interp_uexpr_FEToZ interp_uexpr_WireToFE
            radd rsub rmul ropp rfreeze rge_modulus rpack runpack
            curry_binop_fe25519W curry_unop_fe25519W curry_unop_wire_digitsW
            Word64.interp_op Word64.interp_base_type
            Z.interp_op Z.interp_base_type
            Z.Syntax.interp_op Z.Syntax.interp_base_type
            Interp interp interp_flat_type interpf interp_flat_type fst snd].

Definition interp_radd : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_bexpr radd.
(*Print interp_radd.*)
Definition interp_radd_correct : interp_radd = interp_bexpr radd := eq_refl.
Definition interp_rsub : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_bexpr rsub.
(*Print interp_rsub.*)
Definition interp_rsub_correct : interp_rsub = interp_bexpr rsub := eq_refl.
Definition interp_rmul : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_bexpr rmul.
(*Print interp_rmul.*)
Definition interp_rmul_correct : interp_rmul = interp_bexpr rmul := eq_refl.
Definition interp_ropp : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_uexpr ropp.
(*Print interp_ropp.*)
Definition interp_ropp_correct : interp_ropp = interp_uexpr ropp := eq_refl.
Definition interp_rfreeze : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_uexpr rfreeze.
(*Print interp_rfreeze.*)
Definition interp_rfreeze_correct : interp_rfreeze = interp_uexpr rfreeze := eq_refl.

Definition interp_rge_modulus : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.word64
  := Eval asm_interp in interp_uexpr_FEToZ rge_modulus.
Definition interp_rge_modulus_correct : interp_rge_modulus = interp_uexpr_FEToZ rge_modulus := eq_refl.

Definition interp_rpack : Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.wire_digitsW
  := Eval asm_interp in interp_uexpr_FEToWire rpack.
Definition interp_rpack_correct : interp_rpack = interp_uexpr_FEToWire rpack := eq_refl.

Definition interp_runpack : Specific.GF25519BoundedCommon.wire_digitsW -> Specific.GF25519BoundedCommon.fe25519W
  := Eval asm_interp in interp_uexpr_WireToFE runpack.
Definition interp_runpack_correct : interp_runpack = interp_uexpr_WireToFE runpack := eq_refl.

Local Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) op) (only parsing).
Local Notation unop_correct_and_bounded rop op
  := (iunop_correct_and_bounded (interp_uexpr rop) op) (only parsing).
Local Notation unop_FEToZ_correct rop op
  := (iunop_FEToZ_correct (interp_uexpr_FEToZ rop) op) (only parsing).
Local Notation unop_FEToWire_correct_and_bounded rop op
  := (iunop_FEToWire_correct_and_bounded (interp_uexpr_FEToWire rop) op) (only parsing).
Local Notation unop_WireToFE_correct_and_bounded rop op
  := (iunop_WireToFE_correct_and_bounded (interp_uexpr_WireToFE rop) op) (only parsing).

Local Ltac start_correct_and_bounded_t op op_expr lem :=
  intros; hnf in *; destruct_head' prod; simpl in * |- ;
  repeat match goal with H : is_bounded _ = true |- _ => unfold_is_bounded_in H end;
  repeat match goal with H : wire_digits_is_bounded _ = true |- _ => unfold_is_bounded_in H end;
  change op with op_expr;
  rewrite <- lem.

Lemma radd_correct_and_bounded : binop_correct_and_bounded radd carry_add.
Proof.
  intros; hnf in *; destruct_head' prod; simpl in * |- .
  repeat match goal with H : is_bounded _ = true |- _ => unfold_is_bounded_in H end.
Admitted.
Lemma rsub_correct_and_bounded : binop_correct_and_bounded rsub carry_sub.
Proof.
Admitted.
Lemma rmul_correct_and_bounded : binop_correct_and_bounded rmul mul.
Proof.
Admitted.
Lemma ropp_correct_and_bounded : unop_correct_and_bounded ropp carry_opp.
Proof.
Admitted.
Lemma rfreeze_correct_and_bounded : unop_correct_and_bounded rfreeze freeze.
Proof.
Admitted.
Lemma rge_modulus_correct_and_bounded : unop_FEToZ_correct rge_modulus ge_modulus.
Proof.
Admitted.
Lemma rpack_correct_and_bounded : unop_FEToWire_correct_and_bounded rpack pack.
Proof.
Admitted.
Lemma runpack_correct_and_bounded : unop_WireToFE_correct_and_bounded runpack unpack.
Proof.
Admitted.
