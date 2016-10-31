Require Export Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Reflection.Reify.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.Interpretations.
Require Import Crypto.Reflection.Z.Reify.
Require Export Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.MapInterp.
Require Import Crypto.Reflection.MapInterpWf.
Require Import Crypto.Reflection.WfReflective.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Notation Expr := (Expr base_type Z.interp_base_type op).

Local Ltac make_type_from uncurried_op :=
  let T := (type of uncurried_op) in
  let T := (eval compute in T) in
  let rT := reify_type T in
  exact rT.

Definition ExprBinOpT : type base_type.
Proof. make_type_from (uncurry_binop_fe25519 carry_add). Defined.
Definition ExprUnOpT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 carry_opp). Defined.
Definition ExprUnOpFEToZT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 ge_modulus). Defined.
Definition ExprUnOpWireToFET : type base_type.
Proof. make_type_from (uncurry_unop_wire_digits unpack). Defined.
Definition ExprUnOpFEToWireT : type base_type.
Proof. make_type_from (uncurry_unop_fe25519 pack). Defined.
Definition ExprBinOp : Type := Expr ExprBinOpT.
Definition ExprUnOp : Type := Expr ExprUnOpT.
Definition ExprUnOpFEToZ : Type := Expr ExprUnOpFEToZT.
Definition ExprUnOpWireToFE : Type := Expr ExprUnOpWireToFET.
Definition ExprUnOpFEToWire : Type := Expr ExprUnOpFEToWireT.

Definition interp_bexpr : ExprBinOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_binop_fe25519W (Interp (@Z.interp_op) e).
Definition interp_uexpr : ExprUnOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_unop_fe25519W (Interp (@Z.interp_op) e).
Definition interp_uexpr_FEToZ : ExprUnOpFEToZ -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.word64
  := fun e => curry_unop_fe25519W (Interp (@Z.interp_op) e).
Definition interp_uexpr_FEToWire : ExprUnOpFEToWire -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.wire_digitsW
  := fun e => curry_unop_fe25519W (Interp (@Z.interp_op) e).
Definition interp_uexpr_WireToFE : ExprUnOpWireToFE -> Specific.GF25519BoundedCommon.wire_digitsW -> Specific.GF25519BoundedCommon.fe25519W
  := fun e => curry_unop_wire_digitsW (Interp (@Z.interp_op) e).

Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) op) (only parsing).
Notation unop_correct_and_bounded rop op
  := (iunop_correct_and_bounded (interp_uexpr rop) op) (only parsing).
Notation unop_FEToZ_correct rop op
  := (iunop_FEToZ_correct (interp_uexpr_FEToZ rop) op) (only parsing).
Notation unop_FEToWire_correct_and_bounded rop op
  := (iunop_FEToWire_correct_and_bounded (interp_uexpr_FEToWire rop) op) (only parsing).
Notation unop_WireToFE_correct_and_bounded rop op
  := (iunop_WireToFE_correct_and_bounded (interp_uexpr_WireToFE rop) op) (only parsing).

Ltac rexpr_cbv :=
  lazymatch goal with
  | [ |- { rexpr | interp_type_gen_rel_pointwise _ (Interp _ (t:=?T) rexpr) (?uncurry ?oper) } ]
    => let operf := head oper in
       let uncurryf := head uncurry in
       try cbv delta [T]; try cbv delta [oper];
       try cbv beta iota delta [uncurryf]
  end;
  cbv beta iota delta [interp_flat_type Z.interp_base_type interp_base_type zero_].

Ltac reify_sig :=
  rexpr_cbv; eexists; Reify_rhs; reflexivity.

Local Notation rexpr_sig T uncurried_op :=
  { rexprZ
  | interp_type_gen_rel_pointwise (fun _ => Logic.eq) (Interp interp_op (t:=T) rexprZ) uncurried_op }
    (only parsing).

Notation rexpr_binop_sig op := (rexpr_sig ExprBinOpT (uncurry_binop_fe25519 op)) (only parsing).
Notation rexpr_unop_sig op := (rexpr_sig ExprUnOpT (uncurry_unop_fe25519 op)) (only parsing).
Notation rexpr_unop_FEToZ_sig op := (rexpr_sig ExprUnOpFEToZT (uncurry_unop_fe25519 op)) (only parsing).
Notation rexpr_unop_FEToWire_sig op := (rexpr_sig ExprUnOpFEToWireT (uncurry_unop_fe25519 op)) (only parsing).
Notation rexpr_unop_WireToFE_sig op := (rexpr_sig ExprUnOpWireToFET (uncurry_unop_wire_digits op)) (only parsing).

Notation correct_and_bounded_genT ropW'v ropZ_sigv
  := (let ropW' := MapInterp Word64.of_Z ropW'v in
      let ropZ_sig := ropZ_sigv in
      let ropW := MapInterp (fun _ x => x) ropW' in
      let ropZ := MapInterp Word64.to_Z ropW' in
      let ropBounds := MapInterp ZBounds.of_word64 ropW' in
      let ropBoundedWord64 := MapInterp BoundedWord64.of_word64 ropW' in
      ropZ = proj1_sig ropZ_sig
      /\ interp_type_rel_pointwise2 Relations.related_Zi (Interp (@BoundedWord64.interp_op) ropBoundedWord64) (Interp (@Z.interp_op) ropZ)
      /\ interp_type_rel_pointwise2 Relations.related_boundsi (Interp (@BoundedWord64.interp_op) ropBoundedWord64) (Interp (@ZBounds.interp_op) ropBounds)
      /\ interp_type_rel_pointwise2 Relations.related_word64i (Interp (@BoundedWord64.interp_op) ropBoundedWord64) (Interp (@Word64.interp_op) ropW))
       (only parsing).

Ltac rexpr_correct :=
  let ropW' := fresh in
  let ropZ_sig := fresh in
  intros ropW' ropZ_sig;
  let wf_ropW := fresh "wf_ropW" in
  assert (wf_ropW : Wf ropW') by (subst ropW' ropZ_sig; reflect_Wf base_type_eq_semidec_is_dec op_beq_bl);
  cbv zeta; repeat apply conj;
  [ vm_compute; reflexivity
  | apply @InterpRelWf;
    [ | apply @RelWfMapInterp, wf_ropW ].. ];
  auto with interp_related.

Notation rword_of_Z rexprZ_sig := ((*MapInterp Word64.of_Z*) (proj1_sig rexprZ_sig)) (only parsing).
