Require Import Coq.ZArith.ZArith.
Require Import Crypto.Assembly.GF25519.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Tuple.

(* Totally fine to edit these definitions; DO NOT change the type signatures at all *)
Definition ExprBinOp : Type
  := @PhoasCommon.interp_type word64 GF25519.FE -> @PhoasCommon.interp_type word64 GF25519.FE -> @HL.HL.expr word64 (@PhoasCommon.interp_type word64) GF25519.FE.
Definition ExprUnOp : Type
  := @PhoasCommon.interp_type word64 GF25519.FE -> @HL.HL.expr word64 (@PhoasCommon.interp_type word64) GF25519.FE.
Definition interp_bexpr : ExprBinOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun f x y => HL.HL.interp (E := Evaluables.WordEvaluable) (t := GF25519.FE) (f x y).
Definition interp_uexpr : ExprUnOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := fun f x => HL.HL.interp (E := Evaluables.WordEvaluable) (t := GF25519.FE) (f x).
Axiom radd : ExprBinOp. (* := GF25519.AddExpr.ge25519_add. *)
Axiom rsub : ExprBinOp. (* := GF25519.SubExpr.ge25519_sub. *)
Axiom rmul : ExprBinOp. (* := GF25519.MulExpr.ge25519_mul. *)
Axiom ropp : ExprUnOp. (* := GF25519.OppExpr.ge25519_opp. *)
Axiom rfreeze : ExprUnOp.

Local Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) op) (only parsing).
Local Notation unop_correct_and_bounded rop op
  := (iunop_correct_and_bounded (interp_uexpr rop) op) (only parsing).

Local Ltac start_correct_and_bounded_t op op_expr lem :=
  intros; hnf in *; destruct_head' prod; simpl in * |- ;
  repeat match goal with H : is_bounded _ = true |- _ => unfold_is_bounded_in H end;
  change op with op_expr;
  rewrite <- lem.

Lemma radd_correct_and_bounded : binop_correct_and_bounded radd carry_add.
Proof.
  start_correct_and_bounded_t
    carry_add GF25519.AddExpr.ge25519_add_expr
    (fun x y => proj2_sig (GF25519.AddExpr.ge25519_add' x y)).
  simpl @fe25519WToZ.
Admitted.
Lemma rsub_correct_and_bounded : binop_correct_and_bounded rsub carry_sub.
Proof.
  start_correct_and_bounded_t
    carry_sub GF25519.SubExpr.ge25519_sub_expr
    (fun x y => proj2_sig (GF25519.SubExpr.ge25519_sub' x y)).
  simpl @fe25519WToZ.
Admitted.
Lemma rmul_correct_and_bounded : binop_correct_and_bounded rmul mul.
Proof.
  start_correct_and_bounded_t
    Specific.GF25519.mul GF25519.MulExpr.ge25519_mul_expr
    (fun x y => proj2_sig (GF25519.MulExpr.ge25519_mul' x y)).
  simpl @fe25519WToZ.
Admitted.
Lemma ropp_correct_and_bounded : unop_correct_and_bounded ropp carry_opp.
Proof.
  start_correct_and_bounded_t
    carry_opp GF25519.OppExpr.ge25519_opp_expr
    (fun x => proj2_sig (GF25519.OppExpr.ge25519_opp' x)).
  simpl @fe25519WToZ.
Admitted.
Lemma rfreeze_correct_and_bounded : unop_correct_and_bounded rfreeze freeze.
Proof.
  intros; hnf in *; destruct_head' prod; simpl in * |- ;
  repeat match goal with H : is_bounded _ = true |- _ => unfold_is_bounded_in H end.
  simpl @fe25519WToZ.
Admitted.
