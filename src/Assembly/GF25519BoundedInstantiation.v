Require Import Coq.ZArith.ZArith.
Require Import Crypto.Assembly.GF25519.
Require Import Crypto.Specific.GF25519Bounded.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Util.Tuple.

(* Totally fine to edit these definitions; DO NOT change the type signatures at all *)
Definition ExprBinOp : Type
  := @PhoasCommon.interp_type Z GF25519.FE -> @PhoasCommon.interp_type Z GF25519.FE -> @HL.HL.expr Z (@PhoasCommon.interp_type Z) GF25519.FE.
Definition ExprUnOp : Type
  := @PhoasCommon.interp_type Z GF25519.FE -> @HL.HL.expr Z (@PhoasCommon.interp_type Z) GF25519.FE.
Definition interp_bexpr : ExprBinOp -> Specific.GF25519.fe25519 -> Specific.GF25519.fe25519 -> Specific.GF25519.fe25519
  := fun f x y => HL.HL.interp (E := Evaluables.ZEvaluable) (t := GF25519.FE) (f x y).
Definition interp_uexpr : ExprUnOp -> Specific.GF25519.fe25519 -> Specific.GF25519.fe25519
  := fun f x => HL.HL.interp (E := Evaluables.ZEvaluable) (t := GF25519.FE) (f x).
Definition radd : ExprBinOp := GF25519.AddExpr.ge25519_add.
Definition rsub : ExprBinOp := GF25519.SubExpr.ge25519_sub.
Definition rmul : ExprBinOp := GF25519.MulExpr.ge25519_mul.
Definition ropp : ExprUnOp := GF25519.OppExpr.ge25519_opp.
Axiom rfreeze : ExprUnOp.
Lemma radd_correct : forall x y, interp_bexpr radd x y = carry_add x y.
Proof.
  cbv [interp_bexpr radd GF25519.AddExpr.ge25519_add]; intros.
  apply proj2_sig.
Qed.
Lemma rsub_correct : forall x y, interp_bexpr rsub x y = carry_sub x y.
Proof.
  cbv [interp_bexpr rsub GF25519.SubExpr.ge25519_sub]; intros.
  apply proj2_sig.
Qed.
Lemma rmul_correct : forall x y, interp_bexpr rmul x y = mul x y.
Proof.
  cbv [interp_bexpr rmul GF25519.MulExpr.ge25519_mul]; intros.
  apply proj2_sig.
Qed.
Axiom rfreeze_correct : forall x, interp_uexpr rfreeze x = freeze x.
Local Notation binop_bounded op
  := (forall x y,
         is_bounded x = true
         -> is_bounded y = true
         -> is_bounded (interp_bexpr op x y) = true) (only parsing).
Local Notation unop_bounded op
  := (forall x,
         is_bounded x = true
         -> is_bounded (interp_uexpr op x) = true) (only parsing).
Axiom radd_bounded : binop_bounded radd.
Axiom rsub_bounded : binop_bounded rsub.
Axiom rmul_bounded : binop_bounded rmul.
Axiom ropp_bounded : unop_bounded ropp.
Axiom rfreeze_bounded : unop_bounded rfreeze.
