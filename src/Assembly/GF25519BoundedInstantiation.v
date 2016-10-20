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

(*Local Notation ibinop_correct_and_bounded irop op
  := (forall x y,
         is_bounded (fe25519WToZ x) = true
         -> is_bounded (fe25519WToZ y) = true
         -> fe25519WToZ (irop x y) = op (fe25519WToZ x) (fe25519WToZ y)
            /\ is_bounded (fe25519WToZ (irop x y)) = true) (only parsing).
Local Notation binop_correct_and_bounded rop op
  := (ibinop_correct_and_bounded (interp_bexpr rop) op) (only parsing).
Local Notation iunop_correct_and_bounded irop op
  := (forall x,
         is_bounded (fe25519WToZ x) = true
         -> fe25519WToZ (irop x) = op (fe25519WToZ x)
            /\ is_bounded (fe25519WToZ (irop x)) = true) (only parsing).
Local Notation unop_correct_and_bounded rop op
  := (iunop_correct_and_bounded (interp_uexpr rop) op) (only parsing).
Axiom radd_correct_and_bounded : binop_correct_and_bounded radd carry_add.
Axiom rsub_correct_and_bounded : binop_correct_and_bounded rsub carry_sub.
Axiom rmul_correct_and_bounded : binop_correct_and_bounded rmul mul.
Axiom ropp_correct_and_bounded : unop_correct_and_bounded ropp carry_opp.
Axiom rfreeze_correct_and_bounded : unop_correct_and_bounded rfreeze freeze.*)
