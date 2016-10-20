Require Import Coq.ZArith.ZArith.
Require Import Crypto.Assembly.GF25519.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Util.Tuple.

Axiom is_bounded : forall (x : Specific.GF25519.fe25519), bool. (* Pull from Specific.GF25519Bounded when the latest changes to master are merged into this branch *)


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
Axiom rinv : ExprUnOp.
(*Axiom radd_correct : forall x y, interp_bexpr radd x y = carry_add x y.
Axiom rsub_correct : forall x y, interp_bexpr rsub x y = carry_sub x y.*)
Lemma rmul_correct : forall x y, interp_bexpr rmul x y = mul x y.
Proof.
  cbv [interp_bexpr rmul GF25519.MulExpr.ge25519_mul]; intros.
  apply proj2_sig.
Qed.
(*Axiom ropp_correct : forall x, interp_uexpr ropp x = carry_opp x.
Axiom rinv_correct : forall x, interp_uexpr rinv x = inv x.*)
Axiom check_bbounds : ExprBinOp -> bool.
Axiom check_ubounds : ExprUnOp -> bool.
Axiom radd_bounded : check_bbounds radd = true.
Axiom rsub_bounded : check_bbounds rsub = true.
Axiom rmul_bounded : check_bbounds rmul = true.
Axiom ropp_bounded : check_ubounds ropp = true.
Axiom rinv_bounded : check_ubounds rinv = true.
Axiom bbounds_correct
  : forall rexpr, check_bbounds rexpr = true
                  -> forall x y, is_bounded x = true
                                 -> is_bounded y = true
                                 -> is_bounded (interp_bexpr rexpr x y) = true.
Axiom ubounds_correct
  : forall rexpr, check_ubounds rexpr = true
                  -> forall x, is_bounded x = true
                               -> is_bounded (interp_uexpr rexpr x) = true.
