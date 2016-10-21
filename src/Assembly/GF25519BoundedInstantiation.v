Require Import Coq.ZArith.ZArith.
Require Import Crypto.Assembly.PhoasCommon.
Require Import Crypto.Assembly.QhasmCommon.
Require Import Crypto.Assembly.Compile.
Require Import Crypto.Assembly.LL.
Require Import Crypto.Assembly.GF25519.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519BoundedCommon.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Tuple.

(* Totally fine to edit these definitions; DO NOT change the type signatures at all *)
Section Operations.
  Import Assembly.GF25519.GF25519.
  Definition wfe: Type := @interp_type (word bits) FE.

  Definition ExprBinOp : Type := NAry 20 Z (@CompileLL.WExpr bits FE).
  Definition ExprUnOp : Type := NAry 10 Z (@CompileLL.WExpr bits FE).

  Local Existing Instance WordEvaluable.

  Definition interp_bexpr' (op: ExprBinOp) (x y: tuple (word bits) 10): tuple (word bits) 10 :=
    let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
    let '(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9) := y in
    let op' := NArgMap (fun v => Z.of_N (@wordToN bits v)) op in
    let z := LL.interp' (fun x => NToWord bits (Z.to_N x)) (op' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) in
    z.

  Definition interp_uexpr' (op: ExprUnOp) (x: tuple (word bits) 10): tuple (word bits) 10 :=
    let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in
    let op' := NArgMap (fun v => Z.of_N (@wordToN bits v)) op in
    let z := LL.interp' (fun x => NToWord bits (Z.to_N x)) (op' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) in
    z.

  Definition radd : ExprBinOp := GF25519.Add.wordProg.
  Definition ropp : ExprUnOp := GF25519.Opp.wordProg.
End Operations.


Definition interp_bexpr : ExprBinOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := interp_bexpr'.
Definition interp_uexpr : ExprUnOp -> Specific.GF25519BoundedCommon.fe25519W -> Specific.GF25519BoundedCommon.fe25519W
  := interp_uexpr'.
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
