Require Import Crypto.Assembly.Pipeline.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Util.Tuple.

Module GF25519.
  Definition bits: nat := 64.
  Definition width: Width bits := W64.

  Instance ZE : Evaluable Z := @ZEvaluable bits.
  Existing Instance ZE.

  Fixpoint makeBoundList {n} k (b: @BoundedWord n) :=
    match k with
    | O => nil
    | S k' => cons b (makeBoundList k' b)
    end.

  Section DefaultBounds.
    Import ListNotations.
    Local Notation rr exp := (2^exp + 2^exp/10)%Z.

    Definition feBound: list Z :=
      [rr 26; rr 27; rr 26; rr 27; rr 26;
       rr 27; rr 26; rr 27; rr 26; rr 27].
  End DefaultBounds.

  Definition FE: type.
  Proof.
    let T := eval vm_compute in fe25519 in
    let t := HL.reify_type T in
    exact t.
  Defined.

  Definition liftFE {T} (F: @interp_type Z FE -> T) :=
    fun (a b c d e f g h i j: Z) => F (a, b, c, d, e, f, g, h, i, j).

  Module AddExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound ++ feBound.

    Definition ge25519_add_expr :=
        Eval cbv beta delta [fe25519 carry_add mul carry_sub Let_In] in carry_add.

    Definition ge25519_add' (P Q: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE | HL.interp (t := FE) r = ge25519_add_expr P Q }.
    Proof.
      vm_compute in P, Q; repeat
        match goal with
        | [x:?T |- _] =>
          lazymatch T with
          | Z => fail
          | prod _ _ => destruct x
          | _ => clear x
          end
        end.

      eexists.
      cbv beta delta [ge25519_add_expr].

      let R := HL.rhs_of_goal in
      let X := HL.reify (@interp_type Z) R in
      transitivity (HL.interp (t := ResultType) X); [reflexivity|].

      cbv iota beta delta [
            interp_type interp_binop HL.interp
            Z.land ZEvaluable eadd esub emul eshiftr eand].
      reflexivity.
    Defined.

    Definition ge25519_add (P Q: @interp_type Z ResultType) :=
        proj1_sig (ge25519_add' P Q).

    Definition hlProg: NAry 20 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        liftFE (fun p => (liftFE (fun q => ge25519_add p q))).
  End AddExpr.

  Module OppExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 10.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound.

    Definition ge25519_opp_expr :=
        Eval cbv beta delta [fe25519 carry_add mul carry_sub carry_opp Let_In] in carry_opp.

    Definition ge25519_opp' (P: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE
        | HL.interp (E := @ZEvaluable bits) (t := FE) r = ge25519_opp_expr P }.
    Proof.
      vm_compute in P; repeat
        match goal with
        | [x:?T |- _] =>
          lazymatch T with
          | Z => fail
          | prod _ _ => destruct x
          | _ => clear x
          end
        end.

      eexists.
      cbv beta delta [ge25519_opp_expr zero_].

      let R := HL.rhs_of_goal in
      let X := HL.reify (@interp_type Z) R in
      transitivity (HL.interp (E := @ZEvaluable bits) (t := ResultType) X);
        [reflexivity|].

      cbv iota beta delta [
        interp_type interp_binop HL.interp
        Z.land ZEvaluable eadd esub emul eshiftr eand].
      reflexivity.
    Defined.

    Definition ge25519_opp (P: @interp_type Z ResultType) :=
        proj1_sig (ge25519_opp' P).

    Definition hlProg: NAry 10 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        liftFE (fun p => ge25519_opp p).
  End OppExpr.

  Module Add := Pipeline AddExpr.
  Module Opp := Pipeline OppExpr.

  Section Operations.
    Definition wfe: Type := @interp_type (word bits) FE.

    Definition ExprBinOp : Type := NAry 20 Z (@CompileLL.WExpr bits FE).
    Definition ExprUnOp : Type := NAry 10 Z (@CompileLL.WExpr bits FE).

    Existing Instance WordEvaluable.

    Definition interp_bexpr (op: ExprBinOp) (x y: tuple (word bits) 10): tuple (word bits) 10 :=
      let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in 
      let '(y0, y1, y2, y3, y4, y5, y6, y7, y8, y9) := y in
      let op' := NArgMap (fun v => Z.of_N (@wordToN bits v)) op in
      let z := LL.interp' (fun x => NToWord bits (Z.to_N x)) (op' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9) in
        z.

    Definition interp_uexpr (op: ExprUnOp) (x: tuple (word bits) 10): tuple (word bits) 10 :=
      let '(x0, x1, x2, x3, x4, x5, x6, x7, x8, x9) := x in 
      let op' := NArgMap (fun v => Z.of_N (@wordToN bits v)) op in
      let z := LL.interp' (fun x => NToWord bits (Z.to_N x)) (op' x0 x1 x2 x3 x4 x5 x6 x7 x8 x9) in
        z.
 
    Definition radd : ExprBinOp := Add.wordProg.
    Definition ropp : ExprUnOp := Opp.wordProg.
  End Operations.
End GF25519.

Extraction "GF25519Add" GF25519.Add.
Extraction "GF25519Opp" GF25519.Opp.
