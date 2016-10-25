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

  Definition flatten {T}: (@interp_type Z FE -> T) -> NAry 10 Z T.
    intro F; refine (fun (a b c d e f g h i j: Z) =>
      F (a, b, c, d, e, f, g, h, i, j)).
  Defined.

  Definition unflatten {T}:
      (forall a b c d e f g h i j, T (a, b, c, d, e, f, g, h, i, j))
    -> (forall x: @interp_type Z FE, T x).
  Proof.
    intro F; refine (fun (x: @interp_type Z FE) =>
      let '(a, b, c, d, e, f, g, h, i, j) := x in
      F a b c d e f g h i j).
  Defined.

  Ltac intro_vars_for R := revert R;
    match goal with
    | [ |- forall x, @?T x ] => apply (@unflatten T); intros
    end.

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
      intro_vars_for P.
      intro_vars_for Q.

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
        Eval cbv in (flatten (fun p => (flatten (fun q => ge25519_add p q)))).
  End AddExpr.

  Module SubExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound ++ feBound.

    Definition ge25519_sub_expr :=
        Eval cbv beta delta [fe25519 carry_add mul carry_sub Let_In] in carry_sub.

    Definition ge25519_sub' (P Q: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE | HL.interp (t := FE) r = ge25519_sub_expr P Q }.
    Proof.
      intro_vars_for P.
      intro_vars_for Q.

      eexists.
      cbv beta delta [ge25519_sub_expr].

      let R := HL.rhs_of_goal in
      let X := HL.reify (@interp_type Z) R in
      transitivity (HL.interp (t := ResultType) X); [reflexivity|].

      cbv iota beta delta [
            interp_type interp_binop HL.interp
            Z.land ZEvaluable eadd esub emul eshiftr eand].
      reflexivity.
    Defined.

    Definition ge25519_sub (P Q: @interp_type Z ResultType) :=
        proj1_sig (ge25519_sub' P Q).

    Definition hlProg: NAry 20 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        Eval cbv in (flatten (fun p => (flatten (fun q => ge25519_sub p q)))).
  End SubExpr.

  Module MulExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound ++ feBound.

    Definition ge25519_mul_expr :=
        Eval cbv beta delta [fe25519 carry_add mul carry_sub Let_In] in mul.

    Definition ge25519_mul' (P Q: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE | HL.interp (t := FE) r = ge25519_mul_expr P Q }.
    Proof.
      intro_vars_for P.
      intro_vars_for Q.

      eexists.
      cbv beta delta [ge25519_mul_expr].

      let R := HL.rhs_of_goal in
      let X := HL.reify (@interp_type Z) R in
      transitivity (HL.interp (t := ResultType) X); [reflexivity|].

      cbv iota beta delta [
            interp_type interp_binop HL.interp
            Z.land ZEvaluable eadd esub emul eshiftr eand].
      reflexivity.
    Defined.

    Definition ge25519_mul (P Q: @interp_type Z ResultType) :=
        proj1_sig (ge25519_mul' P Q).

    Definition hlProg: NAry 20 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        Eval cbv in (flatten (fun p => (flatten (fun q => ge25519_mul p q)))).
  End MulExpr.

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
      intro_vars_for P.

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
        Eval cbv in (flatten (fun p => ge25519_opp p)).
  End OppExpr.

  Module Add := Pipeline AddExpr.
  Module Sub := Pipeline SubExpr.
  Module Mul := Pipeline MulExpr.
  Module Opp := Pipeline OppExpr.
End GF25519.

Set Printing All.
Opaque eadd esub emul eshiftr eand toT fromT.
Eval cbv iota beta delta in GF25519.Add.HL.progZ.
Eval cbv iota beta delta in GF25519.Add.AST.progZ.

Extraction "GF25519Add" GF25519.Add.
Extraction "GF25519Sub" GF25519.Sub.
Extraction "GF25519Mul" GF25519.Mul.
Extraction "GF25519Opp" GF25519.Opp.
