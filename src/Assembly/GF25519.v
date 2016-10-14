Require Import Crypto.Assembly.Pipeline.

Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Util.Tuple.

Module GF25519.
  Definition bits: nat := 64.
  Definition width: Width bits := W64.

  Fixpoint makeBoundList {n} k (b: @WordRangeOpt n) :=
    match k with
    | O => nil
    | S k' => cons b (makeBoundList k' b)
    end.

  Section DefaultBounds.
    Import ListNotations.
    Local Notation rr exp := (makeRange 0 (2^exp + 2^exp/10)%Z).

    Definition feBound: list (@WordRangeOpt bits) :=
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
    Definition inputUpperBounds: list (@WordRangeOpt bits) := feBound ++ feBound.

    Definition ge25519_add_expr :=
        Eval cbv beta delta [fe25519 add mul sub Let_In] in add.

    Definition ge25519_add' (P Q: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE
        | HL.interp (E := ZEvaluable) (t := FE) r = ge25519_add_expr P Q }.
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
        transitivity (HL.interp (E := ZEvaluable) (t := ResultType) X);
        [reflexivity|].

        cbv iota beta delta [
            interp_type interp_binop HL.interp
            Z.land ZEvaluable eadd esub emul eshiftr eand].
        reflexivity.
    Defined.

    Definition ge25519_add (P Q: @interp_type Z ResultType) :=
        proj1_sig (ge25519_add' P Q).

    Definition hlProg'': NAry 20 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        liftFE (fun p => (liftFE (fun q => ge25519_add p q))).

    Definition hlProg': NAry 20 Z (@HL.expr Z (@LL.arg Z Z) ResultType).
        refine (liftN (HLConversions.mapVar _ _) hlProg''); intro t;
        [ refine LL.uninterp_arg | refine LL.interp_arg ].
    Defined.

    Definition hlProg: NAry 20 Z (@HL.expr Z (@LL.arg Z Z) ResultType) :=
      Eval vm_compute in hlProg'.
  End AddExpr.

  Module SubExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputUpperBounds: list (@WordRangeOpt bits) := feBound ++ feBound.

    Definition ge25519_sub_expr :=
        Eval cbv beta delta [fe25519 add mul sub Let_In] in sub.

    Definition ge25519_sub' (P Q: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE
        | HL.interp (E := ZEvaluable) (t := FE) r = ge25519_sub_expr P Q }.
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
        cbv beta delta [ge25519_sub_expr].

        let R := HL.rhs_of_goal in
        let X := HL.reify (@interp_type Z) R in
        transitivity (HL.interp (E := ZEvaluable) (t := ResultType) X);
        [reflexivity|].

        cbv iota beta delta [
            interp_type interp_binop HL.interp
            Z.land ZEvaluable eadd esub emul eshiftr eand].
        reflexivity.
    Defined.

    Definition ge25519_sub (P Q: @interp_type Z ResultType) :=
        proj1_sig (ge25519_sub' P Q).

    Definition hlProg'': NAry 20 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        liftFE (fun p => (liftFE (fun q => ge25519_sub p q))).

    Definition hlProg': NAry 20 Z (@HL.expr Z (@LL.arg Z Z) ResultType).
        refine (liftN (HLConversions.mapVar _ _) hlProg''); intro t;
        [ refine LL.uninterp_arg | refine LL.interp_arg ].
    Defined.

    Definition hlProg: NAry 20 Z (@HL.expr Z (@LL.arg Z Z) ResultType) :=
      Eval vm_compute in hlProg'.
  End SubExpr.

  Module MulExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputUpperBounds: list (@WordRangeOpt bits) := feBound ++ feBound.

    Definition ge25519_mul_expr :=
        Eval cbv beta delta [fe25519 add mul sub Let_In] in mul.

    Definition ge25519_mul' (P Q: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE
        | HL.interp (E := ZEvaluable) (t := FE) r = ge25519_mul_expr P Q }.
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
        cbv beta delta [ge25519_mul_expr].

        let R := HL.rhs_of_goal in
        let X := HL.reify (@interp_type Z) R in
        transitivity (HL.interp (E := ZEvaluable) (t := ResultType) X);
        [reflexivity|].

        cbv iota beta delta [
            interp_type interp_binop HL.interp
            Z.land ZEvaluable eadd esub emul eshiftr eand].
        reflexivity.
    Defined.

    Definition ge25519_mul (P Q: @interp_type Z ResultType) :=
        proj1_sig (ge25519_mul' P Q).

    Definition hlProg'': NAry 20 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        liftFE (fun p => (liftFE (fun q => ge25519_mul p q))).

    Definition hlProg': NAry 20 Z (@HL.expr Z (@LL.arg Z Z) ResultType).
        refine (liftN (HLConversions.mapVar _ _) hlProg''); intro t;
        [ refine LL.uninterp_arg | refine LL.interp_arg ].
    Defined.

    Definition hlProg: NAry 20 Z (@HL.expr Z (@LL.arg Z Z) ResultType) :=
      Eval vm_compute in hlProg'.
  End MulExpr.

  Module OppExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 10.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputUpperBounds: list (@WordRangeOpt bits) := feBound.

    Definition ge25519_opp_expr :=
        Eval cbv beta delta [fe25519 add mul sub opp Let_In] in opp.

    Definition ge25519_opp' (P: @interp_type Z FE) :
        { r: @HL.expr Z (@interp_type Z) FE
        | HL.interp (E := ZEvaluable) (t := FE) r = ge25519_opp_expr P }.
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
        transitivity (HL.interp (E := ZEvaluable) (t := ResultType) X);
        [reflexivity|].

        cbv iota beta delta [
            interp_type interp_binop HL.interp
            Z.land ZEvaluable eadd esub emul eshiftr eand].
        reflexivity.
    Defined.

    Definition ge25519_opp (P: @interp_type Z ResultType) :=
        proj1_sig (ge25519_opp' P).

    Definition hlProg'': NAry 10 Z (@HL.expr Z (@interp_type Z) ResultType) :=
        liftFE (fun p => ge25519_opp p).

    Definition hlProg': NAry 10 Z (@HL.expr Z (@LL.arg Z Z) ResultType).
        refine (liftN (HLConversions.mapVar _ _) hlProg''); intro t;
        [ refine LL.uninterp_arg | refine LL.interp_arg ].
    Defined.

    Definition hlProg: NAry 10 Z (@HL.expr Z (@LL.arg Z Z) ResultType) :=
      Eval vm_compute in hlProg'.
  End OppExpr.

  Module Add := Pipeline AddExpr.
  Module Sub := Pipeline SubExpr.
  Module Mul := Pipeline MulExpr.
  Module Opp := Pipeline OppExpr.
End GF25519.

Extraction "GF25519Add" GF25519.Add.
Extraction "GF25519Sub" GF25519.Sub.
Extraction "GF25519Mul" GF25519.Mul.
Extraction "GF25519Opp" GF25519.Opp.
