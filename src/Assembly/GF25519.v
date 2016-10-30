Require Import Coq.ZArith.Znat.
Require Import Coq.ZArith.ZArith.

Require Import Crypto.Assembly.Pipeline.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Util.Tuple.

Module GF25519.
  Definition bits: nat := 64.
  Definition width: Width bits := W64.

  Existing Instance ZEvaluable.

  Fixpoint makeBoundList {n} k (b: @BoundedWord n) :=
    match k with
    | O => nil
    | S k' => cons b (makeBoundList k' b)
    end.

  Section DefaultBounds.
    Import ListNotations.

    Local Notation rr exp := (2^exp + 2^(exp-3))%Z.

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

  Section Expressions.
    Definition flatten {T}: (@interp_type Z FE -> T) -> NAry 10 Z T.
      intro F; refine (fun (a b c d e f g h i j: Z) =>
        F (a, b, c, d, e, f, g, h, i, j)).
    Defined.

    Definition unflatten {T}:
      (forall a b c d e f g h i j : Z, T (a, b, c, d, e, f, g, h, i, j))
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

    Definition ge25519_add_expr :=
      Eval cbv beta delta [fe25519 carry_add mul carry_sub opp Let_In] in carry_add.

    Definition ge25519_sub_expr :=
      Eval cbv beta delta [fe25519 carry_add mul carry_sub opp Let_In] in carry_sub.

    Definition ge25519_mul_expr :=
      Eval cbv beta delta [fe25519 carry_add mul carry_sub opp Let_In] in mul.

    Definition ge25519_opp_expr :=
      Eval cbv beta delta [fe25519 carry_add mul carry_sub opp Let_In] in opp.

    Definition ge25519_add' (P Q: @interp_type Z FE):
      { r: @HL.Expr Z FE | HL.Interp r = ge25519_add_expr P Q }.
    Proof.
      intro_vars_for P.
      intro_vars_for Q.

      eexists.

      cbv beta delta [ge25519_add_expr].

      etransitivity; [reflexivity|].

      let R := HL.rhs_of_goal in
      let X := HL.Reify R in
      transitivity (HL.Interp (X bits)); [reflexivity|].

      cbv iota beta delta [ HL.Interp
          interp_type interp_binop HL.interp
          Z.land ZEvaluable eadd esub emul eshiftr eand].

      reflexivity.
    Defined.

    Definition ge25519_sub' (P Q: @interp_type Z FE):
      { r: @HL.Expr Z FE | HL.Interp r = ge25519_sub_expr P Q }.
    Proof.
      intro_vars_for P.
      intro_vars_for Q.

      eexists.

      cbv beta delta [ge25519_sub_expr].

      etransitivity; [reflexivity|].

      let R := HL.rhs_of_goal in
      let X := HL.Reify R in
      transitivity (HL.Interp (X bits)); [reflexivity|].

      cbv iota beta delta [ HL.Interp
          interp_type interp_binop HL.interp
          Z.land ZEvaluable eadd esub emul eshiftr eand].

      reflexivity.
    Defined.

    Definition ge25519_mul' (P Q: @interp_type Z FE):
      { r: @HL.Expr Z FE | HL.Interp r = ge25519_mul_expr P Q }.
    Proof.
      intro_vars_for P.
      intro_vars_for Q.

      eexists.

      cbv beta delta [ge25519_mul_expr].

      etransitivity; [reflexivity|].

      let R := HL.rhs_of_goal in
      let X := HL.Reify R in
      transitivity (HL.Interp (X bits)); [reflexivity|].

      cbv iota beta delta [ HL.Interp
          interp_type interp_binop HL.interp
          Z.land ZEvaluable eadd esub emul eshiftr eand].

      reflexivity.
    Defined.

    Definition ge25519_opp' (P: @interp_type Z FE):
      { r: @HL.Expr Z FE | HL.Interp r = ge25519_opp_expr P }.
    Proof.
      intro_vars_for P.

      eexists.

      cbv beta delta [ge25519_opp_expr zero_].

      etransitivity; [reflexivity|].

      let R := HL.rhs_of_goal in
      let X := HL.Reify R in
      transitivity (HL.Interp (X bits)); [reflexivity|].

      cbv iota beta delta [ HL.Interp
          interp_type interp_binop HL.interp
          Z.land ZEvaluable eadd esub emul eshiftr eand].

      reflexivity.
    Defined.

    Definition ge25519_add (P Q: @interp_type Z FE) :=
        proj1_sig (ge25519_add' P Q).

    Definition ge25519_sub (P Q: @interp_type Z FE) :=
        proj1_sig (ge25519_sub' P Q).

    Definition ge25519_mul (P Q: @interp_type Z FE) :=
        proj1_sig (ge25519_mul' P Q).

    Definition ge25519_opp (P: @interp_type Z FE) :=
        proj1_sig (ge25519_opp' P).
  End Expressions.

  Module AddExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound ++ feBound.

    Definition prog: NAry 20 Z (@HL.Expr Z ResultType) :=
        Eval cbv in (flatten (fun p => (flatten (fun q => ge25519_add p q)))).
  End AddExpr.

  Module SubExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound ++ feBound.

    Definition ge25519_sub_expr :=
      Eval cbv beta delta [fe25519 carry_add mul carry_sub opp Let_In] in
        carry_sub.

    Definition prog: NAry 20 Z (@HL.Expr Z ResultType) :=
        Eval cbv in (flatten (fun p => (flatten (fun q => ge25519_sub p q)))).
  End SubExpr.

  Module MulExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 20.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound ++ feBound.

    Definition prog: NAry 20 Z (@HL.Expr Z ResultType) :=
        Eval cbv in (flatten (fun p => (flatten (fun q => ge25519_mul p q)))).
  End MulExpr.

  Module OppExpr <: Expression.
    Definition bits: nat := bits.
    Definition inputs: nat := 10.
    Definition width: Width bits := width.
    Definition ResultType := FE.
    Definition inputBounds := feBound.

    Definition prog: NAry 10 Z (@HL.Expr Z ResultType) :=
        Eval cbv in (flatten ge25519_opp).
  End OppExpr.

  Module Add := Pipeline AddExpr.
  Module Sub := Pipeline SubExpr.
  Module Mul := Pipeline MulExpr.
  Module Opp := Pipeline OppExpr.

  Section Instantiation.
    Require Import InitialRing.

    Definition Binary : Type := NAry 20 (word bits) (@interp_type (word bits) FE).
    Definition Unary : Type := NAry 10 (word bits) (@interp_type (word bits) FE).

    Ltac ast_simpl := cbv [
      Add.bits Add.inputs AddExpr.inputs Add.ResultType AddExpr.ResultType
      Add.W Add.R Add.ZEvaluable Add.WEvaluable Add.REvaluable
      Add.AST.progW Add.LL.progW Add.HL.progW AddExpr.prog

      Sub.bits Sub.inputs SubExpr.inputs Sub.ResultType SubExpr.ResultType
      Sub.W Sub.R Sub.ZEvaluable Sub.WEvaluable Sub.REvaluable
      Sub.AST.progW Sub.LL.progW Sub.HL.progW SubExpr.prog

      Mul.bits Mul.inputs MulExpr.inputs Mul.ResultType MulExpr.ResultType
      Mul.W Mul.R Mul.ZEvaluable Mul.WEvaluable Mul.REvaluable
      Mul.AST.progW Mul.LL.progW Mul.HL.progW MulExpr.prog

      Opp.bits Opp.inputs OppExpr.inputs Opp.ResultType OppExpr.ResultType
      Opp.W Opp.R Opp.ZEvaluable Opp.WEvaluable Opp.REvaluable
      Opp.AST.progW Opp.LL.progW Opp.HL.progW OppExpr.prog

      HLConversions.convertExpr CompileHL.Compile CompileHL.compile

      LL.interp LL.uninterp_arg LL.under_lets LL.interp_arg

      ZEvaluable WordEvaluable RWVEvaluable rwv_value
      eadd esub emul eand eshiftr toT fromT

      interp_binop interp_type FE liftN NArgMap id
      omap option_map orElse].

    (* Tack this on to make a simpler AST, but it really slows us down *)
    Ltac word_simpl := cbv [
      AddExpr.bits SubExpr.bits MulExpr.bits OppExpr.bits bits
      NToWord posToWord natToWord wordToNat wordToN wzero'
      Nat.mul Nat.add].

    Ltac kill_conv := let p := fresh in
      pose proof N2Z.id as p; unfold Z.to_N in p;
      repeat rewrite p; clear p;
      repeat rewrite NToWord_wordToN.

    Local Notation unary_eq f g
      := (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9,
             f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
             = g x0 x1 x2 x3 x4 x5 x6 x7 x8 x9).
    Local Notation binary_eq f g
      := (forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9,
             f x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9
             = g x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9).

    Definition add'
      : {f: Binary |
         binary_eq f (NArgMap (fun x => Z.of_N (wordToN x)) Add.AST.progW) }.
    Proof. eexists; intros; ast_simpl; kill_conv; reflexivity. Defined.

    Definition sub'
      : {f: Binary |
         binary_eq f (NArgMap (fun x => Z.of_N (wordToN x)) Sub.AST.progW) }.
    Proof. eexists; ast_simpl; kill_conv; reflexivity. Defined.

    Definition mul'
      : {f: Binary |
         binary_eq f (NArgMap (fun x => Z.of_N (wordToN x)) Mul.AST.progW) }.
    Proof. eexists; ast_simpl; kill_conv; reflexivity. Defined.

    Definition opp' : {f: Unary |
      unary_eq f (NArgMap (fun x => Z.of_N (wordToN x)) Opp.AST.progW) }.
    Proof. eexists; ast_simpl; kill_conv; reflexivity. Defined.

    Definition add := Eval simpl in proj1_sig add'.
    Definition sub := Eval simpl in proj1_sig sub'.
    Definition mul := Eval simpl in proj1_sig mul'.
    Definition opp := Eval simpl in proj1_sig opp'.
  End Instantiation.
End GF25519.
(*
Extraction "GF25519Add" GF25519.Add.
Extraction "GF25519Sub" GF25519.Sub.
Extraction "GF25519Mul" GF25519.Mul.
Extraction "GF25519Opp" GF25519.Opp.
*)
