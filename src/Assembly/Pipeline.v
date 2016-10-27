Require Export Crypto.Assembly.QhasmCommon.

Require Export Crypto.Assembly.PhoasCommon.
Require Export Crypto.Assembly.HL.
Require Export Crypto.Assembly.LL.
Require Export Crypto.Assembly.Compile.
Require Export Crypto.Assembly.Conversions.
Require Export Crypto.Assembly.StringConversion.
Require Export Crypto.Assembly.State.

Require Export Crypto.Util.Notations.
Require Export Crypto.Util.LetIn.

Require Export Coq.ZArith.BinInt.

Require Export ExtrOcamlBasic.
Require Export ExtrOcamlString.

Module Type Expression.
  Parameter bits: nat.
  Parameter width: Width bits.
  Parameter inputs: nat.
  Parameter inputBounds: list Z.
  Parameter ResultType: type.

  Parameter prog: NAry inputs Z (@HL.Expr Z ResultType).
End Expression.

Module Pipeline (Input: Expression).
  Definition bits := Input.bits.
  Definition inputs := Input.inputs.
  Definition ResultType := Input.ResultType.

  Hint Unfold bits inputs ResultType.
  Definition width: Width bits := Input.width.

  Definition W: Type := word bits.
  Definition R: Type := option RangeWithValue.
  Definition B: Type := option (@BoundedWord bits).

  Instance ZEvaluable : Evaluable Z := ZEvaluable.
  Instance WEvaluable : Evaluable W := @WordEvaluable bits.
  Instance REvaluable : Evaluable R := @RWVEvaluable bits.
  Instance BEvaluable : Evaluable B := @BoundedEvaluable bits.

  Existing Instances ZEvaluable WEvaluable REvaluable BEvaluable.

  Module Util.
    Fixpoint applyProgOn {A B k} (d: A) ins (f: NAry k A B): B :=
      match k as k' return NAry k' A B -> B with
      | O => id
      | S m => fun f' =>
        match ins with
        | cons x xs => @applyProgOn A B m d xs (f' x)
        | nil => @applyProgOn A B m d nil (f' d)
        end
      end f.
  End Util.

  Module HL.
    Definition progZ: NAry inputs Z (@HL.Expr Z ResultType) :=
      Input.prog.

    Definition progR: NAry inputs Z (@HL.Expr R ResultType) :=
      liftN (fun x v => @HLConversions.convertExpr Z R _ _ _ (x v)) Input.prog.

    Definition progW: NAry inputs Z (@HL.Expr W ResultType) :=
      liftN (fun x v => @HLConversions.convertExpr Z W _ _ _ (x v)) Input.prog.
  End HL.

  Module LL.
    Definition progZ: NAry inputs Z (@LL.expr Z Z ResultType) :=
      liftN CompileHL.Compile HL.progZ.

    Definition progR: NAry inputs Z (@LL.expr R R ResultType) :=
      liftN CompileHL.Compile HL.progR.

    Definition progW: NAry inputs Z (@LL.expr W W ResultType) :=
      liftN CompileHL.Compile HL.progW.
  End LL.

  Module AST.
    Definition progZ: NAry inputs Z (@interp_type Z ResultType) :=
      liftN LL.interp LL.progZ.

    Definition progR: NAry inputs Z (@interp_type R ResultType) :=
      liftN LL.interp LL.progR.

    Definition progW: NAry inputs Z (@interp_type W ResultType) :=
      liftN LL.interp LL.progW.
  End AST.

  Module Qhasm.
    Definition pair :=
      @CompileLL.compile bits width ResultType _ LL.progW.

    Definition prog := option_map (@fst _ _) pair.

    Definition outputRegisters := option_map (@snd _ _) pair.

    Definition code := option_map StringConversion.convertProgram prog.
  End Qhasm.

  Module Bounds.
    Definition input := map (fun x => range N 0%N (Z.to_N x)) Input.inputBounds.

    Definition upper := Z.of_N (wordToN (wones bits)).

    Definition prog :=
      Util.applyProgOn upper Input.inputBounds LL.progR.

    Definition valid := LLConversions.check (n := bits) (f := id) prog.

    Definition output :=
      typeMap (option_map (fun x => range N (rwv_low x) (rwv_high x)))
              (LL.interp prog).
  End Bounds.
End Pipeline.

Module SimpleExample.
  Module SimpleExpression <: Expression.
    Import ListNotations.

    Definition bits: nat := 32.
    Definition width: Width bits := W32.
    Definition inputs: nat := 1.
    Definition ResultType := TT.

    Definition inputBounds: list Z := [ (2^30)%Z ].

    Existing Instance ZEvaluable.

    Definition prog: NAry 1 Z (@HL.Expr Z TT).
      intros x var.
      refine (HL.Binop OPadd (HL.Const x) (HL.Const 5%Z)).
    Defined.
  End SimpleExpression.

  Module SimplePipeline := Pipeline SimpleExpression.
End SimpleExample.
