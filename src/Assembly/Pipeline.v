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
  Parameter ResultType: type.
  Parameter hlProg: NAry inputs Z (@HL.expr Z (@interp_type Z) ResultType).
  Parameter inputBounds: list Z.
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

  Instance ZEvaluable : Evaluable Z := @ZEvaluable bits.
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
    Definition progZ: NAry inputs Z (@HL.expr Z (@LL.arg Z Z) ResultType) :=
      liftN (HLConversions.mapVar
               (fun t => @LL.uninterp_arg_as_var _ _ t)
               (fun t => @LL.interp_arg _ t))
          Input.hlProg.

    Definition progR: NAry inputs Z (@HL.expr R (@LL.arg R Z) ResultType) :=
      liftN (@HLConversions.convertExpr Z R _ _ ResultType _) (
        liftN (HLConversions.mapVar
          (fun t => @LL.uninterp_arg_as_var R Z t)
          (fun t => fun x => typeMap (fun x =>
              Z.of_N (orElse 0%N (option_map rwv_value x))) (
            @LL.interp_arg' _ _ t LLConversions.rangeOf x))) (

        Input.hlProg)).

    Definition progW: NAry inputs Z (@HL.expr W (@LL.arg W Z) ResultType) :=
      liftN (@HLConversions.convertExpr Z W _ _ ResultType _) (
        liftN (HLConversions.mapVar
            (fun t => @LL.uninterp_arg_as_var W Z t)
            (fun t => fun x => typeMap (fun x => Z.of_N (wordToN x)) (
          @LL.interp_arg' _ _ t (fun x => NToWord bits (Z.to_N x)) x))) (

        Input.hlProg)).
  End HL.

  Module LL.
    Definition progZ: NAry inputs Z (@LL.expr Z Z ResultType) :=
      liftN CompileHL.compile HL.progZ.

    Definition progR: NAry inputs Z (@LL.expr R Z ResultType) :=
      liftN CompileHL.compile HL.progR.

    Definition progW: NAry inputs Z (@LL.expr W Z ResultType) :=
      liftN CompileHL.compile HL.progW.
  End LL.

  Module AST.
    Definition progZ: NAry inputs Z (@interp_type Z ResultType) :=
      liftN (LL.interp' (fun x => x)) LL.progZ.

    Definition progR: NAry inputs Z (@interp_type R ResultType) :=
      liftN (LL.interp' (fun x => Some (rwv 0%N (Z.to_N x) (Z.to_N x)))) LL.progR.

    Definition progW: NAry inputs Z (@interp_type W ResultType) :=
      liftN (LL.interp' (fun x => NToWord bits (Z.to_N x))) LL.progW.
  End AST.

  Module Qhasm.
    Definition pair := @CompileLL.compile bits width ResultType _ LL.progW.

    Definition prog := option_map fst pair.

    Definition outputRegisters := option_map snd pair.

    Definition code := option_map StringConversion.convertProgram prog.
  End Qhasm.

  Module Bounds.
    Definition input := Input.inputBounds.

    Definition prog := Util.applyProgOn (2 ^ (Z.of_nat bits) - 1)%Z input LL.progR.

    Definition valid := LLConversions.check (n := bits) prog.

    Definition output :=
      LL.interp' (fun x => Some (rwv 0%N (Z.to_N x) (Z.to_N x))) prog.
  End Bounds.
End Pipeline.

Module SimpleExample.
  Module SimpleExpression <: Expression.
    Import ListNotations.

    Definition bits: nat := 32.
    Definition width: Width bits := W32.
    Definition inputs: nat := 1.
    Definition ResultType := TT.

    Definition hlProg: NAry 1 Z (@HL.expr Z (@interp_type Z) TT) :=
      Eval vm_compute in (fun x => HL.Binop OPadd (HL.Var x) (HL.Const 5%Z)).

    Definition inputBounds: list Z := [ (2^30)%Z ].
  End SimpleExpression.

  Module SimplePipeline := Pipeline SimpleExpression.

  Export SimplePipeline.
End SimpleExample.

