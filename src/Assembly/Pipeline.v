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
  Parameter hlProg: NAry inputs Z (@HL.Expr' Z ResultType).
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
    Transparent HL.Expr'.

    Definition progZ: NAry inputs Z (@HL.expr Z (@LL.arg Z Z) ResultType).
      refine (liftN _ Input.hlProg); intro X; apply X.
      refine (fun t x => @LL.uninterp_arg Z Z t x).
    Defined.

    Definition progR: NAry inputs Z (@HL.expr R (@LL.arg R R) ResultType).
      refine (liftN _ _); [eapply (@HLConversions.convertExpr Z R _ _)|].
      refine (liftN _ Input.hlProg); intro X; apply X.
      refine (fun t x => @LL.uninterp_arg R R t (typeMap LLConversions.rangeOf x)).
    Defined.

    Definition progW: NAry inputs Z (@HL.expr W (@LL.arg W W) ResultType).
      refine (liftN _ _); [eapply (@HLConversions.convertExpr Z W _ _)|].
      refine (liftN _ Input.hlProg); intro X; apply X.
      refine (fun t x => @LL.uninterp_arg W W t (typeMap (fun v =>
        NToWord bits (Z.to_N v)) x)).
    Defined.
  End HL.

  Module LL.
    Definition progZ: NAry inputs Z (@LL.expr Z Z ResultType) :=
      liftN CompileHL.compile HL.progZ.

    Definition progR: NAry inputs Z (@LL.expr R R ResultType) :=
      liftN CompileHL.compile HL.progR.

    Definition progW: NAry inputs Z (@LL.expr W W ResultType) :=
      liftN CompileHL.compile HL.progW.
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
    Definition pair := @CompileLL.compile bits width ResultType _ LL.progW.

    Definition prog := option_map fst pair.

    Definition outputRegisters := option_map snd pair.

    Definition code := option_map StringConversion.convertProgram prog.
  End Qhasm.

  Module Bounds.
    Definition input := Input.inputBounds.

    Definition prog := Util.applyProgOn (2 ^ (Z.of_nat bits) - 1)%Z input LL.progR.

    Definition valid := LLConversions.check (n := bits) (f := id) prog.

    Definition output := LL.interp prog.
  End Bounds.
End Pipeline.

Module SimpleExample.
  Module SimpleExpression <: Expression.
    Import ListNotations.

    Definition bits: nat := 32.
    Definition width: Width bits := W32.
    Definition inputs: nat := 1.
    Definition ResultType := TT.

    Definition hlProg': NAry 1 Z (@HL.Expr' Z TT).
      intros x t f.
      refine (HL.Binop OPadd (HL.Var (f TT x)) (HL.Const 5%Z)).
    Defined.

    Definition hlProg: NAry 1 Z (@HL.Expr' Z TT) :=
      Eval vm_compute in hlProg'.

    Definition inputBounds: list Z := [ (2^30)%Z ].
  End SimpleExpression.

  Module SimplePipeline := Pipeline SimpleExpression.

  Export SimplePipeline.
End SimpleExample.

