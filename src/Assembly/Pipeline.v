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
  Export Input.

  Module Util.
    Fixpoint applyProgOn {A B k} ins (f: NAry k (option A) B): B :=
      match k as k' return NAry k' (option A) B -> B with
      | O => id
      | S m => fun f' =>
        match ins with
        | cons x xs => @applyProgOn A B m xs (f' x)
        | nil => @applyProgOn A B m nil (f' None)
        end
      end f.
  End Util.

  Definition hlProg': NAry inputs Z (@HL.expr Z (@LL.arg Z Z) ResultType) :=
    liftN (HLConversions.mapVar (fun t => @LL.uninterp_arg_as_var _ _ t)
                                (fun t => @LL.interp_arg _ t)) hlProg.

  Definition llProg: NAry inputs Z (@LL.expr Z Z ResultType) :=
    liftN CompileHL.compile hlProg'.

  Definition wordProg: NAry inputs Z (@CompileLL.WExpr bits ResultType) :=
    liftN (LLConversions.ZToWord (n := bits) Z) llProg.

  Definition qhasmProg := CompileLL.compile (w := width) wordProg.

  Definition qhasmString : option string :=
    match qhasmProg with
    | Some (p, _) => StringConversion.convertProgram p
    | None => None
    end.

  Import LLConversions.

  Definition RWV: Type := option RangeWithValue.

  Instance RWVEvaluable : Evaluable RWV := @RWVEvaluable bits.
  Instance ZEvaluable : Evaluable Z := @ZEvaluable bits.

  Existing Instance RWVEvaluable.
  Existing Instance ZEvaluable.

  Arguments HL.expr _ _ _ : clear implicits.
  Arguments LL.arg _ _ _ : clear implicits.
  Arguments interp_type _ _ : clear implicits.
  Definition rwvHL: NAry inputs Z (@HL.expr RWV (@LL.arg RWV Z) ResultType) :=
    liftN (@HLConversions.convertExpr Z RWV _ _ ResultType _) (
      liftN (HLConversions.mapVar
        (fun t => @LL.uninterp_arg_as_var RWV Z t)
        (fun t => fun x => typeMap (fun x => Z.of_N (orElse 0%N (option_map rwv_value x))) (@LL.interp_arg' _ _ t rangeOf x))) (

      hlProg)).

  Definition rwvLL: @LL.expr RWV Z ResultType :=
    Util.applyProgOn (map (@Some _) inputBounds) (
      NArgMap (orElse 0%Z) (
        liftN CompileHL.compile rwvHL)).

  Definition outputBounds :=
    typeMap (option_map rwvToRange) (
      LL.interp' (fun x => Some (rwv 0%N (Z.to_N x) (Z.to_N x))) (
        rwvLL)).

  Definition valid := check (n := bits) rwvLL.
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
