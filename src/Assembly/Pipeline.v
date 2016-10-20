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
  Parameter hlProg: NAry inputs Z (@HL.expr Z (@LL.arg Z Z) ResultType).
  Parameter inputBounds: list (Range N).
End Expression.

Module Pipeline (Input: Expression).
  Export Input.

  Definition llProg: NAry inputs Z (@LL.expr Z Z ResultType) :=
    liftN CompileHL.compile hlProg.

  Definition wordProg: NAry inputs (@CompileLL.WArg bits TT) (@LL.expr _ _ ResultType) :=
    NArgMap (fun x => Z.of_N (wordToN (LL.interp_arg (t := TT) x))) (
      liftN (LLConversions.convertZToWord bits) llProg).

  Definition qhasmProg := CompileLL.compile (w := width) wordProg.

  Definition qhasmString : option string :=
    match qhasmProg with
    | Some (p, _) => StringConversion.convertProgram p
    | None => None
    end.

  Import LLConversions.

  Definition RWV: Type := option RangeWithValue.

  Definition rwvProg: NAry inputs RWV (@LL.expr RWV RWV ResultType) :=
    NArgMap (fun x => orElse 0%Z (option_map (fun v => Z.of_N (value v)) x) ) (
      liftN (@convertExpr Z RWV ZEvaluable (RWVEval (n := bits)) _) llProg).

  Fixpoint applyProgOn {A B k} ins (f: NAry k (option A) B): B :=
    match k as k' return NAry k' (option A) B -> B with
    | O => id
    | S m => fun f' =>
      match ins with
      | cons x xs => @applyProgOn A B m xs (f' x)
      | nil => @applyProgOn A B m nil (f' None)
      end
    end f.

  Definition outputBounds :=
    applyProgOn (map (@Some _) (map from_range inputBounds)) (
      liftN (fun e => typeMap (option_map proj) (@LL.interp RWV (@RWVEval bits) _ e))
        rwvProg).

  Definition valid :=
    applyProgOn (map (@Some _) (map from_range inputBounds)) (
     liftN (@check bits _ RWV (@RWVEval bits)) rwvProg).
End Pipeline.

Module SimpleExample.
  Module SimpleExpression <: Expression.
    Import ListNotations.

    Definition bits: nat := 32.
    Definition width: Width bits := W32.
    Definition inputs: nat := 1.
    Definition ResultType := TT.

    Definition hlProg: NAry 1 Z (@HL.expr Z (@LL.arg Z Z) TT) :=
        Eval vm_compute in (fun x => HL.Binop OPadd (HL.Const x) (HL.Const 5%Z)).

    Definition inputBounds: list (Range N) := [ range N 0%N (Npow2 31) ].
  End SimpleExpression.

  Module SimplePipeline := Pipeline SimpleExpression.

  Export SimplePipeline.
End SimpleExample.
