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
  Parameter inputBounds: list (@BoundedWord bits).
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

  Definition B: Type := option (@BoundedWord bits).

  Definition boundedProg: NAry inputs B (@LL.expr B B ResultType) :=
    NArgMap (fun x =>
        orElse (Z.of_N (N.pred (Npow2 bits)))
               (option_map Z.of_N (option_map Evaluables.high x))) (
      liftN (LLConversions.convertZToBounded bits) llProg).

  Fixpoint valid' {T k} ins (f: NAry k B T) :=
    match k as k' return NAry k' B T -> T with
    | O => id
    | S m => fun f' =>
      match ins with
      | cons x xs => @valid' _ m xs (f' x)
      | nil => @valid' _ m nil (f' None)
      end
    end f.

  Definition outputBounds := valid' (map (@Some _) inputBounds) boundedProg.

  Definition valid :=
    valid' (map (@Some _) inputBounds) (liftN (LLConversions.check) boundedProg).
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

    Definition inputBounds: list (@BoundedWord bits) := [ any ].
  End SimpleExpression.

  Module SimplePipeline := Pipeline SimpleExpression.

  Export SimplePipeline.
End SimpleExample.
