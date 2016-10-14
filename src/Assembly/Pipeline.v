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
  Parameter inputUpperBounds: list (@WordRangeOpt bits).
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

  Definition Range := @WordRangeOpt bits.

  Definition rangeProg: NAry inputs Range (@LL.expr Range Range ResultType) :=
    NArgMap (fun x =>
        getOrElse (Z.of_N (N.pred (Npow2 bits)))
                  (option_map Z.of_N (getUpperBoundOpt x))) (
      liftN (LLConversions.convertZToWordRangeOpt bits) llProg).

  Definition rangeCheck: NAry inputs Range bool :=
    liftN (LLConversions.check') rangeProg.

  Definition rangeValid: bool :=
    let F := (fix rangeValid' k ins (f: NAry k Range bool) :=
        (match k as k' return NAry k' Range bool -> bool with
        | O => id
        | S m => fun f' =>
          match ins with
          | cons x xs => rangeValid' m xs (f' x)
          | nil => rangeValid' m nil (f' anyWord)
          end
        end f)) in

    F _ inputUpperBounds rangeCheck.
End Pipeline.

Module SimpleExample.
  Module SimpleExpression <: Expression.
    Definition bits: nat := 32.
    Definition width: Width bits := W32.
    Definition inputs: nat := 1.
    Definition ResultType := TT.

    Definition hlProg: NAry 1 Z (@HL.expr Z (@LL.arg Z Z) TT) :=
        Eval vm_compute in (fun x => HL.Binop OPadd (HL.Const x) (HL.Const 5%Z)).

    Definition inputUpperBounds: list (@WordRangeOpt bits) := nil.
  End SimpleExpression.

  Module SimplePipeline := Pipeline SimpleExpression.

  Export SimplePipeline.
End SimpleExample.
