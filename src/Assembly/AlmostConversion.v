
Require Import NArith.
Require Export Qhasm AlmostQhasm Conversion.

Module AlmostConversion <: Conversion AlmostQhasm Qhasm.
  Import QhasmCommon AlmostQhasm Qhasm.
  Import ListNotations.

  Fixpoint almostToQhasm' (prog: AlmostProgram) (startLabel: N): Qhasm.Program :=
    let label0 := N.shiftl 1 startLabel in
    let label1 := N.succ label0 in

    match prog with
    | ASkip => []
    | ASeq a b => (almostToQhasm' a label0) ++ (almostToQhasm' b label1)
    | AAssign a => [ QAssign a ]
    | AOp a => [ QOp a ]
    | ACond c a b =>
      let els := N.to_nat (N.shiftl 1 label0) in
      let finish := S els in
      [QJmp (invertConditional c) els] ++
      (almostToQhasm' a label1) ++
      [QJmp TestTrue finish] ++
      [QLabel els] ++
      (almostToQhasm' b label1) ++
      [QLabel finish]
    | AWhile c a =>
      let start := N.to_nat (N.shiftl 1 label0) in
      let finish := S start in
      [ QJmp (invertConditional c) finish ;
        QLabel start ] ++
        (almostToQhasm' a label1) ++
      [ QJmp c start;
        QLabel finish ]
    end.

  Definition convertProgram (prog: AlmostQhasm.Program) := Some (almostToQhasm' prog 0%N).
  Definition convertState (st: Qhasm.State): option AlmostQhasm.State := Some st.

  Lemma convert_spec: forall st' prog,
    match ((convertProgram prog), (convertState st')) with
    | (Some prog', Some st) =>
      match (Qhasm.eval prog' st') with
      | Some st'' => AlmostQhasm.eval prog st = (convertState st'')
      | _ => True
      end
    | _ => True
    end.
  Admitted.

End AlmostConversion.
