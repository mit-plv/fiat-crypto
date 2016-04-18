
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
      let tru := N.to_nat (N.shiftl 1 label0) in
      let finish := S tru in
      [QJmp c tru] ++
      (almostToQhasm' b label1) ++
      [QJmp TestTrue finish] ++
      [QLabel tru] ++
      (almostToQhasm' a label1) ++
      [QLabel finish]
    | AWhile c a =>
      let start := N.to_nat (N.shiftl 1 label0) in
      let test := S start in
      [ QJmp TestTrue test ;
        QLabel start ] ++
        (almostToQhasm' a label1) ++
      [ QLabel test;
        QJmp c start ]
    end.

  Definition convertProgram (prog: AlmostQhasm.Program) := Some (almostToQhasm' prog 0%N).
  Definition convertState (st: Qhasm.State): option AlmostQhasm.State := Some st.

  Lemma convert_spec:  forall a a' b b' prog prog',
    convertProgram prog = Some prog' ->
    convertState a = Some a' -> convertState b = Some b' ->
    Qhasm.evaluatesTo prog' a b <-> AlmostQhasm.evaluatesTo prog a' b'.
  Admitted.

End AlmostConversion.
