
Require Import NArith.
Require Export Qhasm AlmostQhasm Conversion.

Module AlmostConversion <: Conversion AlmostQhasm Qhasm.
  Import QhasmCommon AlmostQhasm Qhasm.
  Import ListNotations.

  Fixpoint almostToQhasm' (prog: AlmostProgram) (lblStart: N): Qhasm.Program :=
    let label0 := (lblStart * 2)%N in
    let label1 := (label0 + 1)%N in

    match prog with
    | ASkip => []
    | ASeq a b => (almostToQhasm' a label0) ++ (almostToQhasm' b label1)
    | AAssign a => [ QAssign a ]
    | AOp a => [ QOp a ]
    | ACond c a b =>
      let start := N.shiftl 2 label0 in
      let finish := (start + 1)%N in
      [QCond c (N.to_nat start)] ++
      (almostToQhasm' b (start + 2)) ++
      [QCond CTrue (N.to_nat finish)] ++
      [QLabel (N.to_nat start)] ++
      (almostToQhasm' a (start + 3)) ++
      [QLabel (N.to_nat finish)]
    | AWhile c a =>
      let start := N.to_nat (N.shiftl 1 label0) in
      let test := S start in
      [ QCond CTrue test ;
        QLabel start ] ++
        (almostToQhasm' a label1) ++
      [ QLabel test;
        QCond c start ]
    | ADef lbl f x =>
      let start' := N.shiftl 1 label0 in
      let start'' := (1 + start')%N in

      [ QLabel lbl ] ++
      (almostToQhasm' f start') ++
      [ QRet ] ++
      (almostToQhasm' x start'')

    | ACall lbl => [QCall lbl]
    end.

  Definition convertProgram (prog: AlmostQhasm.Program) := Some (almostToQhasm' prog 0%N).
  Definition convertState (st: Qhasm.State): option AlmostQhasm.State := Some st.

  Lemma convert_spec:  forall a a' b b' prog prog',
    convertProgram prog = Some prog' ->
    convertState a = Some a' -> convertState b = Some b' ->
    Qhasm.evaluatesTo prog' a b <-> AlmostQhasm.evaluatesTo prog a' b'.
  Admitted.

End AlmostConversion.
