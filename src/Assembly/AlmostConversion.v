
Require Import Coq.NArith.NArith.
Require Export Crypto.Assembly.Qhasm Crypto.Assembly.AlmostQhasm Crypto.Assembly.Conversion.

Module AlmostConversion <: Conversion AlmostQhasm Qhasm.
  Import QhasmCommon AlmostQhasm Qhasm.
  Import ListNotations.

  Fixpoint almostToQhasm' (prog: AlmostProgram) (lblStart: N): list QhasmStatement :=
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

  Transparent Qhasm.Program AlmostQhasm.Program.

  Definition convertProgram x y (prog: AlmostQhasm.Program x):
      option (Qhasm.Program y) :=
    Some (almostToQhasm' prog 0%N).

  Definition convertState x y (st: Qhasm.State y):
      option (AlmostQhasm.State x) :=
    Some st.

  Lemma convert_spec: forall pa pb a a' b b' prog prog',
    convertProgram pa pb prog = Some prog' ->
    convertState pa pb a = Some a' ->
    convertState pa pb b = Some b' ->
    Qhasm.evaluatesTo pb prog' a b <-> AlmostQhasm.evaluatesTo pa prog a' b'.
  Admitted.

End AlmostConversion.
