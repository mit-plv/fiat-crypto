
Require Export Language Conversion QhasmCommon.
Require Export AlmostQhasm Pseudo State.
Require Export Bedrock.Word.
Require Export List.
Require Vector.

Module PseudoConversion (P: Pseudo) <: Conversion P AlmostQhasm.
  Import QhasmCommon AlmostQhasm P State.
  Import ListNotations.

  Definition convertState (st: AlmostQhasm.State): P.State :=
    match st with
    | fullState _ _ stackState _ =>
      map (fun x => NToWord width (snd x)) (NatM.elements stackState)
    end.

  Fixpoint convertProgram' (prog: Pseudo): option AlmostQhasm.Program :=
    match prog with
    | PVar n i =>
      (AAssign 
    | PConst n c =>
      (AAssign 

    (* TODO (rsloan) *)
    | PBin n m o a b => None
    | PNat n o v => None
    | PShift n o a x => None

    | PLet n k m f g => None
    | PComp n k m f g => None
    | PComb n a b f g => None

    | PIf n m o i0 i1 l r => None
    | PFunExp n f e => None
    end.

  convertProgram (prog: S.Program): option AlmostQhasm.Program :=

  Lemma convert_spec:  forall a a' b b' prog prog',
    convertProgram prog = Some prog' ->
    convertState a = Some a' -> convertState b = Some b' ->
    AlmostQhasm.evaluatesTo prog' a b <-> Pseudo.evaluatesTo prog a' b'.
  Admitted.

End GallinaConversion.
