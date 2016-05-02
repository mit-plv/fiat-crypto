
Require Export Language Conversion QhasmCommon QhasmUtil.
Require Export AlmostQhasm Pseudo State.
Require Export Bedrock.Word.
Require Export List.
Require Vector.

Module PseudoConversion (M: PseudoMachine).
  Import QhasmCommon AlmostQhasm State.
  Import ListNotations.

  Module P := Pseudo M.

  Fixpoint take {A} (n: nat) (lst: list A) :=
    match n with
    | O => []
    | S m =>
      match lst with
      | [] => []
      | l :: ls => l :: (take m ls)
      end
    end.

  Module Conv <: Conversion P AlmostQhasm.
    Import P M.

    Definition activeRegisters := 6.
    Definition overflowReg := ireg 6.

    Definition convertState (st: AlmostQhasm.State): P.State :=
      match st with
      | fullState _ stackState _ =>
        take vars (map (fun x => NToWord width (snd x))
                       (NatM.elements stackState))
      end.

    Fixpoint convertProgram' {n m} (prog: Pseudo n m): option AlmostQhasm.Program :=
      match prog with
      | PVar n i =>
        (AAssign (ARegRegInt width (ireg 0) (ireg i)))

      | PConst n c =>
        (AAssign (AConstInt (ireg n) (iconst c)))

      | PBin n m o a b => None

      | PNat n o v => None

      | PShift n o a x => None

      | PLet n k m f g => None

      | PComp n k m f g => None

      | PComb n a b f g => None

      | PIf n m o i0 i1 l r => None

      | PFunExp n f e => None

      end.

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      AlmostQhasm.evaluatesTo prog' a b <-> P.evaluatesTo prog a' b'.
    Admitted.

  End Conv.
End PseudoConversions.
