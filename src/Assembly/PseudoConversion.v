
Require Export Language Conversion QhasmCommon QhasmUtil.
Require Export AlmostQhasm Pseudo Medial State.
Require Export Bedrock.Word NArith NPeano.
Require Export List Sumbool.
Require Vector.

Module PseudoConversion (Arch: PseudoMachine).
  Import QhasmCommon AlmostQhasm State Util.
  Import ListNotations.

  Module P := Pseudo Arch.
  Module M := Medial Arch.

  Module Conv <: Conversion P M.
    Import P M Arch.

    Fixpoint convertState (st: M.State): option P.State :=
      let try_cons := fun {T} (x: option T) (l: list T) =>
        match x with | Some x' => cons x' l | _ => l end in

      let res := (fix cs' (n: nat) :=
         try_cons (option_map (NToWord width) (NatM.find n st))
           (match n with | O => [] | S m => cs' m end)) vars in

      if (Nat.eq_dec (length res) vars)
      then Some res
      else None.

    Definition convertProgram (prog: Pseudo vars vars): option M.Program :=
      match prog with
      | PVar n i => MAssign (MAVar 0 i)
      | PConst n c =>
      | PBin n o p =>
      | PDual n o p =>
      | PNat n o v =>
      | PShift n o a x =>
      | PLet n k m f g =>
      | PComp n k m f g =>
      | PComb n a b f g =>
      | PIf n m o i0 i1 l r =>
      | PFunExp n f e =>
      end.

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      M.evaluatesTo prog' a b <-> P.evaluatesTo prog a' b'.
    Admitted.

  End Conv.
End PseudoConversion.
