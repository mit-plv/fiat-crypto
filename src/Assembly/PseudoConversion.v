
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

    Definition omap {A B} (x: option A) (f: A -> option B) :=
        match x with | Some y => f y | _ => None end.

    Notation "A <- X ; B" := (omap X (fun A => B)) (at level 70).

    Fixpoint convertProgram' {n m} (prog: Pseudo n m) (mapping: list nat) (start: nat):
        option (Medial * (list nat)) :=
      let nextStart := start * 2 in
      let nextStart' := nextStart + 1 in

      match prog with
      | PVar n i => v <- nth_error mapping i; Some (MSkip, [v])
      | PConst n c => Some (MAssign (MAConst start c), [start])
      | PBin n o p =>
        t <- convertProgram' p mapping start;

        match (snd t) with
        | [l; r] => Some (MSeq (fst t) (MOp (MIOpReg o l r)), [l])
        | _ => None
        end

      | PDual n o p => 
        t <- convertProgram' p mapping nextStart;

        match (snd t) with
        | [l; r] => Some (MSeq (fst t) (MOp (MDOpReg o l r (Some start))), [l; start])
        | _ => None
        end

      | PShift n o a x =>
        t <- convertProgram' x mapping (S start);

        match (snd t) with
        | [v] => Some (MSeq (fst t) (MOp (MOpRot o v a)), [v])
        | _ => None
        end

      | PLet n k m f g =>
        ft <- convertProgram' f mapping nextStart;
        gt <- convertProgram' g (mapping ++ (snd ft)) nextStart';
        Some (MSeq (fst ft) (fst gt), (snd gt))

      | PComp n k m f g =>
        ft <- convertProgram' f mapping nextStart;
        gt <- convertProgram' g (snd ft) nextStart';
        Some (MSeq (fst ft) (fst gt), (snd gt))

      | PComb n a b f g => 
        ft <- convertProgram' f mapping nextStart;
        gt <- convertProgram' f mapping nextStart';
        Some (MSeq (fst ft) (fst gt)), (snd ft) ++ (snd gt))

      | _ => None
      end.

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
