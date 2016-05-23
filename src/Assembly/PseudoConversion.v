
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

    Notation "A <- X ; B" := (omap X (fun A => B)) (at level 70, right associativity).

    Fixpoint range (start len: nat): list nat :=
      match len with
      | O => []
      | S len' => start :: (range (S start) len')
      end.

    Fixpoint list_split {A} (n: nat) (lst: list A): (list A) * (list A) :=
      match n with
      | O => ([], lst)
      | S m =>
        match lst with
        | [] => ([], [])
        | l :: ls =>
          match list_split m ls with
          | (a, b) => (cons l a, b)
          end
        end
      end.

    Fixpoint convertProgram' {n m}
          (prog: Pseudo n m) (inMap outMap: list nat) (start: nat):
        option (Medial * nat) :=

      match prog with
      | PVar n i =>
        min <- nth_error inMap i;
        mout <- nth_error outMap 0;

        if (Nat.eq_dec min mout)
        then Some (MSkip, start)
        else Some ((MAssign (MAVar mout min)), start)

      | PConst n c =>
        mout <- nth_error outMap 0;
        Some (MAssign (MAConst mout c), start)

      | PBin n o p =>
        t <- convertProgram' p inMap (outMap ++ [start]) (S start);
        a <- nth_error outMap 0;

        Some (MSeq (fst t) (MOp (MIOpReg o a start)), (snd t))

      | PDual n o p =>
        match outMap with
        | [a; b] =>
          x <- nth_error inMap 1;
          t <- convertProgram' p inMap [a; x] start;
          Some (MSeq (fst t) (MOp (MDOpReg o a b (Some x))), snd t)

        | _ => None
        end

      | PShift n o a x =>
        t <- convertProgram' x inMap outMap start;
        b <- nth_error outMap 0;
        Some (MSeq (fst t) (MOp (MOpRot o b a)), snd t)

      | PLet n k m f g =>
        let medMap := range start k in
        ft <- convertProgram' f inMap medMap (start + k);
        gt <- convertProgram' g (inMap ++ medMap) outMap (snd ft);
        Some (MSeq (fst ft) (fst gt), (snd gt))

      | PComp n k m f g =>
        let medMap := range start k in
        ft <- convertProgram' f inMap medMap (start + k);
        gt <- convertProgram' g medMap outMap (snd ft);
        Some (MSeq (fst ft) (fst gt), (snd gt))

      | PComb n a b f g => 
        let outt := list_split a outMap in
        ft <- convertProgram' f inMap (fst outt) start;
        gt <- convertProgram' g inMap (snd outt) (snd ft);
        Some (MSeq (fst ft) (fst gt), snd gt)

      | PIf n m o i0 i1 l r => 
        lt <- convertProgram' l inMap outMap start;
        rt <- convertProgram' r inMap outMap start;
        c0 <- nth_error inMap i0;
        c1 <- nth_error inMap i1;
        Some (MCond (MC o c0 c1) (fst lt) (fst rt), (max (snd rt) (snd lt)))

      | PFunExp n f e => 
        ft <- convertProgram' f inMap outMap start;
        Some (MFunexp e (fst ft), (snd ft))
      end.

    Definition convertProgram (prog: Pseudo vars vars): option Medial :=
      let m := range O vars in
      option_map (@fst Medial nat) (convertProgram' prog m m vars).

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      M.evaluatesTo prog' a b <-> P.evaluatesTo prog a' b'.
    Admitted.

  End Conv.
End PseudoConversion.
