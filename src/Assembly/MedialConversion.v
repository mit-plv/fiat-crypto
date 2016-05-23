
Require Export Language Conversion QhasmCommon QhasmUtil.
Require Export Pseudo Medial AlmostQhasm State.
Require Export Bedrock.Word NArith NPeano.
Require Export List Sumbool.
Require Vector.

Module Allocator (Arch: PseudoMachine).
End Allocator.

Module MedialConversion (Arch: PseudoMachine).
  Import QhasmCommon AlmostQhasm State Util.
  Import ListNotations.

  Module M := Medial Arch.
  Module A := Allocator Arch.

  Fixpoint take {A} (n: nat) (lst: list A) :=
    match n with
    | O => []
    | S m =>
      match lst with
      | [] => []
      | l :: ls => l :: (take m ls)
      end
    end.

  Module Conv <: Conversion M AlmostQhasm.
    Import M A Arch.

    Fixpoint maxIndex (prog: M.Program): nat :=
      match prog with
      | MSkip => O
      | MSeq f g => max (maxIndex f) (maxIndex g)
      | MAssign (MAVar a b) => max a b
      | MAssign (MAConst a _) => a
      | MOp (MIOpConst io a c) => a
      | MOp (MIOpReg io a b) => max a b
      | MOp (MDOpReg duo a b (Some x)) => max a (max b x)
      | MOp (MDOpReg duo a b None) => max a b
      | MOp (MOpRot _ a _) => a
      | MCond _ f g => max (maxIndex f) (maxIndex g)
      | MFunexp e f => maxIndex f
      end.

    Definition convertState (st: AlmostQhasm.State): option M.State :=
      match st with
      | fullState _ stackState _ =>
        Some (take vars (map (fun x => NToWord width (snd x))
                       (NatM.elements stackState)))
      end.

    Definition dec_lt (a b: nat): {(a < b)%nat} + {(a >= b)%nat}.
      assert ({(a <? b)%nat = true} + {(a <? b)%nat <> true})
        by abstract (destruct (a <? b)%nat; intuition);
        destruct H.

      - left; abstract (apply Nat.ltb_lt in e; intuition).

      - right; abstract (rewrite Nat.ltb_lt in n; intuition).
    Defined.

    Inductive Mapping :=
      | regM: forall (r: IReg width) (v: nat), v = getIRegIndex r -> Mapping
      | stackM: forall (r: Stack width) (v: nat), v = getStackIndex r -> Mapping
      | constM: forall (r: IConst width) (v: nat), v = getIConstValue r -> Mapping.

    Definition wordToM (w: word width) :=
      constM (iconst w) (getIConstValue (iconst w)) eq_refl.

    Definition regToM (r: IReg width) :=
      regM r (getIRegIndex r) eq_refl.

    Definition stackToM (s: Stack width) :=
      stackM s (getStackIndex s) eq_refl.

    Definition constToM (c: IConst width) :=
      constM c (getIConstValue c) eq_refl.

    Definition mapping_dec (a b: Mapping): {a = b} + {a <> b}.
      refine (match (a, b) as p' return (a, b) = p' -> _ with
      | (regM x v _, regM y v' _) => fun _ => 
        if (Nat.eq_dec v v') then left _ else right _

      | (stackM x v _, stackM y v' _) => fun _ => 
        if (Nat.eq_dec v v') then left _ else right _

      | (constM x v _, constM y v' _) => fun _ => 
        if (Nat.eq_dec v v') then left _ else right _

      | _ => fun _ => right _
      end (eq_refl (a, b))); admit. (* TODO (rsloan): prove *)
    Defined.

    Fixpoint usedStackEntries (lst: list Mapping): list nat :=
      match lst with
      | nil => []
      | cons c cs =>
        match c with
        | stackM _ v _ => cons v (usedStackEntries cs)
        | _ => usedStackEntries cs
        end
      end.

    Definition getFreshStack (cur: list Mapping) (len: nat): list (Stack width) :=
      let used := usedStackEntries cur in

      let open := fun x =>
        negb (proj1_sig (bool_of_sumbool (in_dec Nat.eq_dec x used))) in

      let maxStack := len + (length cur) in 

     (fix gen (rem bound: nat) :=
        match bound with
        | O => []
        | S bound' =>
          match rem with
          | O => []
          | S rem' =>
            let loc := (maxStack - bound) in

            if (open loc)
            then cons (stack loc) (gen rem' bound')
            else gen rem bound'
          end
        end) len maxStack.

    Definition freshMapping (cur: list Mapping) (len: nat): list Mapping :=
      map (fun s => stackToM s) (getFreshStack cur len).

    Definition getS (lst: list (Stack width)) (n: nat) := nth n lst (stack 0).

    Fixpoint moveMapping (a b: list Mapping): AlmostQhasm.Program :=
      match (a, b) with
      | (cons ahd atl, cons bhd btl) =>
        let curOp := 
          match (ahd, bhd) with
          | (regM ra va _, regM rb vb _) =>
            AAssign (ARegRegInt width rb ra)

          | (stackM ra va _, regM rb vb _) =>
            AAssign (ARegStackInt width rb ra)

          | (regM ra va _, stackM rb vb _) =>
            AAssign (AStackRegInt width rb ra)

          | (stackM ra va _, stackM rb vb _) =>
            ASeq
              (AAssign (ARegStackInt width r0 ra))
              (AAssign (AStackRegInt width rb r0))

          | (constM ra va _, stackM rb vb _) =>
            ASeq
              (AAssign (AConstInt width r0 ra))
              (AAssign (AStackRegInt width rb r0))

          | (constM ra va _, regM rb vb _) =>
            AAssign (AConstInt width rb ra)

          | _ => ASkip
          end in
        ASeq curOp (moveMapping atl btl)
      | _ => ASkip
      end.

    Definition wrapM (m: Mapping) (freeR: IReg width) (freeS: Stack width)
               (inside: IReg width -> (AlmostQhasm.Program * Mapping)):
        (AlmostQhasm.Program * Mapping) :=

      match m with
      | regM r v _ => inside r
      | stackM s v _ =>
        let p := (inside freeR) in

        if (mapping_dec (snd p) (regToM freeR))
        then (ASeq (AAssign (ARegStackInt width freeR s))
               (ASeq (fst p)
               (AAssign (AStackRegInt width s freeR))), m)
        else (ASeq (AAssign (ARegStackInt width freeR s)) (fst p), (snd p))

      | constM r v _ =>
        let p := (inside freeR) in

        if (mapping_dec (snd p) (regToM freeR))
        then (ASeq (AAssign (ARegStackInt width freeR freeS))
               (ASeq (fst p)
                     (AAssign (AStackRegInt width freeS freeR))),
              stackToM freeS)
        else (ASeq (AAssign (ARegStackInt width freeR freeS)) (fst p), (snd p))

      end.

    Definition binProg (op: WBinOp) (a b: Mapping) (avoid: list Mapping):
        AlmostQhasm.Program * Mapping :=
      let iop := match op with | Wplus => IPlus | Wminus => IMinus | _ => IAnd end in
      let sl := getFreshStack avoid 2 in
      
      wrapM a r0 (getS sl 0) (fun ra =>
        wrapM b r1 (getS sl 1) (fun rb =>
          (AOp (IOpReg width iop ra rb), regToM ra))).

    Definition dualProg (op: WDualOp) (a b x: Mapping) (avoid: list Mapping):
        AlmostQhasm.Program * Mapping :=
      let dop := match op with | Wmult => IMult end in
      let sl := getFreshStack avoid 3 in

      wrapM a r0 (getS sl 0) (fun ra =>
        wrapM b r1 (getS sl 1) (fun rb =>
          wrapM x r2 (getS sl 2) (fun rx =>
            (AOp (DOpReg width dop ra rb (Some rx)), regToM ra)))).

    Definition shiftProg (op: WShiftOp) (m: Mapping) (n: Index width) (avoid: list Mapping):
        AlmostQhasm.Program * Mapping :=
      let qop := match op with | Wshl => Shl | Wshr => Shr end in
      let sl := getFreshStack avoid 1 in

      wrapM m r0 (getS sl 0) (fun ra =>
        (AOp (OpRot width qop ra n), regToM ra)).

    Fixpoint convertProgram' {n m}
             (prog: Pseudo n m)
             (mapping: list Mapping)
             (avoid: list Mapping):
        option (AlmostQhasm.Program * list Mapping) :=

      let option_map' := fun x f => option_map f x in
      let otup_map := fun x f =>
        match x with
        | Some res =>
          match (f (fst res) (snd res)) with
          | Some res' => Some res'
          | _ => None
          end
        | _ => None
        end in
 
      match prog with
      | PVar n i =>
        option_map' (nth_error mapping i) (fun v => (ASkip, [v]))

      | PConst n c =>
        Some (ASkip, [wordToM c])

      | PBin n o p =>
        otup_map (convertProgram' a mapping avoid) (fun aprog amap =>
          let tmp := freshMapping (avoid ++ mapping ++ amap) n in
          let mov := moveMapping mapping tmp in

          otup_map (convertProgram' b tmp (avoid ++ amap)) (fun bprog bmap =>
            match (amap, bmap) with
            | ([av], [bv]) =>
              let oper := binProg o av bv (avoid ++ mapping ++ amap ++ bmap) in

              Some (ASeq mov (ASeq bprog (ASeq aprog (fst oper))), [snd oper])

            | _ => None
            end))

      | PDual n o a b =>
        otup_map (convertProgram' a mapping avoid) (fun aprog amap =>
          let tmpb := freshMapping (avoid ++ mapping ++ amap) n in
          let movb := moveMapping mapping tmpb in

          otup_map (convertProgram' b tmpb (avoid ++ amap)) (fun bprog bmap =>
            let xs := getFreshStack (avoid ++ mapping ++ amap ++ bmap) 1 in

            match (amap, bmap) with
            | ([av], [bv]) =>
              let x := stackToM (getS xs 0) in
              let oper := dualProg o av bv x (avoid ++ mapping ++ amap ++ bmap) in

              Some (ASeq movb (ASeq bprog
                (ASeq aprog (fst oper))), [snd oper; x])

            | _ => None
            end))

      | PNat n o v =>
        Some (ASkip, [constToM (iconst (applyNat o v))])

      | PShift n o a x =>
        otup_map (convertProgram' a mapping avoid) (fun aprog amap =>
          match amap with
          | [av] => let oper := shiftProg o av x (mapping ++ avoid ++ amap) in

            Some (ASeq aprog (fst oper), [snd oper])

          | _ => None
          end)

      | PLet n k m f g =>
        otup_map (convertProgram' f mapping avoid) (fun fprog fmap =>
          otup_map (convertProgram' g (mapping ++ fmap) avoid) (fun gprog gmap =>
            Some (ASeq fprog gprog, gmap)))

      | PComp n k m f g =>
        otup_map (convertProgram' f mapping avoid) (fun fprog fmap =>
          otup_map (convertProgram' g fmap avoid) (fun gprog gmap =>
            Some (ASeq fprog gprog, gmap)))

      | PComb n a b f g =>
        otup_map (convertProgram' f mapping avoid) (fun fprog fmap =>
          otup_map (convertProgram' g (mapping ++ fmap) avoid) (fun gprog gmap =>
            Some (ASeq fprog gprog, fmap ++ gmap)))

      | PIf n m o i0 i1 l r =>
        otup_map (convertProgram' l mapping avoid) (fun lprog lmap =>
          otup_map (convertProgram' r mapping avoid) (fun rprog rmap =>
            match (nth_error mapping i0, nth_error mapping i1) with
            | (Some (regM a _ _), Some (regM b _ _)) =>
              Some (ACond (TestInt width o a b) lprog (ASeq rprog (moveMapping rmap lmap)), lmap)
            | _ => None
            end))

      | PFunExp n f e =>
        otup_map (convertProgram' f mapping avoid) (fun fprog fmap =>
          let mov := moveMapping mapping fmap in

          match (freshMapping (avoid ++ fmap) 1) with
          | [regM rc _ _] => 
            Some (ASeq mov
              (ASeq (AAssign (AConstInt width rc (iconst (natToWord width e))))
                (AWhile (TestInt width TGt rc r0)
                  (ASeq fprog
                    (ASeq (AAssign (AConstInt width r0 (iconst (wzero width))))
                      (AOp (IOpConst width IMinus rc (iconst (natToWord width 1)))))))), fmap)
          | [stackM sc _ _] => None
          | _ => None
          end)
      end.

    Definition convertProgram (prog: Pseudo vars vars): option AlmostQhasm.Program :=
      match (convertProgram' prog (freshMapping [] vars) []) with
      | Some (prog', _) => Some prog'
      | _ => None
      end.

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      AlmostQhasm.evaluatesTo prog' a b <-> P.evaluatesTo prog a' b'.
    Admitted.

  End Conv.
End PseudoConversion.
