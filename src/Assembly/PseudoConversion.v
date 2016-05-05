
Require Export Language Conversion QhasmCommon QhasmUtil.
Require Export AlmostQhasm Pseudo State.
Require Export Bedrock.Word NArith NPeano.
Require Export List Sumbool.
Require Vector.

Module PseudoConversion (M: PseudoMachine).
  Import QhasmCommon AlmostQhasm State Util.
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

    Definition activeRegisters := 5.
    Definition r0 := ireg 5. (* Invariant: these are never used in a Mapping *)
    Definition r1 := ireg 6.

    Definition convertState (st: AlmostQhasm.State): option P.State :=
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

    Definition freshMapping (cur: list Mapping) (len: nat): list Mapping :=
      let used := (fix g (lst: list Mapping) :=
        match lst with
        | nil => []
        | cons c cs =>
          match c with
          | stackM _ v _ => cons v (g cs)
          | _ => g cs
          end
        end) cur in

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
            let s := stack loc in

            if (open loc)
            then cons (stackM s (getStackIndex s) eq_refl) (gen rem' bound')
            else gen rem bound'
          end
        end) len maxStack.

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

    Definition wordToConstM (w: word width) :=
      constM (iconst w) (getIConstValue (iconst w)) eq_refl.

    (* Invariant: never return r0 or r1 in our mapping *)
    Definition binProg (op: WBinOp) (a b: Mapping):
        AlmostQhasm.Program * Mapping :=
      let iop :=
        match op with
        | Wplus => IPlus
        | Wminus => IMinus
        | _ => IAnd
        end in

      match (a, b) with
      | (regM ra va pa, regM rb vb _) =>
        (AOp (IOpReg width iop ra rb), regM ra va pa)

      | (stackM ra va _, regM rb vb pb) =>
        (ASeq (AAssign (ARegStackInt width r0 ra))
              (AOp (IOpReg width iop rb r0)),
         regM rb vb pb) (* Assumption: commutativity forall IntOp *)

      | (regM ra va pa, stackM rb vb _) =>
        (ASeq (AAssign (ARegStackInt width r0 rb))
              (AOp (IOpReg width iop ra r0)),
         regM ra va pa)

      | (stackM ra va pa, stackM rb vb _) =>
        (ASeq (AAssign (ARegStackInt width r1 ra))
          (ASeq (AAssign (ARegStackInt width r0 rb))
            (ASeq (AOp (IOpReg width iop r1 r0))
              (AAssign (AStackRegInt width ra r1)))),
         stackM ra va pa)

      | (stackM ra va pa, constM rb vb _) =>
        (ASeq (AAssign (ARegStackInt width r0 ra))
          (ASeq (AOp (IOpConst width iop r0 rb))
            (AAssign (AStackRegInt width ra r0))),
         stackM ra va pa)

      | (constM ra va _, constM rb vb _) =>
        (ASkip,
          let v := match iop with
            | IPlus => wplus
            | IMinus => wminus
            | _ => wand
            end width (natToWord width va) (natToWord width vb)
          in constM (iconst v) (getIConstValue (iconst v)) eq_refl)

      | _ => (ASkip, wordToConstM (wzero width))
      end.

    Definition shiftProg (op: WShiftOp) (m: Mapping) (n: Index width):
        AlmostQhasm.Program * Mapping :=
      let qop := match op with | Wshl => Shl | Wshr => Shr end in
      match m with
      | regM r v _ =>
        (AOp (OpRot width qop r n), regM r (getIRegIndex r) eq_refl)
      | stackM r v _ =>
        (ASeq (AAssign (ARegStackInt width r0 r))
          (ASeq (AOp (OpRot width qop r0 n))
            (AAssign (AStackRegInt width r r0))),
         m)
      | constM r v _ =>
        (ASkip, wordToConstM
          match qop with
          | Shl => NToWord width (N.shiftl_nat (N.of_nat v) n)
          | Shr => NToWord width (N.shiftr_nat (N.of_nat v) n)
          end)
      end.

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
        option_map' (nth_error mapping n) (fun v => (ASkip, [v]))

      | PConst n c =>
        Some (ASkip, [constM (iconst c) (getIConstValue (iconst c)) eq_refl])

      | PBin n o a b =>
        otup_map (convertProgram' a mapping avoid) (fun aprog amap =>
          let tmp := freshMapping (avoid ++ mapping ++ amap) n in
          let mov := moveMapping mapping tmp in

          otup_map (convertProgram' b tmp (avoid ++ amap)) (fun bprog bmap =>
            match (amap, bmap) with
            | ([av], [bv]) => let oper := binProg o av bv in

              Some (ASeq mov (ASeq bprog (ASeq aprog (fst oper))), [snd oper])

            | _ => None
            end))

      | PNat n o v =>
        match (applyNat o v) with
        | Some [c] => let ic := iconst c in

          Some (ASkip, [constM ic (getIConstValue ic) eq_refl])

        | _ => None
        end

      | PShift n o a x =>
        otup_map (convertProgram' a mapping avoid) (fun aprog amap =>
          match amap with
          | [av] => let oper := shiftProg o av x in

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
