
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
    Definition r0 := ireg 5.
    Definition r1 := ireg 6.

    Definition convertState (st: AlmostQhasm.State): P.State :=
      match st with
      | fullState _ stackState _ =>
        take vars (map (fun x => NToWord width (snd x))
                       (NatM.elements stackState))
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

      | (stackM ra va _, stackM rb vb _) =>
        (ASeq (AAssign (ARegStackInt width r1 ra))
          (ASeq (AAssign (ARegStackInt width r0 rb))
            (AOp (IOpReg width iop r1 r0))),
         regM r1 (getIRegIndex r1) eq_refl)

      | (stackM ra va _, constM rb vb _) =>
        (ASeq (AAssign (ARegStackInt width r1 ra))
          (AOp (IOpConst width iop r1 rb)),
         regM r1 (getIRegIndex r1) eq_refl)

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
        (ASeq (AAssign (ARegStackInt width r1 r)) (AOp (OpRot width qop r1 n)),
         regM r1 (getIRegIndex r1) eq_refl)
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
             (avoid: list Mapping)
             (ret: nat):
        option (AlmostQhasm.Program * list nat) :=

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
        (ASkip, [constM (iconst c) (getIConstValue (iconst c)) eq_refl])

      | PBin n o a b =>
        let ret' := (ret + 1) mod activeRegisters in
        let tmp0 := freshMapping (avoid ++ mapping) n in
        let tmp1 := freshMapping (avoid ++ mapping ++ tmp0) m in

        otup_map (convertProgram' a mapping avoid ret) (fun aprog amap =>
          otup_map (convertProgram' b mapping avoid ret') (fun bprog bmap =>
            let m0 := moveMapping mapping tmp0 in
            let m1 := moveMapping bmap tmp1 in

            match (amap, bmap) with
            | ([av], [bv]) =>
              let oper := binProg m o av bv r1 in
              Some (ASeq m0 (ASeq bprog (ASeq m1 (ASeq aprog oper))), amap)

            | _ => None
            end))

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
