
Require Export Language Conversion QhasmEvalCommon QhasmUtil.
Require Export Pseudo AlmostQhasm State.
Require Export Bedrock.Word NArith NPeano Euclid.
Require Export List Sumbool Vector.

Module PseudoConversion (Arch: PseudoMachine).
  Import QhasmCommon AlmostQhasm EvalUtil Util.
  Import ListNotations.

  Module P := Pseudo Arch.
  (* Module M := Medial Arch. *)

  (******************    Material Conversions    ************************)

  Module PseudoConversion <: Conversion P AlmostQhasm.
    Import P (* M *) Arch StateCommon.

    (* Fixpoint convertState (st: M.State): option P.State :=
      let try_cons := fun {T} (x: option T) (l: list T) =>
        match x with | Some x' => x' :: l | _ => l end in

      match st with
      | (v, m, c) =>
        let varList := (fix cs' (n: nat) :=
          try_cons (option_map (NToWord width) (NatM.find n v))
            (match n with | O => [] | S m => cs' m end)) vars in

        if (Nat.eq_dec (length varList) vars)
        then Some (varList, m, c)
        else None
      end. *)

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
          | (a, b) => (l :: a, b)
          end
        end
      end.

    Fixpoint maxN (lst: list nat): nat :=
      match lst with
      | x :: xs => max x (maxN xs)
      | [] => O
      end.

    Definition MMap := NatM.t (Mapping width).
    Definition mempty := NatM.empty (Mapping width).

    Fixpoint convertProgram' {n m} (prog: Pseudo n m) (start: nat) (M: MMap):
        option (AlmostProgram * (list (Mapping width)) * MMap) :=
      let rM := fun (x: nat) => regM _ (reg width_spec x) in
      let sM := fun (x: nat) => stackM _ (stack width_spec x) in

      let g := fun (k: nat) =>
        match (NatM.find k M) with
        | Some v => v
        | _ => rM k (* TODO: more intelligent defaults *)
        end in

      let madd := fun (k: nat) (f: nat -> Mapping width) => NatM.add k (f k) M in

      match prog with
      | PVar n (Some true) i => Some (ASkip, [rM i], madd i rM)
      | PVar n (Some false) i => Some (ASkip, [sM i], madd i sM)
      | PVar n None i => Some (ASkip, [g i], M) 
      | PConst n c => Some (AAssign (AConstInt (rM start) c), [rM start], madd start rM)
      | PMem n m v i => Some (AAssign (ARegMem (rM start) v i), madd start rM)
      | _ => None
      end.


      | PBin n o p =>
        match (convertProgram' p start) with
        | Some (p', [a; b]) =>
          Some (MSeq p' (MOp (MIOpReg o a b)), [a])
        | _ => None
        end

      | PCarry n o p =>
        match (convertProgram' p start) with
        | Some (p', [a; b]) =>
          Some (MSeq p' (MOp (MCOpReg o a b)), [a])
        | _ => None
        end

      | PDual n o p =>
        match (convertProgram' p start) with
        | Some (p', [a; b]) =>
          let nextOpen := S (maxN [a; b]) in
          Some (MSeq p' (MOp (MDOpReg o a b (Some nextOpen))), [a; nextOpen])
        | _ => None
        end

      | PShift n o a x =>
        match (convertProgram' x start) with
        | Some (p', [r]) =>
          Some (MSeq p' (MOp (MOpRot o r a)), [proj1_sig a])
        | _ => None
        end

      | PLet n k m f g =>
        ft <- convertProgram' f (start + k);
        gt <- convertProgram' g (S (maxN (snd ft)));

        match (ft, gt) with
        | ((fp, fr), (gp, gr)) => Some (MSeq fp gp, gr)
        end

      | PComb n a b f g => 
        ft <- convertProgram' f start;
        gt <- convertProgram' g (S (maxN (snd ft)));
        match (ft, gt) with
        | ((fp, fr), (gp, gr)) => Some (MSeq fp gp, fr ++ gr)
        end

      | PIf n m o i0 i1 l r => 
        lt <- convertProgram' l start;
        rt <- convertProgram' r start;
        match (lt, rt) with
        | ((lp, lr), (rp, rr)) => Some (MCond (MCReg o i0 i1) lp rp, lr)
        end
        (* TODO: prove that all (Pseudo n m) will return the same list *)

      | PFunExp n f e => 
        match (convertProgram' f start) with
        | Some (fp, fr) => Some (MFunexp e fp, fr)
        | _ => None
        end
 
      | PCall n m lbl _ => Some (MCall lbl, range n m)
      end.

    (* Results are in the locations described by the
       returned list. start is the next known open address *)
    Fixpoint convertProgram' {n m} (prog: Pseudo n m) (start: nat):
        option (Medial * (list nat)) :=

      match prog with
      | PVar n i => Some (MSkip, [start])
      | PConst n c => Some (MAssign (MAConst start c), [start])
      | PMem n m v i => Some (MAssign (MAMem _ start v i), [start])

      | PBin n o p =>
        match (convertProgram' p start) with
        | Some (p', [a; b]) =>
          Some (MSeq p' (MOp (MIOpReg o a b)), [a])
        | _ => None
        end

      | PCarry n o p =>
        match (convertProgram' p start) with
        | Some (p', [a; b]) =>
          Some (MSeq p' (MOp (MCOpReg o a b)), [a])
        | _ => None
        end

      | PDual n o p =>
        match (convertProgram' p start) with
        | Some (p', [a; b]) =>
          let nextOpen := S (maxN [a; b]) in
          Some (MSeq p' (MOp (MDOpReg o a b (Some nextOpen))), [a; nextOpen])
        | _ => None
        end

      | PShift n o a x =>
        match (convertProgram' x start) with
        | Some (p', [r]) =>
          Some (MSeq p' (MOp (MOpRot o r a)), [proj1_sig a])
        | _ => None
        end

      | PLet n k m f g =>
        ft <- convertProgram' f (start + k);
        gt <- convertProgram' g (S (maxN (snd ft)));

        match (ft, gt) with
        | ((fp, fr), (gp, gr)) => Some (MSeq fp gp, gr)
        end

      | PComb n a b f g => 
        ft <- convertProgram' f start;
        gt <- convertProgram' g (S (maxN (snd ft)));
        match (ft, gt) with
        | ((fp, fr), (gp, gr)) => Some (MSeq fp gp, fr ++ gr)
        end

      | PIf n m o i0 i1 l r => 
        lt <- convertProgram' l start;
        rt <- convertProgram' r start;
        match (lt, rt) with
        | ((lp, lr), (rp, rr)) => Some (MCond (MCReg o i0 i1) lp rp, lr)
        end
        (* TODO: prove that all (Pseudo n m) will return the same list *)

      | PFunExp n f e => 
        match (convertProgram' f start) with
        | Some (fp, fr) => Some (MFunexp e fp, fr)
        | _ => None
        end
 
      | PCall n m lbl _ => Some (MCall lbl, range n m)
      end.

    Definition addFunMap {T} (a b: TripleM.t T): TripleM.t T :=
      (fix add' (m: TripleM.t T) (elts: list ((nat * nat * nat) * T)%type) :=
        match elts with
        | [] => m
        | (k, v) :: elts' => add' (TripleM.add k v m) elts'
        end) a (TripleM.elements b).

    Definition convertProgram (prog: Pseudo vars vars): option M.Program :=
      let defs: TripleM.t M.Program :=
        (fix allDefs {n m: nat} (prog: Pseudo n m): TripleM.t M.Program :=
          match prog with
          | PBin n o p => allDefs p
          | PCarry n o p => allDefs p
          | PDual n o p => allDefs p
          | PShift n o a x => allDefs x
          | PLet n k m f g => addFunMap (allDefs f) (allDefs g)
          | PComb n a b f g => addFunMap (allDefs f) (allDefs g)
          | PIf n m t i0 i1 l r => addFunMap (allDefs l) (allDefs r)
          | PFunExp n p e => allDefs p
          | PCall n m l p =>
            match (convertProgram' p n) with
            | Some (mp, _) => TripleM.add (n, m, l) mp (allDefs p)
            | _ => allDefs p
            end
          | _ => TripleM.empty M.Program
          end) _ _ prog in

     let foldF := fun (p: M.Program) (t: (nat * nat * nat) * M.Program) =>
       match t with
       | ((n', m', lbl), p') => MDef lbl p' p
       end in

     let f: M.Program -> option M.Program := fun x =>
       Some (fold_left foldF x (of_list (TripleM.elements defs))) in

     match (convertProgram' prog vars) with
     | Some (p', _) => f p'
     | _ => None
     end.

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      M.evaluatesTo prog' a b <-> P.evaluatesTo prog a' b'.
    Admitted.

  End PseudoConversion.

  Module MedialConversion <: Conversion M AlmostQhasm.
    Import Arch M FullState.

    Definition ireg (x: nat): Reg width := reg width_spec x.
    Definition iconst (x: word width): Const width := const width_spec x.
    Definition istack (x: nat): Stack width := stack width_spec x.

    Definition tmpMap: nat -> Mapping width := (fun x => regM width (ireg x)).

    Definition getMapping (m: Mapping width) (st: AlmostQhasm.State): option (word width) :=
      match m with
      | regM r => getReg r st
      | stackM s => getStack s st
      | _ => None
      end.

    Definition convertState' (mapF: nat -> Mapping width) (st: AlmostQhasm.State): option M.State :=
      let tryAddVar := fun (k: nat) (x: option (word width)) (st: M.State) =>
        match x with | Some x' => MedState.setVar k x' st | _ => st end in

      Some ((fix cs' (n: nat) :=
           tryAddVar n (getMapping (mapF n) st)
           (match n with | O => MedState.emptyState | S m => cs' m end))
         vars).

    Definition convertState (st: AlmostQhasm.State): option M.State :=
      convertState' tmpMap st.

    Fixpoint convertProgram'
             (prog: M.Program)
             (mapF: nat -> Mapping width)
             (nextFree tmp: nat):
        option AlmostQhasm.Program :=

      let omap := fun {A B} (x: option A) (f: A -> option B) =>
        match x with | Some y => f y | _ => None end in

      match prog with
      | MSkip => Some ASkip

      | MSeq a b =>
        omap (convertProgram' a mapF nextFree tmp) (fun aprog =>
          omap (convertProgram' b mapF nextFree tmp) (fun bprog =>
            Some (ASeq aprog bprog)))

      | MAssign a =>
        match a with
        | MAVar x y => 
          match (mapF x, mapF y) with
          | (regM rx, regM ry) =>
            Some (AAssign (ARegReg rx ry))
          | (stackM sx, regM ry) =>
            Some (AAssign (AStackReg sx ry))
          | (regM rx, stackM sy) =>
            Some (AAssign (ARegStack rx sy))
          | (regM rx, constM cy) =>
            Some (AAssign (AConstInt rx cy))
          | _ => None
          end

        | MAConst x c =>
          match (mapF x) with
          | (regM rx) => Some (AAssign (AConstInt rx (iconst c)))
          | _ => None
          end

        | MAMem m x v i =>
          match (mapF x) with
          | (regM rx) => Some (AAssign (ARegMem rx (@mem _ m width_spec v) i))
          | _ => None
          end
        end

      | MOp o =>
        match o with
        | MIOpConst io a c =>
          match (mapF a) with
          | (regM ra) =>
            Some (AOp (IOpConst io ra (iconst c)))
          | _ => None
          end

        | MIOpReg io a b =>
          match (mapF a, mapF b) with
          | (regM ra, regM rb) =>
            Some (AOp (IOpReg io ra rb))
          | _ => None
          end

        | MCOpReg co a b =>
          match (mapF a, mapF b) with
          | (regM ra, regM rb) =>
            Some (AOp (COp co ra rb))
          | _ => None
          end

        | MDOpReg duo a b (Some x) =>
          match (mapF a, mapF b, mapF x) with
          | (regM ra, regM rb, regM rx) =>
            Some (AOp (DOp duo ra rb (Some rx)))
          | _ => None
          end

        | MDOpReg duo a b None =>
          match (mapF a, mapF b) with
          | (regM ra, regM rb) =>
            Some (AOp (DOp duo ra rb None))
          | _ => None
          end

        | MOpRot ro a c =>
          match (mapF a) with
          | (regM ra) =>
            Some (AOp (ROp ro ra c))
          | _ => None
          end
        end

      | MCond c a b =>

        let conv := (fun x => convertProgram' x mapF nextFree tmp) in

        omap (conv a) (fun aprog => omap (conv b) (fun bprog =>
          match c with
          | MCReg t x y =>
            match (mapF x, mapF y) with
            | (regM r0, regM r1) =>
              Some (ACond (CReg _ t r0 r1) aprog bprog)
            | _ => None
            end

          | MCConst t x y =>
            match (mapF x) with
            | (regM r) =>
              Some (ACond (CConst _ t r (iconst y)) aprog bprog)
            | _ => None
            end

          | MZ x =>
            match (mapF x) with
            | (regM r) =>
              Some (ACond (CZero _ r) aprog bprog)
            | _ => None
            end
          end))

      | MFunexp e a =>
        let conv := (fun x => convertProgram' x mapF (S nextFree) tmp) in
        omap (conv a) (fun aprog =>
          match (mapF nextFree, mapF tmp) with
          | (regM rf, regM rt) =>

            Some (ASeq (ASeq
              (AAssign (AConstInt rf (iconst (natToWord _ O))))
              (AAssign (AConstInt rt (iconst (natToWord _ e)))))
              (AWhile (CReg _ TLt rf rt)
                (ASeq aprog (ASeq 
                (AOp (IOpConst Add rf (iconst (natToWord _ 1))))
                (AAssign (AConstInt rt (iconst (natToWord _ e))))))))
          | _ => None
          end)

      | MDef lbl f a =>
        omap (convertProgram' f mapF nextFree tmp) (fun fprog =>
          omap (convertProgram' a mapF (S nextFree) tmp) (fun aprog =>
            Some (ADef lbl fprog aprog)))
      | MCall lbl => Some (ACall lbl)
      end.

    (* TODO (rsloan): make these into parameters *)
    Definition convertProgram (prog: M.Program): option AlmostQhasm.Program :=
      convertProgram' prog tmpMap 100 100.

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      AlmostQhasm.evaluatesTo prog' a b <-> M.evaluatesTo prog a' b'.
    Admitted.

  End MedialConversion.
End PseudoMedialConversion.
