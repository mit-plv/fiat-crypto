
Require Export Language Conversion QhasmCommon QhasmUtil.
Require Export Pseudo Medial AlmostQhasm State.
Require Export Bedrock.Word NArith NPeano.
Require Export List Sumbool.
Require Vector.

Module PseudoMedialConversion (Arch: PseudoMachine).
  Import QhasmCommon AlmostQhasm State Util.
  Import ListNotations.

  Module P := Pseudo Arch.
  Module M := Medial Arch.

  Inductive Mapping (n: nat) :=
    | regM: forall (r: IReg n) (v: nat), v = getIRegIndex r -> Mapping n
    | stackM: forall (r: Stack n) (v: nat), v = getStackIndex r -> Mapping n
    | constM: forall (r: IConst n) (v: nat), v = getIConstValue r -> Mapping n.

  Definition wordToM {n: nat} {spec: ISize n} (w: word n): Mapping n.
    destruct spec; first [
      refine (@constM 32 (constInt32 w) (wordToNat w) _)
    | refine (@constM 64 (constInt64 w) (wordToNat w) _)];
      abstract intuition.
  Defined.

  Definition regToM {n: nat} {spec: ISize n} (r: IReg n): Mapping n.
    destruct spec; refine (@regM _ r (getIRegIndex r) _); abstract intuition.
  Defined.

  Definition stackToM {n: nat} {spec: ISize n} (s: Stack n): Mapping n.
    destruct spec; refine (@stackM _ s (getStackIndex s) _); abstract intuition.
  Defined.

  Definition constToM {n: nat} {spec: ISize n} (c: IConst n): Mapping n.
    destruct spec; refine (@constM _ c (getIConstValue c) _); abstract intuition.
  Defined.

  Definition mapping_dec {n} (a b: Mapping n): {a = b} + {a <> b}.
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

  Definition dec_lt (a b: nat): {(a < b)%nat} + {(a >= b)%nat}.
    assert ({(a <? b)%nat = true} + {(a <? b)%nat <> true})
      by abstract (destruct (a <? b)%nat; intuition);
      destruct H.

    - left; abstract (apply Nat.ltb_lt in e; intuition).

    - right; abstract (rewrite Nat.ltb_lt in n; intuition).
  Defined.

  Fixpoint usedStackEntries {n} (lst: list (Mapping n)): list nat :=
    match lst with
    | nil => []
    | cons c cs =>
      match c with
      | stackM _ v _ => cons v (usedStackEntries cs)
      | _ => usedStackEntries cs
      end
    end.

  (******************    Material Conversions    ************************)

  Module PseudoConversion <: Conversion P M.
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

    Definition convertProgram (prog: Pseudo vars vars): option M.Program :=
      let m := range O vars in
      option_map (@fst Medial nat) (convertProgram' prog m m vars).

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      M.evaluatesTo prog' a b <-> P.evaluatesTo prog a' b'.
    Admitted.

  End PseudoConversion.

  Module MedialConversion <: Conversion M AlmostQhasm.

    Import Arch M.

    Definition width_dec : {width = 32} + {width = 64}.
      destruct width_spec; first [
        left; abstract intuition
        | right; abstract intuition].
    Defined.

    Definition ireg (x: nat): IReg width :=
      match width_spec with
      | I32 => regInt32 x
      | I64 => regInt64 x
      end.

    Definition iconst (x: word width): IConst width.
      refine (
        if width_dec
        then (convert constInt32 _) x
        else (convert constInt64 _) x);
        abstract (rewrite _H; intuition).
    Defined.

    Definition stack (x: nat): Stack width :=
      match width_spec with
      | I32 => stack32 x
      | I64 => stack64 (2 * x)
      end.

    Fixpoint convertState (st: AlmostQhasm.State): option M.State :=
      let try_cons := fun (k: nat) (x: option N) (m: DefMap) =>
        match x with | Some x' => NatM.add k x' m | _ => m end in

      let get (n: nat): option N :=
        match (getIntReg (ireg n) st, getStack (stack n) st) with
        | (Some v, _) => Some (wordToN v)
        | (_, Some v) => Some (wordToN v)
        | _ => None
        end in

      Some (
        (fix cs' (n: nat) :=
         try_cons n (get n)
           (match n with | O => NatM.empty N | S m => cs' m end))
         vars).

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
          | (regM rx _ _, regM ry _ _) =>
            Some (AAssign (ARegRegInt _ rx ry))
          | (stackM sx _ _, regM ry _ _) =>
            Some (AAssign (AStackRegInt _ sx ry))
          | (regM rx _ _, stackM sy _ _) =>
            Some (AAssign (ARegStackInt _ rx sy))
          | (regM rx _ _, constM cy _ _) =>
            Some (AAssign (AConstInt _ rx cy))
          | _ => None
          end

        | MAConst x c =>
          match (mapF x) with
          | (regM rx _ _) =>
            Some (AAssign (AConstInt _ rx (iconst c)))
          | _ => None
          end
        end

      | MOp o =>
        match o with
        | MIOpConst io a c =>
          match (mapF a) with
          | (regM ra _ _) =>
            Some (AOp (IOpConst _ io ra (iconst c)))
          | _ => None
          end

        | MIOpReg io a b =>
          match (mapF a, mapF b) with
          | (regM ra _ _, regM rb _ _) =>
            Some (AOp (IOpReg _ io ra rb))
          | _ => None
          end

        | MDOpReg duo a b (Some x) =>
          match (mapF a, mapF b, mapF x) with
          | (regM ra _ _, regM rb _ _, regM rx _ _) =>
            Some (AOp (DOpReg _ duo ra rb (Some rx)))
          | _ => None
          end

        | MDOpReg duo a b None =>
          match (mapF a, mapF b) with
          | (regM ra _ _, regM rb _ _) =>
            Some (AOp (DOpReg _ duo ra rb None))
          | _ => None
          end

        | MOpRot ro a c =>
          match (mapF a) with
          | (regM ra _ _) =>
            Some (AOp (OpRot _ ro ra c))
          | _ => None
          end
        end

      | MCond (MC to i0 i1) a b =>
        let c := (fun x => convertProgram' x mapF nextFree tmp) in

        omap (c a) (fun aprog => omap (c b) (fun bprog =>
          match (mapF i0, mapF i1) with
          | (regM r0 _ _, regM r1 _ _) =>
            Some (ACond (TestInt _ to r0 r1) aprog bprog)
          | _ => None
          end))

      | MFunexp e a =>
        let c := (fun x => convertProgram' x mapF (S nextFree) tmp) in
        omap (c a) (fun aprog =>
          match (mapF nextFree, mapF tmp) with
          | (regM rf _ _, regM rt _ _) =>

            Some (ASeq (ASeq
              (AAssign (AConstInt _ rf (iconst (natToWord _ O))))
              (AAssign (AConstInt _ rt (iconst (natToWord _ e)))))
              (AWhile (TestInt _ TLt rf rt)
                (ASeq aprog (ASeq 
                (AOp (IOpConst _ IPlus rf (iconst (natToWord _ 1))))
                (AAssign (AConstInt _ rt (iconst (natToWord _ e))))))))
          | _ => None
          end)
      end.

    (* TODO (rsloan): make these into parameters *)
    Definition convertProgram (prog: M.Program): option AlmostQhasm.Program :=
      convertProgram' prog (fun x => @regToM width width_spec (ireg x)) 100 100.

    Lemma convert_spec:  forall a a' b b' prog prog',
      convertProgram prog = Some prog' ->
      convertState a = Some a' -> convertState b = Some b' ->
      AlmostQhasm.evaluatesTo prog' a b <-> M.evaluatesTo prog a' b'.
    Admitted.

  End MedialConversion.
End PseudoMedialConversion.
