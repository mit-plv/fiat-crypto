
Require Export Language Conversion QhasmEvalCommon QhasmUtil.
Require Export Pseudo Medial AlmostQhasm State.
Require Export Bedrock.Word NArith NPeano.
Require Export List Sumbool.
Require Import FMapAVL FMapList JMeq.
Require Import Vector.

Module PseudoMedialConversion (Arch: PseudoMachine).
  Import QhasmCommon AlmostQhasm EvalUtil Util.
  Import ListNotations.

  Module P := Pseudo Arch.
  Module M := Medial Arch.

  (******************    Material Conversions    ************************)

  Module PseudoConversion <: Conversion P M.
    Import P M Arch StateCommon.

    Fixpoint convertState (st: M.State): option P.State :=
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
      end.

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

    (* Results are in the locations described by the
       returned list. start is the next known open address *)
    Fixpoint convertProgram' {n m} (prog: Pseudo n m) (start: nat):
        option (Medial * (list nat)) :=

      match prog with
      | PVar n i => Some (MSkip, [start])
      | PConst n c => Some (MAssign (MAConst start c), [start])
      | PMem n m v i => Some (MAssign (MAMem start v i), [start])

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
        | ((lp, lr), (rp, rr)) => Some (MCond (MC o i0 i1) lp rp, lr)
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
     let defs := (fix allDefs {n m} (prog: Pseudo n m): TripleM.t M.Program :=
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
        end) prog in

     let foldF := fun (t: (nat * nat * nat) * M.Program) (p: M.Program) =>
       match t with
       | ((n', m', lbl), p') => MDef lbl p' p
       end in

     option_map (fold_left _ _ foldF (TripleM.elements defs)) (convertProgram' prog _ _ vars).

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
