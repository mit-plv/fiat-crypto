Require Export Language Conversion QhasmCommon QhasmEvalCommon QhasmUtil.
Require Export Pseudo AlmostQhasm State.
Require Import Bedrock.Word NArith NPeano Euclid.
Require Import List Sumbool Vector.

Module PseudoConversion <: Conversion Pseudo AlmostQhasm.
  Import AlmostQhasm EvalUtil ListState Pseudo ListNotations.

  Section Conv.
    Variable w: nat.
    Variable s: Width w.

    Definition MMap := NatM.t (Mapping w).
    Definition mempty := NatM.empty (Mapping w).

    Definition FMap := NatM.t (AlmostProgram * (list (Mapping w))).
    Definition fempty := NatM.empty (AlmostProgram * (list (Mapping w))).

    Transparent MMap FMap.

    Definition getStart {n m} (prog: @Pseudo w s n m) :=
      let ns := (fix getStart' {n' m'} (prog': @Pseudo w s n' m') :=
        match prog' with
        | PVar _ _ i => [proj1_sig i]
        | PBin _ _ p => getStart' p
        | PDual _ _ p => getStart' p
        | PCarry _ _ p => getStart' p
        | PShift _ _ _ p => getStart' p
        | PFunExp _ p _ => getStart' p
        | PCall _ _ _ p => getStart' p
        | PIf _ _ _ _ _ l r => (getStart' l) ++ (getStart' r)
        | PLet _ k _ a b => (n + k) :: (getStart' a) ++ (getStart' b)
        | PCons _ _ a b => (getStart' a) ++ (getStart' b)
        | _ => []
        end) _ _ prog in

      (fix maxN (lst: list nat) :=
        match lst with
        | [] => O
        | x :: xs => max x (maxN xs)
        end) (n :: m :: ns).

    Definition addMap {T} (a b: (NatM.t T)) : NatM.t T :=
      (fix add' (m: NatM.t T) (elts: list (nat * T)%type) :=
        match elts with
        | [] => m
        | (k, v) :: elts' => add' (NatM.add k v m) elts'
        end) a (NatM.elements b).

    Fixpoint convertProgram' {n m} (prog: @Pseudo w s n m) (start: nat) (M: MMap) (F: FMap) :
        option (AlmostProgram * (list (Mapping w)) * MMap * FMap) :=

      let rM := fun (x: nat) => regM _ (reg s x) in
      let sM := fun (x: nat) => stackM _ (stack s x) in
      let reg' := reg s in
      let stack' := stack s in
      let const' := constant s in

      let get := fun (k: nat) (default: nat -> Mapping w) (M': MMap) =>
        match (NatM.find k M') with
        | Some v => v
        | _ => default k
        end in

      let madd := fun (a: nat) (default: nat -> Mapping w) (M': MMap) =>
        NatM.add a (get a default M') M' in

      let fadd := fun (k: nat) (f: AlmostProgram) (r: list (Mapping w)) =>
        NatM.add k (f, r) in

      let updateM := (
        fix updateM' (k: nat) (mtmp: list (Mapping w)) (Miter: MMap) : MMap :=
        match mtmp with
        | [] => Miter
        | a :: mtmp' => NatM.add k a (updateM' (S k) mtmp' Miter)
        end) in

      match prog with
      | PVar n (Some true) i =>
        Some (ASkip, [get i rM M], madd i rM M, F)

      | PVar n (Some false) i =>
        Some (ASkip, [get i sM M], madd i sM M, F)

      | PVar n None i => (* assign to register by default *)
        Some (ASkip, [get i rM M], madd i rM M, F) 

      | PConst n c =>
        Some (AAssign (AConstInt (reg' start) (const' c)),
              [get start rM M], madd start rM M, F)

      | PMem n m v i =>
        Some (AAssign (ARegMem (reg' start) (mem s v) i),
              [get start rM M], madd start rM M, F)

      | PBin n o p =>
        match (convertProgram' p start M F) with
        | Some (p', [regM (reg _ _ a); regM (reg _ _ b)], M', F') =>
            Some (ASeq p' (AOp (IOpReg o (reg' a) (reg' b))),
                [get a rM M'], madd a rM (madd b rM M'), F')

        | Some (p', [regM (reg _ _ a); constM c], M', F') =>
            Some (ASeq p' (AOp (IOpConst o (reg' a) c)),
                [get a rM M'], madd a rM M', F')

        | Some (p', [regM (reg _ _ a); memM _ b i], M', F') =>
            Some (ASeq p' (AOp (IOpMem o (reg' a) b i)),
                [get a rM M'], madd a rM M', F')

        | Some (p', [regM (reg _ _ a); stackM (stack _ _ b)], M', F') =>
            Some (ASeq p' (AOp (IOpStack o (reg' a) (stack' b))),
                [get a rM M'], madd a rM (madd b sM M'), F')

        | _ => None
        end

      | PCarry n o p =>
        match (convertProgram' p start M F) with
        | Some (p', [regM (reg _ _ a); regM (reg _ _ b)], M', F') =>
            Some (ASeq p' (AOp (COp o (reg' a) (reg' b))),
                [get a rM M'], madd a rM (madd b rM M'), F')

        | _ => None
        end

      | PDual n o p =>
        match (convertProgram' p (S start) M F) with
        | Some (p', [regM (reg _ _ a); regM (reg _ _ b)], M', F') =>
            Some (ASeq p' (AOp (DOp o (reg' a) (reg' b) (Some (reg' start)))),
                  [get a rM M'; get start rM M'],
                  madd a rM (madd b rM (madd start rM M')), F')

        | _ => None
        end

      | PShift n o x p =>
        match (convertProgram' p start M F) with
        | Some (p', [regM (reg _ _ a)], M', F') =>
            Some (ASeq p' (AOp (ROp o (reg' a) x)),
                [get a rM M'], madd a rM M', F')

        | _ => None
        end

      | PLet n k m f g =>
        match (convertProgram' f start M F) with
        | None => None
        | Some (fp, fm, M', F') =>

          (* Make sure all of the new variables are bound to their results *)
          let M'' := updateM start fm M' in

          (* Then convert the second program *)
          match (convertProgram' g (start + (length fm)) M'' F') with
          | None => None
          | Some (gp, gm, M''', F'') => Some (ASeq fp gp, gm, M''', F'')
          end
        end

      | PCons n m f g => 
        match (convertProgram' f start M F) with
        | None => None
        | Some (fp, fm, M', F') =>
            match (convertProgram' g (start + (length fm)) M' F') with
            | None => None
            | Some (gp, gm, M'', F'') => Some (ASeq fp gp, fm ++ gm, M'', F'')
            end
        end

      | PIf n m o i0 i1 l r => 
        match (convertProgram' l start M F) with
        | None => None
        | Some (lp, lr, lM, lF) =>

            match (convertProgram' r start lM lF) with
            | None => None
            | Some (rp, rr, M', F') =>

            if (list_eq_dec mapping_dec lr rr)
            then
                match (get (proj1_sig i0) rM M, get (proj1_sig i1) rM M) with
                | (regM r0, regM r1) => Some (ACond (CReg _ o r0 r1) lp rp, lr, M', F')
                | (regM r, constM c) => Some (ACond (CConst _ o r c) lp rp, lr, M', F')
                | _ => None
                end
            else None
            end
        end

      | PFunExp n f e => 
        match (convertProgram' f (S start) M F) with
        | Some (fp, fr, M', F') => 
            let a := start in
            Some (ASeq
            (AAssign (AConstInt (reg' a) (const' (natToWord _ O))))
            (AWhile (CConst _ TLt (reg' a) (const' (natToWord _ e)))
                (ASeq fp (AOp (IOpConst IAdd (reg' a) (const' (natToWord _ 1)))))),
            fr, madd a rM M', F')

        | _ => None
        end

      | PCall n m lbl f =>
        match (convertProgram' f start M F) with
        | Some (fp, fr, M', F') =>
            let F'' := NatM.add lbl (fp, fr) F' in
            Some (ACall lbl, fr, M', F'')
        | None => None
      end
    end.

  End Conv.

  Definition convertProgram x y (prog: Program x) : option (AlmostQhasm.Program y) := 
    let vs := max (inputs x) (outputs x) in
    let M0 := mempty (width x) in
    let F0 := fempty (width x) in

    match (convertProgram' (width x) (spec x) prog vs M0 F0) with
    | Some (prog', _, M, F) =>
      Some (fold_left
           (fun p0 t => match t with | (k, (v, _)) => ADef k v p0 end)
           prog'
           (of_list (NatM.elements F)))
    | _ => None
    end.

  Fixpoint convertState x y (st: AlmostQhasm.State y) : option (State x) :=
    let vars := max (inputs x) (outputs x) in

    let try_cons := fun {T} (x: option T) (l: list T) =>
      match x with | Some x' => x' :: l | _ => l end in

    let get := fun i =>
      match (FullState.getReg (reg (spec x) i) st,
             FullState.getStack (stack (spec x) i) st) with
      | (Some v, _) => Some v
      | (_, Some v) => Some v
      | _ => None
      end in

    let varList := (fix cs' (n: nat) :=
      try_cons (get (vars - n)) (match n with | O => [] | S m => cs' m end)) vars in

    match st with
    | FullState.fullState _ _ memState _ carry =>
      if (Nat.eq_dec (length varList) vars)
      then Some (varList, memState, carry)
      else None
    end.

  Lemma convert_spec: forall pa pb a a' b b' prog prog',
    convertProgram pa pb prog = Some prog' ->
    convertState pa pb a = Some a' ->
    convertState pa pb b = Some b' ->
    evaluatesTo pa prog a' b' ->
    AlmostQhasm.evaluatesTo pb prog' a b.
  Admitted.
End PseudoConversion.
