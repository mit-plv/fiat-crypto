Require Import QhasmEvalCommon Pseudo.
Require Import Language.
Require Import List.

Module Medial (M: PseudoMachine) <: Language.
  Import ListNotations.
  Import State.
  Import M.

  Definition W := word width.

  (* Program Types *)
  Definition State := (NatNMap * PairNMap * (option bool))%type.

  Definition varS (st: State) := fst (fst st).
  Definition memS (st: State) := snd (fst st).
  Definition carryS (st: State) := snd st.

  Definition var (i: nat) (st: State) := NatM.find i (varS st).
  Definition mem (v i: nat) (st: State) := PairM.find (v, i) (memS st).

  Inductive MAssignment : Type :=
    | MAVar: nat -> nat -> MAssignment 
    | MAMem: nat -> nat -> nat -> MAssignment 
    | MAConst: nat -> W -> MAssignment.

  Inductive MOperation :=
    | MIOpConst: IntOp -> nat -> W -> MOperation
    | MIOpReg: IntOp -> nat -> nat -> MOperation
    | MCOpReg: CarryOp -> nat -> nat -> MOperation
    | MDOpReg: DualOp -> nat -> nat -> option nat -> MOperation
    | MOpRot: RotOp -> nat -> Index width -> MOperation.

  Inductive MConditional :=
    | MC: TestOp -> nat -> nat -> MConditional.

  Inductive Medial: Set :=
    | MSkip: Medial
    | MSeq: Medial -> Medial -> Medial
    | MAssign: MAssignment -> Medial
    | MOp: MOperation -> Medial
    | MCond: MConditional -> Medial -> Medial -> Medial
    | MFunexp: nat -> Medial -> Medial
    | MDef: nat -> Medial -> Medial -> Medial
    | MCall: nat -> Medial.

  Definition Program := Medial.

  Fixpoint inline (l: nat) (f p: Medial) :=
    match p with
    | MSeq a b => MSeq (inline l f a) (inline l f b)
    | MCond c a b => MCond c (inline l f a) (inline l f b)
    | MFunexp e a => MFunexp e (inline l f a)
    | MDef l' f' p' =>
      if (Nat.eq_dec l l')
      then p
      else MDef l' (inline l f f') (inline l f p')
    | MCall l' =>
      if (Nat.eq_dec l l')
      then f
      else p
    | _ => p
    end.

  Fixpoint inlineAll (p: Medial) :=
    match p with
    | MSeq a b => MSeq (inlineAll a) (inlineAll b)
    | MCond c a b => MCond c (inlineAll a) (inlineAll b)
    | MFunexp e a => MFunexp e (inlineAll a)
    | MDef l' f' p' => inline l' f' (inlineAll p')
    | _ => p
    end.

  Fixpoint meval (m: Medial) (st: State): option State :=
    let omap := fun {A B} (x: option A) (f: A -> option B) =>
      match x with | Some y => f y | _ => None end in

    match m with
    | MSkip => Some st

    | MSeq a b => omap (meval a st) (fun s => meval b s)

    | MAssign a =>
      match a with
      | MAVar x y =>
        match (var y st) with
        | Some v => Some (NatM.add x v (varS st), memS st, carryS st)
        | _ => None
        end

      | MAMem x y i =>
        match (mem y i st) with
        | Some v => Some (NatM.add x v (varS st), memS st, carryS st)
        | _ => None
        end

      | MAConst x c => Some (NatM.add x (wordToN c) (varS st), memS st, carryS st)
      end

    | MOp o =>
      match o with
      | MIOpConst io a c =>
        omap (var a st) (fun v =>
          let (res, c') := evalIntOp io (NToWord _ v) c in
          Some (NatM.add a (wordToN res) (varS st), memS st, c'))

      | MIOpReg io a b =>
        omap (var a st) (fun va =>
          omap (var b st) (fun vb =>
            let (res, c') := evalIntOp io (NToWord width va) (NToWord width vb) in
            Some (NatM.add a (wordToN res) (varS st), memS st, c')))

      | MCOpReg o a b =>
        omap (var a st) (fun va =>
          omap (var b st) (fun vb =>
            let c := match (carryS st) with | Some b => b | _ => false end in
            let (res, c') := evalCarryOp o (NToWord width va) (NToWord width vb) c in
            Some (NatM.add a (wordToN res) (varS st), memS st, Some c')))

      | MDOpReg duo a b (Some x) =>
        omap (var a st) (fun va =>
          omap (var b st) (fun vb =>
            let res := evalDualOp duo (NToWord width va) (NToWord width vb) in
            Some (NatM.add a (wordToN (fst res))
                   (NatM.add x (wordToN (snd res)) (varS st)), memS st, carryS st)))

      | MDOpReg duo a b None =>
        omap (var a st) (fun va =>
          omap (var b st) (fun vb =>
            let res := evalDualOp duo (NToWord width va) (NToWord width vb) in
            Some (NatM.add a (wordToN (fst res)) (varS st), memS st, carryS st)))

      | MOpRot ro a x =>
        omap (var a st) (fun v =>
          let res := evalRotOp ro (NToWord width v) (proj1_sig x) in
          Some (NatM.add a (wordToN res) (varS st), memS st, carryS st))
      end

    | MCond c a b =>
      match c with
      | MC t x y =>
        omap (var x st) (fun vx =>
          omap (var y st) (fun vy =>
            if (evalTest t (NToWord width vx) (NToWord width vy))
            then meval a st
            else meval b st))
      end

    | MFunexp n a =>
      (fix fexp (m: nat) (f: State -> option State) (s: State) :=
        match m with
        | O => Some s
        | S m' =>
          match f s with
          | None => None
          | Some s' => fexp m' f s'
          end
        end
      ) n (meval a) st

    | _ => None
    end.

  Definition evaluatesTo := fun m st0 st1 => meval (inlineAll m) st0 = Some st1.

  (* world peace *)
End Medial.
