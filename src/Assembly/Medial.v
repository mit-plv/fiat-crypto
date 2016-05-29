Require Import QhasmEvalCommon Pseudo.
Require Import Language.
Require Import List.

Module Medial (Arch: PseudoMachine) <: Language.
  Import MedState EvalUtil Arch.

  Definition W := word width.

  (* Program Types *)
  Definition State := MedState width.
  Transparent State.

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
        match (getVar y st) with
        | Some v => Some (setVar x v st)
        | _ => None
        end

      | MAMem x y i =>
        match (getMem y i st) with
        | Some v => Some (setVar x v st)
        | _ => None
        end

      | MAConst x c => Some (setVar x c st)
      end

    | MOp o =>
      match o with
      | MIOpConst io a c =>
        omap (getVar a st) (fun v =>
          let (res, c') := evalIntOp io v c in
          Some (setVar a res (setCarryOpt c' st)))

      | MIOpReg io a b =>
        omap (getVar a st) (fun va =>
          omap (getVar b st) (fun vb =>
            let (res, c') := evalIntOp io va vb in
            Some (setVar a res (setCarryOpt c' st))))

      | MCOpReg o a b =>
        omap (getVar a st) (fun va =>
          omap (getVar b st) (fun vb =>
            let c := match (snd st) with | Some b => b | _ => false end in
            let (res, c') := evalCarryOp o va vb c in
            Some (setVar a res (setCarry c' st))))

      | MDOpReg duo a b (Some x) =>
        omap (getVar a st) (fun va =>
          omap (getVar b st) (fun vb =>
            let (low, high) := evalDualOp duo va vb in
            Some (setVar a low (setVar x high st))))

      | MDOpReg duo a b None =>
        omap (getVar a st) (fun va =>
          omap (getVar b st) (fun vb =>
            let (low, high) := evalDualOp duo va vb in
            Some (setVar a low st)))

      | MOpRot ro a x =>
        omap (getVar a st) (fun v =>
          let res := evalRotOp ro v (proj1_sig x) in
          Some (setVar a res st))
      end

    | MCond c a b =>
      match c with
      | MC t x y =>
        omap (getVar x st) (fun vx =>

          (* TODO: why can't we infer width here? *)
          omap (@getVar width y st) (fun vy =>
            if (evalTest t vx vy)
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
