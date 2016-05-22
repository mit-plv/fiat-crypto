Require Import QhasmEvalCommon Pseudo.
Require Import Language.
Require Import List.

Module Medial (M: PseudoMachine) <: Language.
  Import ListNotations.
  Import State.
  Import M.

  Definition W := word width.

  (* Program Types *)
  Definition State := DefMap.

  Inductive MAssignment : Type :=
    | MAVar: nat -> nat -> MAssignment 
    | MAConst: nat -> W -> MAssignment.

  Inductive MOperation :=
    | MIOpConst: IntOp -> nat -> W -> MOperation
    | MIOpReg: IntOp -> nat -> nat -> MOperation
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
    | MFunexp: nat -> Medial -> Medial.

  Definition Program := Medial.

  Fixpoint meval (m: Medial) (st: State): option State :=
    let omap := fun {A B} (x: option A) (f: A -> option B) =>
      match x with | Some y => f y | _ => None end in
    match m with
    | MSkip => Some st
    | MSeq a b => omap (meval a st) (fun s => meval b s)
    | MAssign a =>
      match a with
      | MAVar x y =>
        match (NatM.find y st) with
        | (Some v) => Some (NatM.add x v st)
        | _ => None
        end
      | MAConst x c => Some (NatM.add x (wordToN c) st)
      end
    | MOp o =>
      match o with
      | MIOpConst io a c =>
        omap (NatM.find a st) (fun v =>
          let res := evalIOp io (NToWord _ v) c in
          Some (NatM.add a (wordToN res) st))

      | MIOpReg io a b =>
        omap (NatM.find a st) (fun va =>
          omap (NatM.find b st) (fun vb =>
            let res := evalIOp io (NToWord width va) (NToWord width vb) in
            Some (NatM.add a (wordToN res) st)))

      | MDOpReg duo a b (Some x) =>
        omap (NatM.find a st) (fun va =>
          omap (NatM.find b st) (fun vb =>
            let res := evalDualOp duo (NToWord width va) (NToWord width vb) in
            Some (NatM.add a (wordToN (fst res))
                   (NatM.add x (wordToN (snd res)) st))))

      | MDOpReg duo a b None =>
        omap (NatM.find a st) (fun va =>
          omap (NatM.find b st) (fun vb =>
            let res := evalDualOp duo (NToWord width va) (NToWord width vb) in
            Some (NatM.add a (wordToN (fst res)) st)))

      | MOpRot ro a x =>
        omap (NatM.find a st) (fun v =>
          let res := evalRotOp ro (NToWord width v) (proj1_sig x) in
          Some (NatM.add a (wordToN res) st))
      end
    | MCond c a b =>
      match c with
      | MC t x y =>
        omap (NatM.find x st) (fun vx =>
          omap (NatM.find y st) (fun vy =>
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
    end.

  Definition evaluatesTo := fun m st0 st1 => meval m st0 = Some st1.

  (* world peace *)
End Medial.
