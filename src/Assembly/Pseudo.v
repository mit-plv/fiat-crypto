Require Import QhasmEvalCommon QhasmUtil State.
Require Import Language.
Require Import List.

Module Type PseudoMachine.
  Parameter width: nat.
  Parameter vars: nat.
  Parameter width_spec: Width width.
End PseudoMachine.

Module Pseudo (M: PseudoMachine) <: Language.
  Import ListNotations State Util M.

  Definition const: Type := word width.

  (* Program Types *)
  Definition State := ((list const) * (list (list const)) * (option bool))%type.

  Definition var (st: State)  := fst (fst st).
  Definition mem (st: State)  := snd (fst st).
  Definition carry (st: State) := snd st.

  Inductive Pseudo: nat -> nat -> Type :=
    | PVar: forall n, Index n -> Pseudo n 1
    | PMem: forall n m, Index n -> Index m -> Pseudo n 1
    | PConst: forall n, const -> Pseudo n 1

    | PBin: forall n, IntOp -> Pseudo n 2 -> Pseudo n 1
    | PDual: forall n, DualOp -> Pseudo n 2 -> Pseudo n 2
    | PCarry: forall n, CarryOp -> Pseudo n 2 -> Pseudo n 1
    | PShift: forall n, RotOp -> Index width -> Pseudo n 1 -> Pseudo n 1

    | PIf: forall n m, TestOp -> Index n -> Index n -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PFunExp: forall n, Pseudo n n -> nat -> Pseudo n n

    | PLet: forall n k m, Pseudo n k -> Pseudo (n + k) m -> Pseudo n m
    | PComb: forall n a b, Pseudo n a -> Pseudo n b -> Pseudo n (a + b)
    | PCall: forall n m, Pseudo n m -> Pseudo n m.

  Hint Constructors Pseudo.

  Definition Program := Pseudo vars vars.

  Fixpoint pseudoEval {n m} (prog: Pseudo n m) (st: State): option State :=
    match prog with
    | PVar n i =>
      omap (nth_error (var st) i) (fun x =>
        Some ([x], mem st, carry st))

    | PMem n m v i =>
      omap (nth_error (mem st) v) (fun vec =>
        omap (nth_error vec i) (fun x =>
          Some ([x], mem st, carry st)))

    | PConst n c => Some ([c], mem st, carry st)

    | PBin n o p =>
      omap (pseudoEval p st) (fun sp =>
        match sp with
        | ([wa; wb], m', _) =>
          let (v, c) := evalIntOp o wa wb in Some ([v], m', c)
        | _ => None
        end)

    | PCarry n o p =>
      omap (pseudoEval p st) (fun sp =>
        match sp with
        | ([wa; wb], m', Some c) =>
          let (v, c') := evalCarryOp o wa wb c in Some ([v], m', Some c')
        | _ => None
        end)

    | PDual n o p =>
      omap (pseudoEval p st) (fun sp =>
        match sp with
        | ([wa; wb], m', co) =>
          let (low, high) := evalDualOp o wa wb in Some ([low; high], m', co)
        | _ => None
        end)

    | PShift n o a x =>
      omap (pseudoEval x st) (fun sx =>
        match sx with
        | ([wx], m', co) => Some ([evalRotOp o wx a], m', co)
        | _ => None
        end)

    | PLet n k m f g =>
      omap (pseudoEval f st) (fun sf =>
        omap (pseudoEval g ((var st) ++ (var sf), mem sf, carry sf))
          (fun sg => Some sg))

    | PComb n a b f g =>
      omap (pseudoEval f st) (fun sf =>
        omap (pseudoEval g st) (fun sg =>
          Some ((var sf) ++ (var sg), mem sg, carry sg)))

    | PIf n m t i0 i1 l r =>
      omap (nth_error (var st) i0) (fun v0 =>
        omap (nth_error (var st) i1) (fun v1 =>
          if (evalTest t v0 v1)
          then pseudoEval l st
          else pseudoEval r st ))

    | PFunExp n p e =>
      (fix funexpseudo (e': nat) (st': State) := 
        match e' with
        | O => Some st'
        | S e'' =>
          omap (pseudoEval p st') (fun st'' =>
            funexpseudo e'' st'')
        end) e st

    | PCall n m p => pseudoEval p st
    end.

  Definition evaluatesTo := fun (p: Program) (st st': State) => (pseudoEval p st = Some st').

  (* world peace *)
End Pseudo.

Module PseudoUnary32 <: PseudoMachine.
  Definition width := 32.
  Definition vars := 1.
  Definition width_spec := W32.
  Definition const: Type := word width.
End PseudoUnary32.

Module PseudoUnary64 <: PseudoMachine.
  Definition width := 64.
  Definition vars := 1.
  Definition width_spec := W64.
  Definition const: Type := word width.
End PseudoUnary64.
 