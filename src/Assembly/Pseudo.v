Require Import QhasmEvalCommon QhasmUtil State.
Require Import Language.
Require Import List.

Module Type PseudoMachine.
  Parameter width: nat.
  Parameter vars: nat.
  Parameter width_spec: Width width.
End PseudoMachine.

Module Pseudo (M: PseudoMachine) <: Language.
  Import EvalUtil ListState Util M.

  Definition const: Type := word width.

  (* Program Types *)
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
    | PCall: forall n m, Label -> Pseudo n m -> Pseudo n m.

  Hint Constructors Pseudo.

  Definition Program := Pseudo vars vars.
  Definition State := ListState width.

  Fixpoint pseudoEval {n m} (prog: Pseudo n m) (st: State): option State :=
    match prog with
    | PVar n i => omap (getVar i st) (fun x => Some (setList [x] st))
    | PMem n m v i => omap (getMem v i st) (fun x => Some (setList [x] st))
    | PConst n c => Some (setList [c] st)
    | PBin n o p =>
      omap (pseudoEval p st) (fun sp =>
        match (getList sp) with
        | [wa; wb] =>
          let (v, c) := evalIntOp o wa wb in
          Some (setList [v] (setCarryOpt c sp))
        | _ => None
        end)

    | PCarry n o p =>
      omap (pseudoEval p st) (fun sp =>
        match (getList sp, getCarry sp) with
        | ([wa; wb], Some c) =>
          let (v, c') := evalCarryOp o wa wb c in
          Some (setList [v] (setCarry c' sp))
        | _ => None
        end)

    | PDual n o p =>
      omap (pseudoEval p st) (fun sp =>
        match (getList sp) with
        | [wa; wb] =>
          let (low, high) := evalDualOp o wa wb in
          Some (setList [low; high] sp)
        | _ => None
        end)

    | PShift n o a x =>
      omap (pseudoEval x st) (fun sx =>
        match (getList sx) with
        | [wx] => Some (setList [evalRotOp o wx a] sx)
        | _ => None
        end)

    | PLet n k m f g =>
      omap (pseudoEval f st) (fun sf =>
        omap (pseudoEval g (setList ((getList st) ++ (getList sf)) sf))
          (fun sg => Some sg))

    | PComb n a b f g =>
      omap (pseudoEval f st) (fun sf =>
        omap (pseudoEval g st) (fun sg =>
          Some (setList ((getList sf) ++ (getList sg)) sg)))

    | PIf n m t i0 i1 l r =>
      omap (getVar i0 st) (fun v0 =>
        omap (getVar i1 st) (fun v1 =>
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

    | PCall n m _ p => pseudoEval p st
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
 