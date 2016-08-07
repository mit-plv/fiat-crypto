Require Import Crypto.Assembly.QhasmCommon Crypto.Assembly.QhasmUtil Crypto.Assembly.State.
Require Import Crypto.Assembly.Language Crypto.Assembly.QhasmEvalCommon.
Require Import Coq.Lists.List Coq.Arith.Compare_dec Coq.omega.Omega.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.FixCoqMistakes.

Module Pseudo <: Language.
  Import EvalUtil ListState.

  Inductive Pseudo {w: nat} {s: Width w}: nat -> nat -> Type :=
    | PVar: forall n, option bool -> Index n -> Pseudo n 1
    | PMem: forall n m , Index n -> Index m -> Pseudo n 1
    | PConst: forall n, word w -> Pseudo n 1
    | PBin: forall n, IntOp -> Pseudo n 2 -> Pseudo n 1
    | PDual: forall n, DualOp -> Pseudo n 2 -> Pseudo n 2
    | PCarry: forall n, CarryOp -> Pseudo n 2 -> Pseudo n 1
    | PShift: forall n, RotOp -> Index w -> Pseudo n 1 -> Pseudo n 1
    | PFunExp: forall n, Pseudo n n -> nat -> Pseudo n n
    | PLet: forall n k m, Pseudo n k -> Pseudo (n + k) m -> Pseudo n m
    | PComb: forall n a b, Pseudo n a -> Pseudo n b -> Pseudo n (a + b)
    | PCall: forall n m, Label -> Pseudo n m -> Pseudo n m
    | PIf: forall n m, TestOp -> Index n -> Index n ->
                  Pseudo n m -> Pseudo n m -> Pseudo n m.

  Hint Constructors Pseudo.

  Record Params': Type := mkParams {
    width: nat;
    spec: Width width;
    inputs: nat;
    outputs: nat
  }.

  Definition Params := Params'.
  Definition State (p: Params) : Type := ListState (width p).
  Definition Program (p: Params) : Type :=
    @Pseudo (width p) (spec p) (inputs p) (outputs p).

  Definition Unary32: Params := mkParams 32 W32 1 1.
  Definition Unary64: Params := mkParams 64 W64 1 1.

  (* Evaluation *)

  Fixpoint pseudoEval {n m w s} (prog: @Pseudo w s n m) (st: ListState w) : option (ListState w) :=
    match prog with
    | PVar n _ i => omap (getVar i st) (fun x => Some (setList [x] st))
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
        omap (pseudoEval g (setList (getList st) sf)) (fun sg =>
          Some (setList ((getList sf) ++ (getList sg)) sg)))

    | PIf n m t i0 i1 l r =>
      omap (getVar i0 st) (fun v0 =>
        omap (getVar i1 st) (fun v1 =>
          if (evalTest t v0 v1)
          then pseudoEval l st
          else pseudoEval r st ))

    | PFunExp n p e =>
      (fix funexpseudo (e': nat) (st': ListState w) :=
        match e' with
        | O => Some st'
        | S e'' =>
          omap (pseudoEval p st') (fun st'' =>
            funexpseudo e'' st'')
        end) e st

    | PCall n m _ p => pseudoEval p st
    end.

  Definition evaluatesTo (p: Params) (prog: Program p) (st st': State p) :=
      pseudoEval prog st = Some st'.

  Definition indexize {n: nat} (x: nat) : Index n.
    intros; destruct (le_dec n 0).

    - exists 0; abstract intuition auto with zarith.
    - exists (x mod n)%nat; abstract (
        pose proof (Nat.mod_bound_pos x n); omega).
  Defined.
End Pseudo.
