Require Import QhasmEvalCommon.
Require Import Language.
Require Import List.

Module Pseudo <: Language.
  Import ListNotations.
  Import State.

  (* Program Types *)
  Definition State := list (word 32).

  Inductive WBinOp: Set :=
    | Wplus: WBinOp    | Wmult: WBinOp
    | Wminus: WBinOp   | Wand: WBinOp.

  Inductive WNatOp: Set :=
    | Wones: WNatOp    | Wzeros: WNatOp.

  Inductive WShiftOp: Set :=
    | Wshl: WShiftOp   | Wshr: WShiftOp.

  Inductive Pseudo: nat -> Set :=
    | PUnit: forall n, Pseudo n

    | PVar: forall n, nat -> Pseudo n
    | PLet: forall n m, nat -> Pseudo n -> Pseudo m -> Pseudo m

    | PCombine: forall n m, Pseudo n -> Pseudo m -> Pseudo (n + m)
    | PLeft: forall n m, Pseudo (n + m) -> Pseudo n
    | PRight: forall n m, Pseudo (n + m) -> Pseudo m

    | PBinOp: WBinOp -> Pseudo 1 -> Pseudo 1 -> Pseudo 1
    | PNatOp: WNatOp -> nat -> Pseudo 1
    | PShiftOp: WShiftOp -> Pseudo 1 -> nat -> Pseudo 1

    | PIf: forall n, TestOp -> Pseudo 1 -> Pseudo 1 ->
           Pseudo n -> Pseudo n -> Pseudo n

    | PFunExp: forall n, nat -> Pseudo n -> Pseudo n -> nat -> Pseudo n.

  Hint Constructors Pseudo.

  Definition Program := Pseudo.

  Coercion unsum {A B} (x: sumbool A B): bool := proj1_sig (bool_of_sumbool x).

  Fixpoint substitute {n m} (var: nat) (value: Pseudo n) (prog: Pseudo m): Pseudo m.
    refine (match prog as prog' in Pseudo m return prog = prog' -> _ with
      | PVar n' v => fun _ =>
      if (andb (Nat.eq_dec n n') (Nat.eq_dec v var))
      then (convert value _)
      else prog
    | _ => fun _ => prog
    end (eq_refl prog)).

    | PLet n' m' v x p => fun _ =>
      let x' := substitute _ _ var value x in
      let p' := substitute _ _ var value p in

      if (andb (Nat.eq_dec n n') (Nat.eq_dec v var))
      then prog
      else (convert (PLet n' m' v x' p') _)

    | PCombine n' m' p0 p1 => fun _ =>
      let p0' := substitute _ _ var value p0 in
      let p1' := substitute _ _ var value p1 in
      (convert (PCombine n' m' p0' p1') _)

    | PLeft n' m' p => fun _ =>
      let p' := substitute _ _ var value p in
      (convert (PLeft n' m' p') _)

    | PRight n' m' p => fun _ =>
      let p' := substitute _ _ var value p in
      (convert (PRight n' m' p') _)

    | PUnit n' => fun _ => prog

    | PBinOp o a b => fun _ =>
      let a' := substitute _ _ var value a in
      let b' := substitute _ _ var value b in
      (convert (PBinOp o a' b') _)

    | PNatOp o x => fun _ => prog

    | PShiftOp o x s => fun _ =>
      let x' := substitute _ _ var value x in
      (convert (PShiftOp o x' s) _)

    | PIf n' o a b pTrue pFalse => fun _ =>
      let a' := substitute _ _ var value a in
      let b' := substitute _ _ var value b in
      let pTrue' := substitute _ _ var value pTrue in
      let pFalse' := substitute _ _ var value pFalse in
      (convert (PIf n' o a' b' pTrue' pFalse') _)

    | PFunExp n' v x p e => fun _ =>
      let x' := substitute _ _ var value x in
      let p' := substitute _ _ var value p in

      if (andb (Nat.eq_dec n n') (Nat.eq_dec v var))
      then prog
      else (convert (PFunExp n' v x' p' e) _)
    end (eq_refl prog)).
  Defined.

  Inductive PseudoEval: forall n, Pseudo n -> State -> State -> Prop :=
    | PELet: forall n v x p p' s s',
         substitute v x p = Some p'
       -> PseudoEval n p' s s'
       -> PseudoEval n (PLet n v x p) s s'

    | PECombine: forall n m, Pseudo n -> Pseudo m -> Pseudo (n + m)
    | PELeft: forall n m, Pseudo (n + m) -> Pseudo n
    | PERight: forall n m, Pseudo (n + m) -> Pseudo m

    | PEUnit: forall n, Pseudo n -> Pseudo n
    | PEBinOp: WBinOp -> Pseudo 1 -> Pseudo 1 -> Pseudo 1
    | PENatOp: WNatOp -> nat -> Pseudo 1
    | PEShiftOp: WShiftOp -> Pseudo 1 -> nat -> Pseudo 1

    | PEIf: forall n, TestOp -> Pseudo 1 -> Pseudo 1 ->
           Pseudo n -> Pseudo n -> Pseudo n

    | PEFunExp: forall n, nat -> Pseudo n -> Pseudo n -> nat -> Pseudo n.

    | AESeq: forall p p' s s' s'',
        AlmostEval p s s'
      -> AlmostEval p' s' s''
      -> AlmostEval (ASeq p p') s s''
    | AEAssign a: forall s s',
        evalAssignment a s = Some s'
      -> AlmostEval (AAssign a) s s'
    | AEOp: forall s s' a,
        evalOperation a s = Some s'
      -> AlmostEval (AOp a) s s'
    | AECondFalse: forall c a b s s',
        evalCond c s = Some false
      -> AlmostEval b s s'
      -> AlmostEval (ACond c a b) s s'
    | AECondTrue: forall c a b s s',
        evalCond c s = Some true
      -> AlmostEval a s s'
      -> AlmostEval (ACond c a b) s s'
    | AEWhileRun: forall c a s s' s'',
        evalCond c s = Some true
      -> AlmostEval a s s'
      -> AlmostEval (AWhile c a) s' s''
      -> AlmostEval (AWhile c a) s s''
    | AEWhileSkip: forall c a s,
        evalCond c s = Some false
      -> AlmostEval (AWhile c a) s s.

  Definition evaluatesTo := AlmostEval.

  (* world peace *)
End AlmostQhasm.
