Require Import QhasmEvalCommon QhasmUtil.
Require Import Language.
Require Import List.

Module Pseudo <: Language.
  Import ListNotations State Util.

  (* Program Types *)
  Definition State := list (word 32).

  Inductive WBinOp: Set :=
    | Wplus: WBinOp    | Wmult: WBinOp
    | Wminus: WBinOp   | Wand: WBinOp.

  Inductive WNatOp: Set :=
    | Wones: WNatOp    | Wzeros: WNatOp.

  Inductive WShiftOp: Set :=
    | Wshl: WShiftOp   | Wshr: WShiftOp.

  (* WAST: function from all variables to a single (word 32) *)
  (* Pseudo: function from inputs to outputs to a single (word 32) *)
  Inductive Pseudo: nat -> nat -> Set :=
    | PVar: forall n, Index n -> Pseudo n 1
    | PConst: forall n, word 32 -> Pseudo n 1

    | PBin: forall n m, WBinOp -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PNat: forall n, nat -> Pseudo n 1
    | PShift: forall n, WShiftOp -> Pseudo n 1 -> nat -> Pseudo n 1

    | PLet: forall n k m, Pseudo n k -> Pseudo (n + k) m -> Pseudo n m
    | PComp: forall n k m, Pseudo n k -> Pseudo k m -> Pseudo n m
    | PComb: forall n a b, Pseudo n a -> Pseudo n b -> Pseudo n (a + b)

    | PIf: forall n m, TestOp -> Index n -> Index n -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PFunExp: forall n k, nat -> Pseudo n k -> Pseudo (n + k) n -> nat -> Pseudo n n.

  Hint Constructors Pseudo.

  Definition Program := Pseudo.

  Definition applyBin (op: WBinOp) (a b: list (word 32)): option (list (word 32)) :=
    match op with
    | Wplus => None
    | Wmult => None
    | Wminus => None
    | Wand => None
    end.

  Definition applyNat (op: WNatOp) (v: nat): option (list (word 32)) :=
    match op with
    | Wones => None
    | Wzeros => None
    end.

  Definition applyShift (op: WShiftOp) (v: word 32): option (list (word 32)) :=
    match op with
    | Wshl => None
    | Wshr => None
    end.

  Inductive PseudoEval: forall n m, Pseudo n m -> State -> State -> Prop :=
    | PEVar: forall s n (i: Index n) w,
        nth_error s i = Some w
      -> PseudoEval n 1 (PVar n i) s [w]

    | PEConst: forall n s w,
        PseudoEval n 1 (PConst n w) s [w]

    | PEBin: forall n m a b s sa sb s' op,
        applyBin op sa sb = Some s'
      -> PseudoEval n m a s sa
      -> PseudoEval n m b s sb
      -> PseudoEval n m (PBin n m op a b) s s'

    | PENat: forall n op v s s',
        applyNat op v s'
      -> PseudoEval n (PNat n v) s s'

    | PEShift: forall n, WShiftOp -> Pseudo n 1 -> nat -> Pseudo n 1

.

    | PELet: forall n m, Pseudo n k -> Pseudo (n + k) m -> Pseudo n m
    | PEComp: forall n k m, Pseudo n k -> Pseudo k m -> Pseudo n m
    | PEComb: forall n a b, Pseudo n a -> Pseudo n b -> Pseudo n (a + b)

    | PEIf: forall n m, TestOp -> Index n -> Index n -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PEFunExp: forall n k, nat -> Pseudo n k -> Pseudo (n + k) n -> nat -> Pseudo n n
  .

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
