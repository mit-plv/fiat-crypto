Require Import QhasmEvalCommon QhasmUtil.
Require Import Language.
Require Import List.

Module Type Pseudo <: Language.
  Import ListNotations State Util.

  (* Input/output specification *)
  Parameter width: nat.
  Parameter vars: nat.

  Definition const: Type := word width.

  (* Qhasm primitives we'll use *)
  Parameter izero: IConst width.
  
  Definition ireg: nat -> IReg width :=
    match izero with
    | constInt32 _ => regInt32
    | constInt64 _ => regInt64
    end.

  Definition iconst: word width -> IConst width :=
    match izero with
    | constInt32 _ => constInt32
    | constInt64 _ => constInt64
    end.

  Definition stack: nat -> Stack width :=
    match izero with
    | constInt32 _ => stack32
    | constInt64 _ => fun x => stack64 (2 * x)
    end.

  (* Program Types *)
  Definition State := list const.

  Inductive WBinOp: Set :=
    | Wplus: WBinOp    | Wmult: WBinOp
    | Wminus: WBinOp   | Wand: WBinOp.

  Inductive WNatOp: Set :=
    | Wones: WNatOp    | Wzeros: WNatOp.

  Inductive WShiftOp: Set :=
    | Wshl: WShiftOp   | Wshr: WShiftOp.

  Inductive Pseudo: nat -> nat -> Type :=
    | PVar: forall n, Index n -> Pseudo n 1
    | PConst: forall n, const -> Pseudo n 1

    | PBin: forall n m, WBinOp -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PNat: forall n, WNatOp -> nat -> Pseudo n 1
    | PShift: forall n, WShiftOp -> Pseudo n 1 -> nat -> Pseudo n 1

    | PLet: forall n k m, Pseudo n k -> Pseudo (n + k) m -> Pseudo n m
    | PComp: forall n k m, Pseudo n k -> Pseudo k m -> Pseudo n m
    | PComb: forall n a b, Pseudo n a -> Pseudo n b -> Pseudo n (a + b)

    | PIf: forall n m, TestOp -> Index n -> Index n -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PFunExp: forall n, Pseudo n n -> nat -> Pseudo n n.

  Hint Constructors Pseudo.

  Definition Program := Pseudo vars vars.

  Definition applyBin (op: WBinOp) (a b: list const): option (list const) :=
    match op with
    | Wplus => None
    | Wmult => None
    | Wminus => None
    | Wand => None
    end.

  Definition applyNat (op: WNatOp) (v: nat): option (list const) :=
    match op with
    | Wones => None
    | Wzeros => None
    end.

  Definition applyShift (op: WShiftOp) (v: const) (n: nat): option (list const) :=
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
        applyNat op v = Some s'
      -> PseudoEval n 1 (PNat n op v) s s'

    | PEShift: forall n m a s s' w op,
        applyShift op w m = Some s'
      -> PseudoEval n 1 a s [w]
      -> PseudoEval n 1 (PShift n op a m) s s'

    | PELet: forall n m k s x s' a b,
        PseudoEval n k a s x
      -> PseudoEval (n + k) m b (s ++ x) s'
      -> PseudoEval n m (PLet n k m a b) s s'

    | PEComp: forall n k m s s' s'' a b,
        PseudoEval n k a s s'
      -> PseudoEval k m b s' s''
      -> PseudoEval n m (PComp n k m a b) s s''

    | PEComb: forall n a b x y s sx sy,
        PseudoEval n a x s sx
      -> PseudoEval n b y s sy
      -> PseudoEval n (a + b) (PComb n a b x y) s (sx ++ sy)

    | PEIfTrue: forall n m t x y s sx wx wy (i0 i1: Index n),
        nth_error s i0 = Some wx
      -> evalTest t wx wy = true
      -> PseudoEval n m x s sx
      -> PseudoEval n m (PIf n m t i0 i1 x y) s sx

    | PEIfFalse: forall n m t x y s sy wx wy (i0 i1: Index n),
        nth_error s i1 = Some wy
      -> evalTest t wx wy = false
      -> PseudoEval n m y s sy
      -> PseudoEval n m (PIf n m t i0 i1 x y) s sy

    | PEFunExpO: forall n f s,
        PseudoEval n n (PFunExp n f O) s s

    | PEFunExpS: forall n f s s' s'' e e',
        e = S e'
      -> PseudoEval n n f s s'
      -> PseudoEval n n (PFunExp n f e') s' s''
      -> PseudoEval n n (PFunExp n f e) s s''.

  Definition evaluatesTo := PseudoEval vars vars.

  (* world peace *)
End Pseudo.
