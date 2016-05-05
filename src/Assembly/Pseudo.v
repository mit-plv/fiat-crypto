Require Import QhasmEvalCommon QhasmUtil.
Require Import Language.
Require Import List.

Module Type PseudoMachine.
  Parameter width: nat.
  Parameter vars: nat.
  Parameter width_spec: ISize width.
End PseudoMachine.

Module Pseudo (M: PseudoMachine) <: Language.
  Import ListNotations State Util M.

  Definition const: Type := word width.

  Definition width_dec: {width = 32} + {width = 64}.
    destruct width_spec.
    - left; abstract intuition.
    - right; abstract intuition.
  Defined.

  Definition ireg (x: nat): IReg width :=
    match width_spec with
    | I32 => regInt32 x
    | I64 => regInt64 x
    end.

  Definition iconst (x: word width): IConst width.
    refine (
      if width_dec
      then (convert constInt32 _) x
      else (convert constInt64 _) x);
    abstract (rewrite _H; intuition).
  Defined.

  Definition stack (x: nat): Stack width :=
    match width_spec with
    | I32 => stack32 x
    | I64 => stack64 (2 * x)
    end.

  (* Program Types *)
  Definition State := list const.

  Inductive WBinOp: Set :=
    | Wplus: WBinOp
    | Wminus: WBinOp   | Wand: WBinOp.

  Inductive WNatOp: Set :=
    | Wones: WNatOp    | Wzeros: WNatOp.

  Inductive WShiftOp: Set :=
    | Wshl: WShiftOp   | Wshr: WShiftOp.

  Inductive Pseudo: nat -> nat -> Type :=
    | PVar: forall n, Index n -> Pseudo n 1
    | PConst: forall n, const -> Pseudo n 1

    | PBin: forall n, WBinOp -> Pseudo n 1 -> Pseudo n 1 -> Pseudo n 1
    | PNat: forall n, WNatOp -> Index width -> Pseudo n 1
    | PShift: forall n, WShiftOp -> Pseudo n 1 -> Index width -> Pseudo n 1

    | PLet: forall n k m, Pseudo n k -> Pseudo (n + k) m -> Pseudo n m
    | PComp: forall n k m, Pseudo n k -> Pseudo k m -> Pseudo n m
    | PComb: forall n a b, Pseudo n a -> Pseudo n b -> Pseudo n (a + b)

    | PIf: forall n m, TestOp -> Index n -> Index n -> Pseudo n m -> Pseudo n m -> Pseudo n m
    | PFunExp: forall n, Pseudo n n -> nat -> Pseudo n n.

  Hint Constructors Pseudo.

  Definition Program := Pseudo vars vars.

  Definition applyBin (op: WBinOp) (a b: word width): option (list const) :=
    match op with
    | Wplus => Some [(wplus a b)]
    | Wminus => Some [(wminus a b)]
    | Wand => Some [(wand a b)]
    end.

  Definition applyNat (op: WNatOp) (v: Index width): option (list const).
    refine match op with
    | Wones => Some [convert (zext (wones v) (width - v)) _]
    | Wzeros => Some [wzero width]
    end; abstract (
      destruct v; simpl;
      replace (x + (width - x)) with width;
      intuition ).
  Defined.

  Definition applyShift (op: WShiftOp) (v: const) (n: Index width): option (list const).
    refine match op with
    | Wshl => Some [convert (Word.combine (wzero n) (split1 (width - n) n (convert v _))) _]
    | Wshr => Some [convert (Word.combine (split2 n (width - n) (convert v _)) (wzero n)) _]
    end; abstract (
      unfold const;
      destruct n; simpl;
      replace (width - x + x) with width;
      replace (x + (width - x)) with width;
      intuition ).
  Defined.

  Inductive PseudoEval: forall n m, Pseudo n m -> State -> State -> Prop :=
    | PEVar: forall s n (i: Index n) w,
        nth_error s i = Some w
      -> PseudoEval n 1 (PVar n i) s [w]

    | PEConst: forall n s w,
        PseudoEval n 1 (PConst n w) s [w]

    | PEBin: forall n a b s sa sb s' op,
        applyBin op sa sb = Some s'
      -> PseudoEval n 1 a s [sa]
      -> PseudoEval n 1 b s [sb]
      -> PseudoEval n 1 (PBin n op a b) s s'

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

Module PseudoUnary32 <: PseudoMachine.
  Definition width := 32.
  Definition vars := 1.
  Definition width_spec := I32.
  Definition const: Type := word width.
End PseudoUnary32.

Module PseudoUnary64 <: PseudoMachine.
  Definition width := 64.
  Definition vars := 1.
  Definition width_spec := I64.
  Definition const: Type := word width.
End PseudoUnary64.
 