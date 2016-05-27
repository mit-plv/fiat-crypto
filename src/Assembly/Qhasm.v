Require Import QhasmEvalCommon.
Require Import Language.
Require Import List NPeano.

Module Qhasm <: Language.
  Import ListNotations.
  Import State.

  (* A constant upper-bound on the number of operations we run *)
  Definition State := State.

  (* Program Types *)
  Inductive QhasmStatement :=
    | QAssign: Assignment -> QhasmStatement
    | QOp: Operation -> QhasmStatement
    | QJmp: Conditional -> Label -> QhasmStatement
    | QLabel: Label -> QhasmStatement.

  Hint Constructors QhasmStatement.

  Definition Program := list QhasmStatement.

  (* Only execute while loops a fixed number of times.
     TODO (rsloan): can we do any better? *)

  Fixpoint getLabelMap' (prog: Program) (cur: LabelMap) (index: nat): LabelMap :=
    match prog with
    | p :: ps =>
      match p with
      | QLabel label => getLabelMap' ps (NatM.add label index cur) (S index)
      | _ => getLabelMap' ps cur (S index)
      end
    | [] => cur
    end.

  Definition getLabelMap (prog: Program): LabelMap :=
    getLabelMap' prog (NatM.empty nat) O.

  Inductive QhasmEval: nat -> Program -> LabelMap -> State -> State -> Prop :=
    | QEOver: forall p n m s, (n > (length p))%nat -> QhasmEval n p m s s
    | QEZero: forall p s m, QhasmEval O p m s s
    | QEAssign: forall n p m a s s' s'',
        (nth_error p n) = Some (QAssign a)
      -> evalAssignment a s = Some s'
      -> QhasmEval (S n) p m s' s''
      -> QhasmEval n p m s s''
    | QEOp: forall n p m a s s' s'',
        (nth_error p n) = Some (QOp a)
      -> evalOperation a s = Some s'
      -> QhasmEval (S n) p m s' s''
      -> QhasmEval n p m s s''
    | QEJmpTrue: forall (n loc next: nat) p m c l s s',
        (nth_error p n) = Some (QJmp c l)
      -> evalCond c s = Some true
      -> NatM.find l m = Some loc
      -> QhasmEval loc p m s s'
      -> QhasmEval n p m s s'
    | QEJmpFalse: forall (n loc next: nat) p m c l s s',
        (nth_error p n) = Some (QJmp c l)
      -> evalCond c s = Some false
      -> QhasmEval (S n) p m s s'
      -> QhasmEval n p m s s'
    | QELabel: forall n p m l s s',
        (nth_error p n) = Some (QLabel l)
      -> QhasmEval (S n) p m s s'
      -> QhasmEval n p m s s'.

  Definition evaluatesTo := fun p => QhasmEval O p (getLabelMap p).

  (* world peace *)
End Qhasm.

