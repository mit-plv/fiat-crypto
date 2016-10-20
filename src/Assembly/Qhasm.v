Require Import QhasmCommon QhasmEvalCommon.
Require Import List NPeano.

Module Qhasm.
  Import ListNotations.
  Import QhasmEval.

  Definition State := State.

  (* Program Types *)
  Inductive QhasmStatement :=
    | QAssign: Assignment -> QhasmStatement
    | QOp: Operation -> QhasmStatement
    | QCond: Conditional -> Label -> QhasmStatement
    | QLabel: Label -> QhasmStatement
    | QCall: Label -> QhasmStatement
    | QRet: QhasmStatement.

  Hint Constructors QhasmStatement.

  Definition Program := list QhasmStatement.

  (* Only execute while loops a fixed number of times.
     TODO (rsloan): can we do any better? *)

  Fixpoint getLabelMap' (prog: Program) (cur: LabelMap) (index: nat): LabelMap :=
    match prog with
    | p :: ps =>
      match p with
      | QLabel label => @getLabelMap' ps (NatM.add label index cur) (S index)
      | _ => @getLabelMap' ps cur (S index)
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
    | QECondTrue: forall (n loc next: nat) p m c l s s',
        (nth_error p n) = Some (QCond c l)
      -> evalCond c s = Some true
      -> NatM.find l m = Some loc
      -> QhasmEval loc p m s s'
      -> QhasmEval n p m s s'
    | QECondFalse: forall (n loc next: nat) p m c l s s',
        (nth_error p n) = Some (QCond c l)
      -> evalCond c s = Some false
      -> QhasmEval (S n) p m s s'
      -> QhasmEval n p m s s'
    | QERet: forall (n n': nat) s s' s'' p m,
        (nth_error p n) = Some QRet
      -> popRet s = Some (s', n')
      -> QhasmEval n' p m s' s''
      -> QhasmEval n  p m s s''
    | QECall: forall (w n n' lbl: nat) s s' s'' p m,
        (nth_error p n) = Some (QCall lbl)
      -> NatM.find lbl m = Some n'
      -> QhasmEval n' p m (pushRet (S n) s') s''
      -> QhasmEval n  p m s s''
    | QELabel: forall n p m l s s',
        (nth_error p n) = Some (QLabel l)
      -> QhasmEval (S n) p m s s'
      -> QhasmEval n p m s s'.

  Definition evaluatesTo := fun p => @QhasmEval O p (getLabelMap p).

  (* world peace *)
End Qhasm.
