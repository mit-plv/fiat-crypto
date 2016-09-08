Require Import Crypto.Assembly.QhasmCommon Crypto.Assembly.QhasmEvalCommon.
Require Import Crypto.Assembly.Language.
Require Import Coq.Lists.List.

Module AlmostQhasm <: Language.
  Import QhasmEval.

  (* Program Types *)
  Definition Params := unit.
  Definition State := fun (_: Params) => State.

  Inductive AlmostProgram: Set :=
    | ASkip: AlmostProgram
    | ASeq: AlmostProgram -> AlmostProgram -> AlmostProgram
    | AAssign: Assignment -> AlmostProgram
    | AOp: Operation -> AlmostProgram
    | ACond: Conditional -> AlmostProgram -> AlmostProgram -> AlmostProgram
    | AWhile: Conditional -> AlmostProgram -> AlmostProgram
    | ADef: Label -> AlmostProgram -> AlmostProgram -> AlmostProgram
    | ACall: Label -> AlmostProgram.

  Hint Constructors AlmostProgram.

  Definition Program := fun (_: Params) => AlmostProgram.

  Fixpoint inline (l: nat) (f prog: AlmostProgram) :=
    match prog with
    | ASeq a b => ASeq (inline l f a) (inline l f b)
    | ACond c a b => ACond c (inline l f a) (inline l f b)
    | AWhile c a => AWhile c (inline l f a)
    | ADef l' f' p' =>
      if (Nat.eq_dec l l')
      then prog
      else ADef l' (inline l f f') (inline l f p')
    | ACall l' =>
      if (Nat.eq_dec l l')
      then f
      else prog
    | _ => prog
    end.

  Inductive AlmostEval {x: Params}: Program x -> State x -> State x -> Prop :=
    | AESkip: forall s, AlmostEval ASkip s s
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
        -> AlmostEval (AWhile c a) s s
    | AEFun: forall l f p s s',
        AlmostEval (inline l f p) s s'
        -> AlmostEval (ADef l f p) s s'.

  Definition evaluatesTo := @AlmostEval.

  (* world peace *)
End AlmostQhasm.
