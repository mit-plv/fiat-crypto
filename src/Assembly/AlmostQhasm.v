Require Import QhasmEvalCommon.
Require Import Language.
Require Import List.

Module AlmostQhasm <: Language.
  Import ListNotations.
  Import State.

  (* A constant upper-bound on the number of operations we run *)
  Definition maxOps: nat := 1000.

  (* Program Types *)
  Definition State := State.

  Inductive AlmostProgram: Set :=
    | ASkip: AlmostProgram
    | ASeq: AlmostProgram -> AlmostProgram -> AlmostProgram
    | AAssign: Assignment -> AlmostProgram
    | AOp: Operation -> AlmostProgram
    | ACond: Conditional -> AlmostProgram -> AlmostProgram -> AlmostProgram
    | AWhile: Conditional -> AlmostProgram -> AlmostProgram.

  Hint Constructors AlmostProgram.

  Definition Program := AlmostProgram.

  Inductive AlmostEval: AlmostProgram -> State -> State -> Prop :=
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
      -> AlmostEval (AWhile c a) s s.

  Definition evaluatesTo := AlmostEval.

  (* world peace *)
End AlmostQhasm.
