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

  (* Only execute while loops a fixed number of times.
     TODO (rsloan): can we do any better? *)

  (* TODO: make this inductive *)
  Fixpoint almostEvalWhile (cond: Conditional) (prog: Program) (state: State) (horizon: nat): option State :=
    match horizon with
    | (S m) =>
      if (evalCond cond state)
      then almostEvalWhile cond prog state m
      else Some state
    | O => None
    end.

  Fixpoint eval (prog: Program) (state: State): option State :=
    match prog with
    | ASkip => Some state
    | ASeq a b =>
      match (eval a state) with
      | (Some st') => eval b st'
      | _ => None
      end
    | AAssign a => evalAssignment a state
    | AOp a => evalOperation a state
    | ACond c a b =>
      if (evalCond c state)
      then eval a state
      else eval b state
    | AWhile c a => almostEvalWhile c a state maxOps
    end.

  (* world peace *)
End AlmostQhasm.
