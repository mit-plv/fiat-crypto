Require Import QhasmEvalCommon.
Require Import Language.
Require Import List NPeano.

Module Qhasm <: Language.
  Import ListNotations.

  (* A constant upper-bound on the number of operations we run *)
  Definition maxOps: nat := 1000.
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

  Fixpoint eval' (prog: Program) (state: State) (loc: nat) (horizon: nat) (labelMap: LabelMap) (maxLoc: nat): option State :=
    match horizon with
    | (S h) =>
      match (nth_error prog loc) with
      | Some stmt =>
        let (nextState, jmp) :=
          match stmt with
          | QAssign a => (evalAssignment a state, None)
          | QOp o => (evalOperation o state, None)
          | QLabel l => (state, None)
          | QJmp c l =>
            if (evalCond c state)
            then (state, Some l)
            else (state, None)
          end
        in
          match jmp with
          | None =>
            if (Nat.eq_dec loc maxLoc)
            then Some nextState
            else eval' prog nextState (S loc) h labelMap maxLoc
          | Some nextLoc =>
            eval' prog nextState nextLoc h labelMap nextLoc
          end
      | None => None
      end
    | O => None
    end.

  Definition eval (prog: Program) (state: State): option State :=
    eval' prog state O maxOps (getLabelMap prog) ((length prog) - 1).

  (* world peace *)
End Qhasm.

