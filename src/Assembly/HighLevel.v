
Inductive Const32 : Set = | const32: word 32 -> Const32.

Inductive HL :=
  | Input: Const32 -> HL
  | Variable: Const32 -> HL
  | Let: forall m, nat -> HL -> HL -> HL
  | Lift1: (Const32 -> Const32) -> HL -> HL
  | Lift2: (Const32 -> Const32 -> Const32) -> HL -> HL -> HL.
