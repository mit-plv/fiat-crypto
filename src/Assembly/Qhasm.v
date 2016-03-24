
Require Import String.

Inductive Const32 : Set = | const32: word 32 -> Const32.

Inductive Reg (len: nat) : Set =
  | reg32: string -> Reg 32
  | reg3232: string -> Reg 64
  | reg6464: string -> Reg 128
  | float80: string -> Reg 80.

Inductive Stack (len: nat) : Set =
  | stack32: string -> Stack 32.
  | stack64: string -> Stack 64.
  | stack128: string -> Stack 128.

Definition Index (limit: nat) := {x: nat | x < limit}.

Inductive Assignment : Set :=
  | Assign32Stack32: Reg 32 -> Stack32 -> Assignment
  | Assign32Stack16: Reg 32 -> Stack32 -> Index 2 -> Assignment
  | Assign32Stack8: Reg 32 -> Stack32 -> Index 4 -> Assignment
  | Assign32Stack64: Reg 32 -> Stack64 -> Index 2 -> Assignment
  | Assign32Stack128: Reg 32 -> Stack128 -> Index 2 -> Assignment

  | Assign32Reg32: Reg 32 -> Reg 32 -> Assignment
  | Assign32Reg16: Reg 32 -> Reg 32 -> Index 2 -> Assignment
  | Assign32Reg8: Reg 32 -> Reg 32 -> Index 4 -> Assignment
  | Assign32Reg64: Reg 32 -> Reg64 -> Index 2 -> Assignment
  | Assign32Reg128: Reg 32 -> Reg 128 -> Index 4 -> Assignment

  | Assign3232Stack32: Reg 64 -> Index 2 -> Stack32 -> Assignment
  | Assign3232Stack64: Reg 64 -> Stack64 -> Assignment
  | Assign3232Stack128: Reg 64 -> Stack128 -> Index 2 -> Assignment

  | Assign3232Reg32: Reg 64 -> Index 2 -> Reg 32 -> Assignment
  | Assign3232Reg64: Reg 64 -> Reg64 -> Assignment
  | Assign3232Reg128: Reg 64 -> Reg 128 -> M 2 -> Assignment

  | AssignConstant: Reg 32 -> Const32 -> Assignment
  | AssignPtr: Reg 32 -> Stack64.

Hint Constructors Assignment.
                          
Inductive BinOp :=
  | Plus: BinOp | Minus: BinOp | Mult: BinOp
  | Div: BinOp | Xor: BinOp | And: BinOp.

Inductive RotOp :=
  | Shl: NatOp | Shr: NatOp | Rotl: NatOp | Rotr: NatOp.

Inductive Operation :=
  | OpReg32Constant: BinOp -> Reg 32 -> Const32 -> Operation
  | OpReg32Reg32: BinOp -> Reg 32 -> Reg 32 -> Operation
  | RotReg32: RotOp -> Reg 32 -> Index 32 -> Operation

  | OpReg64Constant: BinOp -> Reg 32 -> Const32 -> Operation
  | OpReg64Reg64: BinOp -> Reg 64 -> Reg 64 -> Operation

  | OpReg128Constant: BinOp -> Reg 128 -> Const32 -> Operation
  | OpReg128Reg128: BinOp -> Reg 128 -> Reg 128 -> Operation.

Hint Constructors Operation.

Inductive TestOp :=
  | Eq: TestOp
  | Lt: TestOp
  | UnsignedLt: TestOp
  | Gt: TestOp
  | UnsignedGt: TestOp.

Definition Invert := bool.

Definition Conditional :=
  | TestReg32Reg32: TestOp -> Invert -> Reg 32 -> Reg 32 -> Conditional
  | TestReg32Const: TestOp -> Invert -> Reg 32 -> W -> Conditional.

Hint Constructors Conditional.

Definition Label := nat.

Inductive AlmostQhasm :=
  | QSeq: AlmostQhasm -> AlmostQhasm -> AlmostQhasm
  | QAssign: Assignment -> AlmostQhasm
  | QOp: Operation -> AlmostQhasm 
  | QCond: Conditional -> AlmostQhasm -> AlmostQhasm -> AlmostQhasm
  | QWhile: Conditional -> AlmostQhasm -> AlmostQhasm

Hint Constructors AlmostQhasm.

Inductive Qhasm :=
  | QSeq: Qhasm -> Qhasm -> Qhasm
  | QAssign: Assignment -> Qhasm
  | QOp: Operation -> Qhasm
  | QCond: Conditional -> Qhasm -> Qhasm -> Qhasm
  | QWhile: Conditional -> Qhasm -> Qhasm

Hint Constructors Qhasm.

(* evalReg: Qhasm -> Reg 32 -> Reg 32
   evalStack: Qhasm -> Stack32 -> Stack32 *)

