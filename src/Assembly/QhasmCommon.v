Require Export String List.
Require Export Bedrock.Word.

(* A formalization of x86 qhasm *)
Definition Label := nat.
Definition Index (limit: nat) := {x: nat | (x < limit)%nat}.
Definition Invert := bool.

(* A constant upper-bound on the number of operations we run *)
Definition maxOps: nat := 1000.

(* Datatypes *)
Inductive Const: nat -> Set :=
  | const32: word 32 -> Const 32
  | const64: word 64 -> Const 64
  | const128: word 128 -> Const 128.

Inductive Reg: nat -> Set :=
  | reg32: nat -> Reg 32
  | reg3232: nat -> Reg 64
  | reg6464: nat -> Reg 128
  | reg80: nat -> Reg 80.

Inductive Stack: nat -> Set :=
  | stack32: nat -> Stack 32
  | stack64: nat -> Stack 64
  | stack128: nat -> Stack 128
  | stack256: nat -> Stack 256
  | stack512: nat -> Stack 512.

(* Assignments *)
Inductive Assignment : Set :=
  | Assign32Stack32: Reg 32 -> Stack 32 -> Assignment
  | Assign32Stack16: Reg 32 -> Stack 32 -> Index 2 -> Assignment
  | Assign32Stack8: Reg 32 -> Stack 32 -> Index 4 -> Assignment
  | Assign32Stack64: Reg 32 -> Stack 64 -> Index 2 -> Assignment
  | Assign32Stack128: Reg 32 -> Stack 128 -> Index 2 -> Assignment

  | Assign32Reg32: Reg 32 -> Reg 32 -> Assignment
  | Assign32Reg16: Reg 32 -> Reg 32 -> Index 2 -> Assignment
  | Assign32Reg8: Reg 32 -> Reg 32 -> Index 4 -> Assignment
  | Assign32Reg64: Reg 32 -> Reg 64 -> Index 2 -> Assignment
  | Assign32Reg128: Reg 32 -> Reg 128 -> Index 4 -> Assignment

  | Assign3232Stack32: Reg 64 -> Index 2 -> Stack 32 -> Assignment
  | Assign3232Stack64: Reg 64 -> Stack 64 -> Assignment
  | Assign3232Stack128: Reg 64 -> Stack 128 -> Index 2 -> Assignment

  | Assign3232Reg32: Reg 64 -> Index 2 -> Reg 32 -> Assignment
  | Assign3232Reg64: Reg 64 -> Reg 64 -> Assignment
  | Assign3232Reg128: Reg 64 -> Reg 128 -> Index 2 -> Assignment

  | Assign6464Reg32: Reg 128 -> Index 4 -> Reg 32 -> Assignment
  | Assign6464Reg64: Reg 128 -> Index 2 -> Reg 64 -> Assignment
  | Assign6464Reg128: Reg 128 -> Reg 128 -> Assignment

  | AssignConstant: Reg 32 -> Const 32 -> Assignment.

Hint Constructors Assignment.

(* Operations *)

Inductive BinOp :=
  | Plus: BinOp | Minus: BinOp | Mult: BinOp
  | Div: BinOp | Xor: BinOp | And: BinOp | Or: BinOp.

Inductive RotOp :=
  | Shl: RotOp | Shr: RotOp | Rotl: RotOp | Rotr: RotOp.

Inductive Operation :=
  | OpReg32Constant: BinOp -> Reg 32 -> Const 32 -> Operation
  | OpReg32Reg32: BinOp -> Reg 32 -> Reg 32 -> Operation
  | RotReg32: RotOp -> Reg 32 -> Index 32 -> Operation

  | OpReg64Constant: BinOp -> Reg 64 -> Const 64 -> Operation
  | OpReg64Reg64: BinOp -> Reg 64 -> Reg 64 -> Operation

  | OpReg128Constant: BinOp -> Reg 128 -> Const 32 -> Operation
  | OpReg128Reg128: BinOp -> Reg 128 -> Reg 128 -> Operation.

Hint Constructors Operation.

(* Control Flow *)

Inductive TestOp :=
  | TEq: TestOp
  | TLt: TestOp
  | TUnsignedLt: TestOp
  | TGt: TestOp
  | TUnsignedGt: TestOp.

Inductive Conditional :=
  | TestTrue: Conditional
  | TestFalse: Conditional
  | TestReg32Reg32: TestOp -> Invert -> Reg 32 -> Reg 32 -> Conditional
  | TestReg32Const: TestOp -> Invert -> Reg 32 -> Const 32 -> Conditional.

Definition invertConditional (c: Conditional): Conditional :=
  match c with
  | TestTrue => TestFalse
  | TestFalse => TestTrue
  | TestReg32Reg32 o i r0 r1 => TestReg32Reg32 o (negb i) r0 r1
  | TestReg32Const o i r c => TestReg32Const o (negb i) r c
  end.

Hint Constructors Conditional.

(* Reg, Stack, Const Utilities *)

Definition getRegWords {n} (x: Reg n) :=
  match x with
  | reg32 loc => 1
  | reg3232 loc => 2
  | reg6464 loc => 4
  | reg80 loc => 2
  end.

Definition getStackWords {n} (x: Stack n) :=
  match x with
  | stack32 loc => 1
  | stack64 loc => 2
  | stack128 loc => 4
  | stack256 loc => 8
  | stack512 loc => 16
  end.

Definition getRegIndex {n} (x: Reg n): nat :=
  match x with
  | reg32 loc => loc
  | reg3232 loc => loc
  | reg6464 loc => loc
  | reg80 loc => loc
  end.

Definition getStackIndex {n} (x: Stack n): nat :=
  match x with
  | stack32 loc => loc
  | stack64 loc => loc
  | stack128 loc => loc
  | stack256 loc => loc
  | stack512 loc => loc
  end.

(* For register allocation checking *)
Definition regCount (base: nat): nat :=
  match base with
  | 32 => 7   | 64 => 8
  | 128 => 8  | 80 => 8
  | _ => 0
  end.

