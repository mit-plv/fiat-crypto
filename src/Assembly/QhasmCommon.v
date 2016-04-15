Require Export String List NPeano.
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
  | reg32: nat -> Reg 32.

Inductive Stack: nat -> Set :=
  | stack32: nat -> Stack 32
  | stack64: nat -> Stack 64
  | stack128: nat -> Stack 128.

Definition CarryState := option bool.

(* Assignments *)
Inductive Assignment : Set :=
  | AStack: forall n, Reg n -> Stack n -> Assignment
  | AReg: forall n, Reg n -> Reg n -> Assignment
  | AIndex: forall n m, Reg n -> Reg m -> Index (n/m)%nat -> Assignment
  | AConst: forall n, Reg n -> Const n -> Assignment
  | APtr: forall n, Reg 32 -> Stack n -> Assignment.

Hint Constructors Assignment.

(* Operations *)

Inductive QOp :=
  | QPlus: QOp | QMinus: QOp | QIMult: QOp
  | QXor: QOp | QAnd: QOp | QOr: QOp.

Inductive QFixedOp :=
  | QMult: QFixedOp | UDiv: QFixedOp.

Inductive QRotOp :=
  | Shl: QRotOp | Shr: QRotOp | QRotl: QRotOp | QRotr: QRotOp.

Inductive Operation :=
  | OpConst: QOp -> Reg 32 -> Const 32 -> Operation
  | OpReg: QOp -> Reg 32 -> Reg 32 -> Operation
  | OpFixedConst: QFixedOp -> Reg 32 -> Const 32 -> Operation
  | OpFixedReg: QFixedOp -> Reg 32 -> Reg 32 -> Operation
  | OpRot: QRotOp -> Reg 32 -> Index 32 -> Operation.

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
  end.

Definition getStackWords {n} (x: Stack n) :=
  match x with
  | stack32 loc => 1
  | stack64 loc => 2
  | stack128 loc => 4
  end.

Definition getRegIndex {n} (x: Reg n): nat :=
  match x with
  | reg32 loc => loc
  | reg3232 loc => loc
  | reg6464 loc => loc
  end.

Definition getStackIndex {n} (x: Stack n): nat :=
  match x with
  | stack32 loc => loc
  | stack64 loc => loc
  | stack128 loc => loc
  end.

(* For register allocation checking *)
Definition regCount (base: nat): nat :=
  match base with
  | 32 => 7   | 64 => 8
  | 128 => 8  | 80 => 8
  | _ => 0
  end.

