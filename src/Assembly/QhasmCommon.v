Require Export String List NPeano NArith.
Require Export Bedrock.Word.

(* A formalization of x86 qhasm *)
Definition Label := nat.
Definition Index (limit: nat) := {x: nat | (x < limit)%nat}.

(* Sugar and Tactics *)

Definition convert {A B: Type} (x: A) (H: A = B): B :=
  eq_rect A (fun B0 : Type => B0) x B H.

Notation "'always' A" := (fun _ => A) (at level 90) : state_scope.
Notation "'cast' e" := (convert e _) (at level 20) : state_scope.
Notation "'lift' e" := (exist _ e _) (at level 20) : state_scope.
Notation "'contra'" := (False_rec _ _) : state_scope.

Obligation Tactic := abstract intuition.

(* Asm Types *)
Inductive ISize: nat -> Type :=
  | I32: ISize 32
  | I64: ISize 64.

Inductive IConst: nat -> Type :=
  | constInt32: word 32 -> IConst 32
  | constInt64: word 64 -> IConst 64.

Inductive IReg: nat -> Type :=
  | regInt32: nat -> IReg 32
  | regInt64: nat -> IReg 64.

Inductive Stack: nat -> Type :=
  | stack32: nat -> Stack 32
  | stack64: nat -> Stack 64
  | stack128: nat -> Stack 128.

Definition CarryState := option bool.

(* Assignments *)
Inductive Assignment : Type :=
  | ARegStackInt: forall n, IReg n -> Stack n -> Assignment
  | AStackRegInt: forall n, Stack n -> IReg n -> Assignment
  | ARegRegInt: forall n, IReg n -> IReg n -> Assignment
  | AConstInt: forall n, IReg n -> IConst n -> Assignment
  | AIndex: forall n m, IReg n -> Stack m -> Index (m/n)%nat -> Assignment
  | APtr: forall n, IReg 32 -> Stack n -> Assignment.

Hint Constructors Assignment.

(* Operations *)

Inductive IntOp :=
  | IPlus: IntOp | IMinus: IntOp
  | IXor: IntOp  | IAnd: IntOp | IOr: IntOp.

Inductive DualOp :=
  | IMult: DualOp.

Inductive RotOp :=
  | Shl: RotOp | Shr: RotOp.

Inductive Operation :=
  | IOpConst: forall n, IntOp -> IReg n -> IConst n -> Operation
  | IOpReg: forall n, IntOp -> IReg n -> IReg n -> Operation
  | DOpReg: forall n, DualOp -> IReg n -> IReg n -> option (IReg n) -> Operation
  | OpRot: forall n, RotOp -> IReg n -> Index n -> Operation.

Hint Constructors Operation.

(* Control Flow *)

Inductive TestOp :=
  | TEq: TestOp   | TLt: TestOp  | TLe: TestOp
  | TGt: TestOp   | TGe: TestOp.

Inductive Conditional :=
  | TestTrue: Conditional
  | TestFalse: Conditional
  | TestInt: forall n, TestOp -> IReg n -> IReg n -> Conditional.

Hint Constructors Conditional.

(* Reg, Stack, Const Utilities *)

Definition getIRegWords {n} (x: IReg n) :=
  match x with
  | regInt32 loc => 1
  | regInt64 loc => 2
  end.

Definition getStackWords {n} (x: Stack n) :=
  match x with
  | stack32 loc => 1
  | stack64 loc => 2
  | stack128 loc => 4
  end.

Definition getIConstValue {n} (x: IConst n): nat :=
  match x with
  | constInt32 v => wordToNat v
  | constInt64 v => wordToNat v
  end.

Definition getIRegIndex {n} (x: IReg n): nat :=
  match x with
  | regInt32 loc => loc
  | regInt64 loc => loc
  end.

Definition getStackIndex {n} (x: Stack n): nat :=
  match x with
  | stack32 loc => loc
  | stack64 loc => loc
  | stack128 loc => loc
  end.

(* For register allocation checking *)
Definition intRegCount (base: nat): nat :=
  match base with
  | 32 => 7
  | 64 => 8
  | _ => 0
  end.
