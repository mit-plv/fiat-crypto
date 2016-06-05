Require Export String List NPeano NArith.
Require Export Bedrock.Word.

(* Utilities *)
Definition Label := nat.

Definition Index (limit: nat) := {x: nat | (x < limit)%nat}.
Coercion indexToNat {lim: nat} (i: Index lim): nat := proj1_sig i.

Inductive Either A B :=
  | xleft: A -> Either A B
  | xright: B -> Either A B.

Definition convert {A B: Type} (x: A) (H: A = B): B :=
  eq_rect A (fun B0 : Type => B0) x B H.

(* Asm Types *)
Inductive Width: nat -> Type := | W32: Width 32 | W64: Width 64.

(* A constant value *)
Inductive Const: nat -> Type :=
  | const: forall {n}, Width n -> word n -> Const n.

(* A variable in any register *)
Inductive Reg: nat -> Type :=
  | reg: forall {n}, Width n -> nat -> Reg n.

(* A variable on the stack. We should use this sparingly. *)
Inductive Stack: nat -> Type :=
  | stack: forall {n}, Width n -> nat -> Stack n.

(* A pointer to a memory block. Called as:
     mem width index length
   where length is in words of size width.

   All Mem pointers will be declared as Stack arguments in the
   resulting qhasm output *)
Inductive Mem: nat -> nat -> Type :=
  | mem: forall {n m}, Width n -> nat -> Mem n m.

(* The state of the carry flag:
   1       = Some true
   0       = Some false
   unknown = None *)
Definition Carry := option bool.

(* Assignments *)

Inductive Assignment : Type :=
  | ARegMem: forall {n m}, Reg n -> Mem n m -> Index m -> Assignment
  | AMemReg: forall {n m}, Mem n m -> Index m -> Reg n -> Assignment
  | AStackReg: forall {n}, Stack n -> Reg n -> Assignment
  | ARegStack: forall {n}, Reg n -> Stack n -> Assignment
  | ARegReg: forall {n}, Reg n -> Reg n -> Assignment
  | AConstInt: forall {n}, Reg n -> Const n -> Assignment.

(* Operations *)

Inductive IntOp :=
  | Add: IntOp  | Sub: IntOp
  | Xor: IntOp  | And: IntOp
  | Or: IntOp.

Inductive CarryOp := | AddWithCarry: CarryOp.

Inductive DualOp := | Mult: DualOp.

Inductive RotOp := | Shl: RotOp | Shr: RotOp.

Inductive Operation :=
  | IOpConst: forall {n}, IntOp -> Reg n -> Const n -> Operation
  | IOpReg: forall {n}, IntOp -> Reg n -> Reg n -> Operation
  | IOpMem: forall {n m}, IntOp -> Reg n -> Mem n m -> Index m -> Operation
  | IOpStack: forall {n}, IntOp -> Reg n -> Stack n -> Operation
  | DOp: forall {n}, DualOp -> Reg n -> Reg n -> option (Reg n) -> Operation
  | ROp: forall {n}, RotOp -> Reg n -> Index n -> Operation
  | COp: forall {n}, CarryOp -> Reg n -> Reg n -> Operation.

(* Control Flow *)

Inductive TestOp :=
  | TEq: TestOp   | TLt: TestOp  | TLe: TestOp
  | TGt: TestOp   | TGe: TestOp.

Inductive Conditional :=
  | CTrue: Conditional 
  | CZero: forall n, Reg n -> Conditional 
  | CReg: forall n, TestOp -> Reg n -> Reg n -> Conditional 
  | CConst: forall n, TestOp -> Reg n -> Const n -> Conditional.

(* Generalized Variable Entry *)

Inductive Mapping (n: nat) :=
  | regM: forall (r: Reg n), Mapping n
  | stackM: forall (s: Stack n), Mapping n
  | memM: forall {m} (x: Mem n m) (i: Index m), Mapping n
  | constM: forall (x: Const n), Mapping n.

(* Parameter Accessors *)

Definition constWidth {n} (x: Const n): nat := n.

Definition regWidth {n} (x: Reg n): nat := n.

Definition stackWidth {n} (x: Stack n): nat := n.

Definition memWidth {n m} (x: Mem n m): nat := n.

Definition memLength {n m} (x: Mem n m): nat := m.

Definition constValueW {n} (x: Const n): word n :=
  match x with | @const n _ v => v end.

Definition constValueN {n} (x: Const n): nat :=
  match x with | @const n _ v => wordToNat v end.

Definition regName {n} (x: Reg n): nat :=
  match x with | @reg n _ v => v end.

Definition stackName {n} (x: Stack n): nat :=
  match x with | @stack n _ v => v end.

Definition memName {n m} (x: Mem n m): nat :=
  match x with | @mem n m _ v => v end.

(* Hints *)
Hint Constructors
     Reg Stack Const Mem Mapping
     Assignment Operation Conditional.
