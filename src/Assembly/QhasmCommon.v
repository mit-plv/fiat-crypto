Require Export String List.
Require Export Bedrock.Word.

Require Import ZArith NArith NPeano.
Require Import Coq.Structures.OrderedTypeEx.
Require Import FMapAVL FMapList.

Require Import QhasmUtil.

Module NatM := FMapAVL.Make(Nat_as_OT).
Definition DefMap: Type := NatM.t N.
Definition StateMap: Type := NatM.t DefMap.
Definition LabelMap: Type := NatM.t nat.

(* A formalization of x86 qhasm *)

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
  | stack128: nat -> Stack 128.

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

(* Machine State *)

Inductive State :=
| fullState (regState: StateMap) (stackState: StateMap): State.

Definition getReg {n} (reg: Reg n) (state: State): option (word n).
  destruct state; inversion reg as [L H | L H | L H | L H];
    destruct (NatM.find n regState) as [map |];
    first [ destruct (NatM.find L map) as [n0 |] | exact None ];
    first [ rewrite H; exact (Some (NToWord n n0)) | exact None ].
Defined.

Definition setReg {n} (reg: Reg n) (value: word n) (state: State): State.
  inversion state; inversion reg as [L H | L H | L H | L H];
    destruct (NatM.find n regState) as [map |];
    first [
       exact
         (fullState
           (NatM.add n
             (NatM.add L (wordToN value) map) regState)
             stackState)
     | exact state ].
Defined.

Definition getStack {n} (entry: Stack n) (state: State): option (word n).
  destruct state; inversion entry as [L H | L H | L H];
    destruct (NatM.find n stackState) as [map |];
    first [ destruct (NatM.find L map) as [n0 |] | exact None ];
    first [ rewrite H; exact (Some (NToWord n n0)) | exact None ].
Defined.

Definition setStack {n} (entry: Stack n) (value: word n) (state: State): State.
  inversion state; inversion entry as [L H | L H | L H];
    destruct (NatM.find n stackState) as [map |];
    first [
       exact
         (fullState regState
           (NatM.add n
             (NatM.add L (wordToN value) map) regState))
     | exact state ].
Defined.

Definition emptyState: State :=
  fullState (NatM.empty DefMap) (NatM.empty DefMap).
