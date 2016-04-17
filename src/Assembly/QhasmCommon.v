Require Export String List NPeano NArith.
Require Export Bedrock.Word.

(* A formalization of x86 qhasm *)
Definition Label := nat.
Definition Index (limit: nat) := {x: nat | (x < limit)%nat}.
Definition Invert := bool.

(* Sugar and Tactics *)

Definition convert {A B: Type} (x: A) (H: A = B): B :=
  eq_rect A (fun B0 : Type => B0) x B H.

Notation "'always' A" := (fun _ => A) (at level 90) : state_scope.
Notation "'cast' e" := (convert e _) (at level 20) : state_scope.
Notation "'lift' e" := (exist _ e _) (at level 20) : state_scope.
Notation "'contra'" := (False_rec _ _) : state_scope.

Obligation Tactic := abstract intuition.

(* Float Datatype *)

Record Float (floatBits: nat) (fractionBits: nat) := mkFloat {
  validFloat: word floatBits -> Prop;

  wordToFloat: word fractionBits -> {w: word floatBits | validFloat w};
  floatToWord: {w: word floatBits | validFloat w} -> word fractionBits;

  wordToFloat_spec : forall x, floatToWord (wordToFloat x) = x;

  serialize: {w: word floatBits | validFloat w} -> N;
  deserialize: N -> {w: word floatBits | validFloat w};

  serialize_spec1 : forall x, serialize (deserialize x) = x;
  serialize_spec2 : forall x, deserialize (serialize x) = x;

  floatPlus: {w: word floatBits | validFloat w}
          ->  {w: word floatBits | validFloat w}
          ->  {w: word floatBits | validFloat w};

  floatPlus_wordToFloat : forall n m,
      (wordToN n < (Npow2 (fractionBits - 1)))%N ->
      (wordToN m < (Npow2 (fractionBits - 1)))%N ->
      floatPlus (wordToFloat n) (wordToFloat m)
        = wordToFloat (wplus n m);

  floatMult: {w: word floatBits | validFloat w}
          ->  {w: word floatBits | validFloat w}
          ->  {w: word floatBits | validFloat w};

  floatMult_wordToFloat : forall n m,
      (wordToN n < (Npow2 (fractionBits / 2)%nat))%N ->
      (wordToN m < (Npow2 (fractionBits / 2)%nat))%N ->
      floatMult (wordToFloat n) (wordToFloat m)
        = wordToFloat (wmult n m);

  floatAnd:  {w: word floatBits | validFloat w}
          ->  {w: word floatBits | validFloat w}
          ->  {w: word floatBits | validFloat w};

  floatAnd_wordToFloat : forall n m,
    floatAnd (wordToFloat n) (wordToFloat m) = wordToFloat (wand n m)
}.

Parameter Float32: Float 32 23.

Parameter Float64: Float 64 52.

(* Asm Types *)
Inductive IConst: nat -> Type :=
  | constInt32: word 32 -> IConst 32.

Inductive FConst: nat -> Type :=
  | constFloat32: word 23 -> FConst 32
  | constFloat64: word 52 -> FConst 64.

Inductive IReg: nat -> Type :=
  | regInt32: nat -> IReg 32.

Inductive FReg: nat -> Type :=
  | regFloat32: nat -> FReg 32
  | regFloat64: nat -> FReg 64.

Inductive Stack: nat -> Type :=
  | stack32: nat -> Stack 32
  | stack64: nat -> Stack 64
  | stack128: nat -> Stack 128.

Definition CarryState := option bool.

(* Assignments *)
Inductive Assignment : Type :=
  | AStackInt: forall n, IReg n -> Stack n -> Assignment
  | AStackFloat: forall n, FReg n -> Stack n -> Assignment

  | ARegInt: forall n, IReg n -> IReg n -> Assignment
  | ARegFloat: forall n, FReg n -> FReg n -> Assignment

  | AConstInt: forall n, IReg n -> IConst n -> Assignment
  | AConstFloat: forall n, FReg n -> FConst n -> Assignment

  | AIndex: forall n m, IReg n -> IReg m -> Index (n/m)%nat -> Assignment
  | APtr: forall n, IReg 32 -> Stack n -> Assignment.

Hint Constructors Assignment.

(* Operations *)

Inductive IntOp :=
  | IPlus: IntOp | IMinus: IntOp
  | IXor: IntOp  | IAnd: IntOp | IOr: IntOp.

Inductive FloatOp :=
  | FPlus: FloatOp | FMult: FloatOp | FAnd: FloatOp.

Inductive RotOp :=
  | Shl: RotOp | Shr: RotOp.

Inductive Operation :=
  | IOpConst: IntOp -> IReg 32 -> IConst 32 -> Operation
  | IOpReg: IntOp -> IReg 32 -> IReg 32 -> Operation

  | FOpConst32: FloatOp -> FReg 32 -> FConst 32 -> Operation
  | FOpReg32: FloatOp -> FReg 32 -> FReg 32 -> Operation

  | FOpConst64: FloatOp -> FReg 64 -> FConst 64 -> Operation
  | FOpReg64: FloatOp -> FReg 64 -> FReg 64 -> Operation

  | OpRot: RotOp -> IReg 32 -> Index 32 -> Operation.

Hint Constructors Operation.

(* Control Flow *)

Inductive TestOp :=
  | TEq: TestOp   | TLt: TestOp  | TLe: TestOp
  | TGt: TestOp   | TGe: TestOp.

Inductive Conditional :=
  | TestTrue: Conditional
  | TestFalse: Conditional
  | TestInt: forall n, TestOp -> IReg n -> IReg n -> Conditional
  | TestFloat: forall n, TestOp -> FReg n -> FReg n -> Conditional.

Hint Constructors Conditional.

(* Reg, Stack, Const Utilities *)

Definition getIRegWords {n} (x: IReg n) :=
  match x with
  | regInt32 loc => 1
  end.

Definition getFRegWords {n} (x: FReg n) :=
  match x with
  | regFloat32 loc => 1
  | regFloat64 loc => 2
  end.

Definition getStackWords {n} (x: Stack n) :=
  match x with
  | stack32 loc => 1
  | stack64 loc => 2
  | stack128 loc => 4
  end.

Definition getIRegIndex {n} (x: IReg n): nat :=
  match x with
  | regInt32 loc => loc
  end.

Definition getFRegIndex {n} (x: FReg n): nat :=
  match x with
  | regFloat32 loc => loc
  | regFloat64 loc => loc
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
  | _ => 0
  end.

Definition floatRegCount (base: nat): nat :=
  match base with
  | 32 => 8
  | 64 => 8
  | _ => 0
  end.
