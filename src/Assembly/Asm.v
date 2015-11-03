
Require Export Bedrock.Word.

Inductive AsmType: Set :=
  | Int32    | Int64
  | Float80  | Int128
  | Pointer.

Definition Name := String.

Inductive AsmVar (type: AsmType) :=
  | StackAsmVar : Name -> AsmVar
  | MemoryAsmVar : Name -> AsmVar
  | Register : Name -> AsmVar.

Definition bits (type: AsmType): nat :=
  match type with
  | Int32 => 32
  | Int64 => 64
  | Float80 => 80
  | Int128 => 128
  | Pointer => 64
  end.

Definition isDouble (a b: AsmType): Prop :=
  match (a, b) with
  | (Int32, Int64) => True
  | (Int64, Int128) => True
  | _ => False
  end.

Inductive UnaryOp :=
  | AsmId | AsmNot | AsmOpp.

Inductive BinaryOp :=
  | AsmPlus | AsmMinus  | AsmMult
  | AsmDiv  | AsmAnd    | AsmOr
  | AsmXor  | AsmRShift | AsmLShift.

Inductive AsmTerm (type: AsmType) :=
  | AsmConst : (word (bits type)) -> (AsmTerm type)
  | AsmVarTerm : AsmVar type -> AsmTerm type
  | AsmRef: AsmVar type -> AsmTerm Pointer
  | AsmDeref: AsmVar Pointer -> AsmTerm type.

Inductive AsmExpr (type: AsmType) :=
  | Unary : UnaryOp -> (AsmTerm type) -> (AsmExpr type)
  | Binary : BinaryOp -> (AsmTerm type) -> (AsmTerm type) -> (AsmExpr type).

Inductive AsmComputation :=
  | AsmDeclare : forall t, AsmVar t -> AsmComputation
  | AsmSet : forall t, AsmVar t -> Expr t -> AsmComputation
  | AsmDestruct : forall t1 t2,
    isDouble t1 t2 -> AsmVar t1 -> AsmVar t1 -> AsmExpr t2
      -> Unit.
  | AsmConstruct : forall t1 t2,
    isDouble t1 t2 -> AsmVar t2 -> AsmExpr t1 -> AsmExpr t1
      -> Unit.
  | AsmSeq : AsmComputation -> AsmComputation -> AsmComputation
  | AsmLabel : String -> AsmComputation -> AsmComputation
  | AsmGoto : String -> AsmComputation
  | AsmIf : forall t, (AsmTerm t) -> AsmComputation -> AsmComputation.

Inductive AsmSub :=
  | Asm: forall t,
    list ((AsmVar t) * (AsmTerm t)) -> AsmComputation -> AsmTerm t.
