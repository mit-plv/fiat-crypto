
Require Import AsmComputation.

Notation "stack32 A" := StackAsmVar A.
Notation "int32 A" := MemoryAsmVar A.
Notation "reg32 A" := Register A.

Notation "{{ A }}" := AsmConst A.

Notation "** A" := AsmRef A.
Notation "&& A" := AsmDeref A.

Notation "~ A" := Unary AsmNot A.
Notation "- A" := Unary AsmOpp A.
Notation "A + B" := Binary AsmPlus A B.
Notation "A - B" := Binary AsmMinus A B.
Notation "A * B" := Binary AsmMult A B.
Notation "A / B" := Binary AsmDiv A B.
Notation "A & B" := Binary AsmAnd A B.
Notation "A | B" := Binary AsmOr A B.
Notation "A ^ B" := Binary AsmXor A B.
Notation "A >> B" := Binary AsmRShift A B.
Notation "A << B" := Binary AsmLShift A B.

Notation "declare A" := AsmDeclare A
Notation "A ::= B" := AsmSet A B
Notation "(A B) =:= C" := AsmDestruct A B C
Notation "A =:= (B C)" := AsmConstruct A B C
Notation "A ;; B" := AsmSeq A B
Notation "A :: B" := AsmLabel A B
Notation "goto A" := AsmGoto A
Notation "A ? B" := AsmIf A B

Notation "enter A do B" := Asm A B
