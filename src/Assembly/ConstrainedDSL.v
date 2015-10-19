
Require Export ConstrainedComputation.

Notation "const A" := CConst A.
Notation "var A" := CVar A.
Notation "A : B" := CJoin A B.
Notation "left A" := CLeft A.
Notation "right A" := CRight A.

Notation "~ A" := UnaryExpr CNot A.
Notation "- A" := UnaryExpr COpp A.
Notation "A + B" := BinaryExpr CPlus A B.
Notation "A - B" := BinaryExpr CMinus A B.
Notation "A * B" := BinaryExpr CMult A B.
Notation "A / B" := BinaryExpr CDiv A B.
Notation "A & B" := BinaryExpr CAnd A B.
Notation "A | B" := BinaryExpr COr A B.
Notation "A ^ B" := BinaryExpr CXor A B.
Notation "A >> B" := BinaryExpr CRShift A B.
Notation "A << B" := BinaryExpr CLShift A B.

Definition toExpr {type} (term: CTerm type) = TermExpr term.
Coersion toExpr: {type} CTerm type >-> CExpr type.

Notation "ret A" := CRet A
Notation "A . B" := CCompose A B
Notation "A ? B : C" := CIte A B C
Notation "set A to B in C" := CLet A B C
