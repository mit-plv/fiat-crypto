
Require Import Bedrock.Word.
(* Expression *)

(* THEORY: if we permit operations on joined types, we can represent
 *         vector operations without searching *)
Inductive CType: Set :=
  | Words | list word

Definition cTypeToWord(type: CType): Type :=
  match type with
  | Int32 => word 32
  | Int64 => word 64
  | Join a b => (cTypeToWord a) * (cTypeToWord b)
  end.

Definition bits(type: CType): nat :=
  match type with
  | Int32 => 32
  | Int64 => 64
  | Join a b => (bits a) + (bits b)
  end.

Inductive UnaryOp :=
  | CNot | COpp.

Inductive BinaryOp :=
  | CPlus | CMinus  | CMult
  | CDiv  | CAnd    | COr
  | CXor  | CRShift | CLShift.

Inductive CTerm (type: CType) :=
  | CConst : (word (bits type)) -> (CTerm type)
  | CVar : Name -> CTerm type
  | CJoin : forall t1 t2, CTerm t1 -> CTerm t2 -> CTerm (Join t1 t2)
  | CLeft : CTerm (Join type _) -> CTerm type
  | CRight : CTerm (Join _ type) -> CTerm type.

Inductive CExpr (type: CType) :=
  | TermExpr : (CTerm type) -> (CExpr type)
  | UnaryExpr : UnaryOp -> (CTerm type) -> (CExpr type)
  | BinaryExpr : BinaryOp -> (CTerm type) -> (CTerm type) -> (CExpr type).

Inductive Sub (inType: CType) (outType: CType) :=
  | CRet : Expr outType -> Sub inType outType
  (* | Repeat *)
  | CCompose : forall medType,
           (Sub inType medType)
        -> (Sub medType outType)
        -> (Sub inType outType)
  | CIte : (Sub inType Int32)    (* condition *)
        -> (Sub inType outType)  (* then *)
        -> (Sub inType outType)  (* else *)
        -> (Sub inType outType)
  | CLet : Name -> CTerm ->
        -> (Sub inType outType)
        -> (Sub inType outType).

Definition bindTerm {valueType objectType} (var: Name) (value: CTerm valueType) (object: CTerm objectType): CTerm objectType :=
  match valueType with
  | objectType =>
    match object with
    | CConst _ => object
    | CVar name => if (name = var) then value else object end
    | CJoin left right =>
        CJoin (bindTerm var value left) (bindTerm var value right)
    | CLeft from => CLeft (bindTerm var value larger)
    | CRight from => CRight (bindTerm var value larger)
    end
  | _ => object.

Definition bindExpr {valueType objectType} (var: Name) (value: CTerm valueType) (object: CExpr objectType): CExpr objectType :=
  match object with
  | TermExpr term => TermExpr (bindTerm var value term)
  | UnaryExpr op term => UnaryExpr op (bindTerm var value term)
  | BinaryExpr op term1 term2 =>
      BinaryExpr op (bindTerm var value term1) (bindTerm var value term2)
  end.

Definition bind {valueType fromType toType} (var: Name) (value: CTerm) (object: Sub fromType toType): Sub fromType toType :=
  match object with
  | CRet expr => CRet (bindExpr var value expr)
  | CCompose left right =>
      CCompose (bind var value left) (bind var value right)
  | CIte cond thenSub elseSub =>
      CIte (bind var value cond)
           (bind var value thenSub)
           (bind var value elseSub)
  | CLet name bindTo sub =>
      CLet name bindTo (bind var value sub)
  end.

Inductive TermEquiv {t} (left: CTerm t) (right: (cTypeToWord t)) :=
  | EquivInt32: forall (w: (word (bits Int32))), TermEquiv (CConst w) w
  | EquivInt64: forall (w: (word (bits Int64))), TermEquiv (CConst w) w
  | EquivJoin: forall aComp bComp aGallina bGallina,
      TermEquiv aComp aGallina
   -> TermEquiv bComp bGallina
   -> TermEquiv (CJoin aComp bComp) (aGallina, bGallina)
  | EquivLeft: forall aComp aGallina,
      TermEquiv aComp aGallina
   -> TermEquiv (CLeft aComp) (fst aGallina)
  | EquivRight: forall aComp aGallina,
      TermEquiv aComp aGallina
   -> TermEquiv (CRight aComp) (snd aGallina).

Definition applyBinaryOp {n: nat} (op: UnaryOp) (a b: word n) :=
  match op with
  | CPlus => Word.plus a b
  | CMinus => Word.minus a b
  | CMult => Word.mult a b
  | CDiv => Word.div a b
  | CAnd => Word.and a b
  | COr => Word.or a b
  | CXor => Word.xor a b
  | CRShift => Word.rshift a b
  | CLShift => Word.lshift a b
  end.

Definition applyUnaryOp {n: nat} (op: UnaryOp) (w: word n) :=
  match op with
  | CNot => Word.not w
  | COpp => Word.opp w
  end.

Inductive ExprEquiv {t} (left: CExpr t) (right: (cTypeToWord t)) :=
  | EquivNop: forall aComp aGallina,
      TermEquiv aComp aGallina
   -> ExprEquiv (TermExpr aComp) aGallina
  | EquivNot: forall aComp aGallina op,
      TermEquiv aComp aGallina
   -> ExprEquiv (UnaryExpr op aComp) (applyUnaryOp op aGallina)
  | EquivPlus: forall aComp aGallina bComp bGallina op,
      TermEquiv aComp aGallina
   -> TermEquiv bComp bGallina
   -> ExprEquiv (BinaryExpr op aComp bComp) (applyBinaryOp aGallina bGallina).

Inductive SubEquiv {fromType toType} (left: Sub fromType toType) (right: (cTypeToWord fromType) -> (cTypeToWord toType)) :=
  | EquivRet: forall aComp aGallina,
      ExprEquiv aComp aGallina
   -> SubEquiv (CRet aComp) (fun x => aGallina)
  | EquivComp: forall fComp fGallina gComp gGallina,
      SubEquiv fComp fGallina
   -> SubEquiv gComp gGallina
   -> SubEquiv (CCompose fComp gComp) (fun x => gGallina (fGallina x))
  | EquivIte: forall (fComp: Sub fromType Int32) fGallina gComp gGallina,
      SubEquiv fComp fGallina
   -> SubEquiv gComp gGallina
   -> SubEquiv hComp hGallina
   -> SubEquiv (CIte fComp gComp hComp)
        (fun x => if (neq 0 (fGallina x)) then gGallina x else hGallina x)
  | EquivLet: forall name bindTo sub fGallina,
      SubEquiv (bind name bindTo sub) fGallina
   -> SubEquiv (CLet name bindTo sub) fGallina.
