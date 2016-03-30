Require Export Language Conversion.
Require Export Qhasm.
Require Import QhasmCommon QhasmEvalCommon QhasmUtil.
Require Export String Ascii.
Require Import NArith NPeano.
Require Export Bedrock.Word.

Module QhasmString <: Language.
  Definition Program := string.
  Definition State := unit.

  Definition eval (p: Program) (s: State): option State := Some tt.
End QhasmString.

Module StringConversion <: Conversion Qhasm QhasmString.

  (* The easy one *)
  Definition convertState (st: QhasmString.State): option Qhasm.State := None.

  (* Hexadecimal Primitives *)

  Section Hex.
    Local Open Scope string_scope.

    Definition natToDigit (n : nat) : string :=
      match n with
        | 0  => "0"  | 1  => "1"  | 2  => "2"  | 3  => "3"
        | 4  => "4"  | 5  => "5"  | 6  => "6"  | 7  => "7"
        | 8  => "8"  | 9  => "9"  | 10 => "A"  | 11 => "B"
        | 12 => "C"  | 13 => "D"  | 14 => "E"  | _  => "F"
      end.

    Fixpoint nToHex' (n: N) (digitsLeft: nat): string :=
        match digitsLeft with
        | O => ""
        | S nextLeft =>
            match n with
            | N0 => "0"
            | _ => (nToHex' (N.shiftr_nat n 4) nextLeft) ++
                (natToDigit (N.to_nat (N.land n 15%N)))
            end
        end.

    Definition nToHex (n: N): string :=
      let size := (N.size n) in
      let div4 := fun x => (N.shiftr x 2%N) in
      let size' := (size + 4 - (N.land size 3))%N in
      nToHex' n (N.to_nat (div4 size')).

  End Hex.

  (* Conversion of elements *)

  Section Elements.
    Local Open Scope string_scope.

    Definition nameSuffix (n: nat): string := 
      (nToHex (N.of_nat n)).

    Definition wordToString {n} (w: word n): string := 
      "0x" ++ (nToHex (wordToN w)).

    Coercion wordToString : word >-> string.

    Definition constToString {n} (c: Const n): string :=
      match c with
      | const32 w => "0x" ++ w
      | const64 w => "0x" ++ w
      | const128 w => "0x" ++ w
      end.

    Coercion constToString : Const >-> string.

    Definition indexToString {n} (i: Index n): string :=
      "0x" ++ (nToHex (N.of_nat i)).

    Coercion indexToString : Index >-> string.

    Definition regToString {n} (r: Reg n): option string :=
      Some match r with
      | reg32 n => "ex" ++ (nameSuffix n)
      | reg3232 n => "mm" ++ (nameSuffix n)
      | reg6464 n => "xmm" ++ (nameSuffix n)
      | reg80 n => "st" ++ (nameSuffix n)
      end.

    Definition stackToString {n} (s: Stack n): option string :=
      Some match s with
      | stack32 n => "word" ++ (nameSuffix n)
      | stack64 n => "double" ++ (nameSuffix n)
      | stack128 n => "quad" ++ (nameSuffix n)
      end.

    Definition stackLocation {n} (s: Stack n): word 32 :=
      combine (natToWord 8 n) (natToWord 24 n).

    Definition assignmentToString (a: Assignment): option string :=
      match a with
      | Assign32Stack32 r s =>
        match (regToString r, stackToString s) with
        | (Some s0, Some s1) => s0 ++ " = " ++ s1
        | _ => None
        end.
      | Assign32Stack16 r s i => r0 ++ " = " ++ r1
      | Assign32Stack8 r s i =>
      | Assign32Stack64 r s i =>
      | Assign32Stack128 r s i =>

      | Assign32Reg32 r0 r1 => r0 ++ " = " ++ r1 
      | Assign32Reg16 r0 r1 i =>
      | Assign32Reg8 r0 r1 i =>
      | Assign32Reg64 r0 r1 i =>
      | Assign32Reg128 r0 r1 i =>

      | Assign3232Stack32 r i s =>
      | Assign3232Stack64 r s =>
      | Assign3232Stack128 r s i =>

      | Assign3232Reg32 r0 i r1 =>
      | Assign3232Reg64 r0 r1 =>
      | Assign3232Reg128 r0 r1 i =>

      | Assign6464Reg32 r0 i r1 =>
      | Assign6464Reg64 r0 i r1 =>
      | Assign6464Reg128 r0 r1 =>

      | AssignConstant r c =>
      end.

    Definition binOpToString (b: BinOp): string :=
      match b with
      | Plus => "+"
      | Minus => "-"
      | Mult => "*"
      | Div => "/"
      | Xor => "^"
      | And => "&"
      | Or => "|"
      end.

    Definition rotOpToString (r: RotOp): string :=
      match r with
      | Shl => "<<"
      | Shr => ">>"
      | Rotl => "<<<"
      | Rotr => ">>>"
      end.

    Definition operationToString (o: Operation): string :=
      match o with
      | OpReg32Constant b r c =>
        (regToString r) ++ " " ++ (binOpToString b) ++ "= " ++ (constToString c)
      | OpReg32Reg32 b r0 r1 =>
        (regToString r0) ++ " " ++ (binOpToString b) ++ "= " ++ (constToString r1)
      | RotReg32 o r i =>
        (regToString r) ++ " " ++ (rotOpToString o) ++ "= " ++ (constToString i)

      | OpReg64Constant b r c =>
        (regToString r) ++ " " ++ (binOpToString b) ++ "= " ++ (constToString c)
      | OpReg64Reg64 b r0 r1 =>
        (regToString r) ++ " " ++ (binOpToString b) ++ "= " ++ (constToString c)

      | OpReg128Constant b r c =>
        (regToString r) ++ " " ++ (binOpToString b) ++ "= " ++ (constToString c)
      | OpReg128Reg128 b r0 r1 =>
        (regToString r) ++ " " ++ (binOpToString b) ++ "= " ++ (constToString c)
      end.

    Definition testOpToString (t: TestOp): string :=
      match t with
      | TEq =>
      | TLt =>
      | TUnsignedLt =>
      | TGt =>
      | TUnsignedGt =>
      end.

    Definition conditionalToString (c: Conditional): string :=
      match c with
      | TestTrue =>
      | TestFalse =>
      | TestReg32Reg32 o i r0 r1 =>
      | TestReg32Const o i r c =>
      end.

  End Elements.

  Section Parsing.

    Inductive Entry :=
      | regEntry: forall n, Reg n => Entry
      | stackEntry: forall n, Stack n => Entry
      | constEntry: forall n, Const n => Entry.

    Definition allRegs (prog: Qhasm.Program): list Entry := [(* TODO *)]

  End Parsing.

  (* Macroscopic Conversion Methods *)

  Definition convertStatement (statement: Qhasm.QhasmStatement): string :=
    match prog with
    | QAssign a =>
    | QOp o =>
    | QJmp c l =>
    | QLabel l =>
    end.

  Definition convertProgramPrologue (prog: Qhasm.Program): option string :=

  Definition convertProgramEpilogue (prog: Qhasm.Program): option string :=

  Definition convertProgram (prog: Qhasm.Program): option string :=
    Some EmptyString.

  Lemma convert_spec: forall st' prog,
    match ((convertProgram prog), (convertState st')) with
    | (Some prog', Some st) =>
      match (QhasmString.eval prog' st') with
      | Some st'' => Qhasm.eval prog st = (convertState st'')
      | _ => True
      end
    | _ => True
    end.
  Admitted.

End StringConversion.
