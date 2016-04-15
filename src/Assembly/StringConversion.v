Require Export Language Conversion.
Require Import QhasmCommon QhasmEvalCommon QhasmUtil Qhasm.
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
    Import Util.

    Definition nameSuffix (n: nat): string := 
      (nToHex (N.of_nat n)).

    Coercion wordToString {n} (w: word n): string := 
      "0x" ++ (nToHex (wordToN w)).

    Coercion constToString {n} (c: Const n): string :=
      match c with
      | const32 w => "0x" ++ w
      | const64 w => "0x" ++ w
      | const128 w => "0x" ++ w
      end.

    Coercion indexToString {n} (i: Index n): string :=
      "0x" ++ (nToHex (N.of_nat i)).

    Coercion regToString {n} (r: Reg n): string :=
      match r with
      | reg32 n => "ex" ++ (nameSuffix n)
      | reg3232 n => "mm" ++ (nameSuffix n)
      | reg6464 n => "xmm" ++ (nameSuffix n)
      | reg80 n => "st" ++ (nameSuffix n)
      end.

    Coercion stackToString {n} (s: Stack n): string :=
      match s with
      | stack32 n => "word" ++ (nameSuffix n)
      | stack64 n => "double" ++ (nameSuffix n)
      | stack128 n => "quad" ++ (nameSuffix n)
      | stack256 n => "stack256n" ++ (nameSuffix n)
      | stack512 n => "stack512n" ++ (nameSuffix n)
      end.

    Coercion stringToSome (x: string): option string := Some x.

    Definition stackLocation {n} (s: Stack n): word 32 :=
      combine (natToWord 8 n) (natToWord 24 n).

    Definition assignmentToString (a: Assignment): option string :=
      match a with

      (* r = s *)
      | Assign32Stack32 r s => r ++ " = " ++ s

      | _ => None
      end.

    Coercion binOpToString (b: BinOp): string :=
      match b with
      | Plus => "+"
      | Minus => "-"
      | Mult => "*"
      | Div => "/"
      | Xor => "^"
      | And => "&"
      | Or => "|"
      end.

    Coercion rotOpToString (r: RotOp): string :=
      match r with
      | Shl => "<<"
      | Shr => ">>"
      | Rotl => "<<<"
      | Rotr => ">>>"
      end.

    Definition operationToString (o: Operation): option string :=
      match o with
      | OpReg32Constant b r c =>
        r ++ " " ++ b ++ "= " ++ c
      | OpReg32Reg32 b r0 r1 =>
        r0 ++ " " ++ b ++ "= " ++ r1
      | RotReg32 o r i =>
        r ++ " " ++ o ++ "= " ++ i
      | OpReg64Constant b r c =>
        r ++ " " ++ b ++ "= " ++ c
      | OpReg64Reg64 b r0 r1 =>
        r0 ++ " " ++ b ++ "= " ++ r1
      | _ => None
      end.

    Coercion testOpToString (t: TestOp): string :=
      match t with
      | TEq => "="
      | TLt => "<"
      | TUnsignedLt => "unsigned<"
      | TGt => ">"
      | TUnsignedGt => "unsigned>"
      end.

    Definition conditionalToString (c: Conditional): string :=
      let f := fun (i: bool) => if i then "!" else "" in
      match c with
      | TestTrue => ""
      | TestFalse => ""
      | TestReg32Reg32 o i r0 r1 => (f i) ++ o ++ "?" ++ r0 ++ " " ++ r1
      | TestReg32Const o i r c =>(f i) ++ o ++ "?" ++ r ++ " " ++ c
      end.

  End Elements.

  Section Parsing.

    Inductive Entry :=
      | regEntry: forall n, Reg n -> Entry
      | stackEntry: forall n, Stack n -> Entry
      | constEntry: forall n, Const n -> Entry.

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
