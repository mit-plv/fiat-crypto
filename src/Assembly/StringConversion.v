Require Export Language Conversion.
Require Export String Ascii Basics.
Require Import QhasmCommon QhasmEvalCommon QhasmUtil Qhasm.
Require Import NArith NPeano.
Require Export Bedrock.Word.

Module QhasmString <: Language.
  Definition Program := string.
  Definition State := unit.

  Definition evaluatesTo (p: Program) (i o: State): Prop := True.
End QhasmString.

Module StringConversion <: Conversion Qhasm QhasmString.
  Import Qhasm ListNotations.

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
      match c with | const _ _ w => wordToString w end.

    Coercion regToString {n} (r: Reg n): string :=
      match r with
      | reg _ W32 n => "w" ++ (nameSuffix n)
      | reg _ W64 n => "d" ++ (nameSuffix n)
      end.

    Coercion natToString (n: nat): string :=
      "0x" ++ (nToHex (N.of_nat n)).

    Coercion stackToString {n} (s: Stack n): string :=
      match s with
      | stack _ W32 n => "ws" ++ (nameSuffix n)
      | stack _ W64 n => "ds" ++ (nameSuffix n)
      end.

    Coercion memToString {n m} (s: Mem n m): string :=
      match s with
      | mem _ _ W32 v => "wm" ++ (nameSuffix v)
      | mem _ _ W64 v => "dm" ++ (nameSuffix v)
      end.

    Coercion stringToSome (x: string): option string := Some x.

    Definition stackLocation {n} (s: Stack n): word 32 :=
      combine (natToWord 8 n) (natToWord 24 n).

    Definition assignmentToString (a: Assignment): option string :=
      let f := fun x => if (Nat.eq_dec x 32) then "32" else "64" in
      match a with
      | ARegStack n r s => r ++ " = *(int" ++ f n ++ " *)" ++ s
      | AStackReg n s r => "*(int" ++ f n ++ " *) " ++ s ++ " = " ++ r
      | ARegMem n m r v i => r ++ " = " ++ "*(int" ++ f n ++ " *) (" ++ v ++ " + " ++ i ++ ")"
      | AMemReg n m v i r => "*(int" ++ f n ++ " *) (" ++ v ++ " + " ++ i ++ ") = " ++ r
      | ARegReg n a b => a ++ " = " ++ b
      | AConstInt n r c => r ++ " = " ++ c
      end.

    Coercion intOpToString (b: IntOp): string :=
      match b with
      | Add => "+"
      | Sub => "-"
      | Xor => "^"
      | And => "&"
      | Or => "|"
      end.

    Coercion dualOpToString (b: DualOp): string :=
      match b with
      | Mult => "*"
      end.

    Coercion carryOpToString (b: CarryOp): string :=
      match b with
      | AddWithCarry => "+"
      end.
 
    Coercion rotOpToString (r: RotOp): string :=
      match r with
      | Shl => "<<"
      | Shr => ">>"
      end.
 
    Definition operationToString (op: Operation): option string :=
      let f := fun x => if (Nat.eq_dec x 32) then "32" else "64" in
      match op with
      | IOpConst n o r c => 
        r ++ " " ++ o ++ "= " ++ c
      | IOpReg n o a b =>
        a ++ " " ++ o ++ "= " ++ b
      | IOpMem n _ o a b i =>
        a ++ " " ++ o ++ "= *(int" ++ (f n) ++ "* " ++ b ++ " + " ++ i ++ ")"
      | IOpStack n o a b =>
        a ++ " " ++ o ++ "= " ++ b
      | DOp n o a b x =>
        match x with
        | Some r =>
          "inline " ++ r ++ " " ++ a ++ " " ++ o ++ "= " ++ b
        | None => a ++ " " ++ o ++ "= " ++ b
        end
      | COp n o a b =>
        a ++ " " ++ o ++ "= " ++ b
      | ROp n o r i =>
        r ++ " " ++ o ++ "= " ++ i
      end.

    Definition testOpToString (t: TestOp): bool * string :=
      match t with
      | TEq => (true, "=")
      | TLt => (true, "<")
      | TGt => (true, ">")
      | TLe => (false, ">")
      | TGe => (false, "<")
      end.

    Definition conditionalToString (c: Conditional): string * string :=
      match c with
      | CTrue => ("=? 0", "=") 
      | CZero n r => ("=? " ++ r, "=")
      | CReg n t a b => 
        match (testOpToString t) with
        | (true, s) =>
          (s ++ "? " ++ a ++ " - " ++ b, s)
        | (false, s) =>
          (s ++ "? " ++ a ++ " - " ++ b, "!" ++ s)
        end

      | CConst n t a b => 
        match (testOpToString t) with
        | (true, s) => 
          (s ++ "? " ++ a ++ " - " ++ b, s)
        | (false, s) =>
          (s ++ "? " ++ a ++ " - " ++ b, "!" ++ s)
        end
      end.

  End Elements.

  Section Parsing.
    Definition convM {n m} (x: list (Mapping n)): list (Mapping m).
      destruct (Nat.eq_dec n m); subst. exact x. exact [].
    Defined.

    Arguments regM [n] r.
    Arguments stackM [n] s.
    Arguments memM [n m] x i.
    Arguments constM [n] x.

    Fixpoint entries (width: nat) (prog: Program): list (Mapping width) :=
      match prog with
      | cons s next =>
        match s with
        | QAssign a =>
          match a with
          | ARegStack n r s => convM [regM r; stackM s]
          | AStackReg n s r => convM [regM r; stackM s]
          | ARegMem n m a b i => convM [regM a; memM b i]
          | AMemReg n m a i b => convM [memM a i; regM b]
          | ARegReg n a b => convM [regM a; regM b]
          | AConstInt n r c => convM [regM r; constM c]
          end
        | QOp o =>
          match o with
          | IOpConst _ o a c => convM [regM a; constM c]
          | IOpReg _ o a b => convM [regM a; regM b]
          | IOpStack _ o a b => convM [regM a; stackM b]
          | IOpMem _ _ o a b i => convM [regM a; memM b i]
          | DOp _ o a b (Some x) => convM [regM a; regM b; regM x]
          | DOp _ o a b None => convM [regM a; regM b]
          | ROp _ o a i => convM [regM a]
          | COp _ o a b => convM [regM a; regM b]
          end
        | QCond c _ =>
          match c with
          | CTrue => []
          | CZero n r => convM [regM r]
          | CReg n o a b => convM [regM a; regM b]
          | CConst n o a c => convM [regM a; constM c]
          end
        | _ => []
        end ++ (entries width next)
      | nil => nil
      end.

    Definition flatMapOpt {A B} (lst: list A) (f: A -> option B): list B :=
      fold_left
        (fun lst a => match (f a) with | Some x => cons x lst | _ => lst end)
        lst [].

    Definition flatMapList {A B} (lst: list A) (f: A -> list B): list B :=
      fold_left (fun lst a => lst ++ (f a)) lst [].

    Fixpoint dedup {n} (l : list (Mapping n)) : list (Mapping n) :=
      match l with
      | [] => []
      | x::xs =>
        if in_dec EvalUtil.mapping_dec x xs
        then dedup xs
        else x::(dedup xs)
      end.

    Definition getRegNames (n: nat) (lst: list (Mapping n)): list nat :=
      flatMapOpt (dedup lst) (fun e =>
        match e with | regM (reg _ _ x) => Some x | _ => None end).

    Definition getStackNames (n: nat) (lst: list (Mapping n)): list nat :=
      flatMapOpt (dedup lst) (fun e =>
        match e with | stackM (stack _ _ x) => Some x | _ => None end).

    Definition getMemNames (n: nat) (lst: list (Mapping n)): list nat :=
      flatMapOpt (dedup lst) (fun e =>
        match e with | memM _ (mem _ _ _ x) _ => Some x | _ => None end).

    Fixpoint getInputs' (n: nat) (prog: list QhasmStatement) (init: list (Mapping n)): list (Mapping n) :=
      let f := fun rs => filter (fun x =>
        negb (proj1_sig (bool_of_sumbool (in_dec EvalUtil.mapping_dec x init)))) rs in
      let g := fun {w} p => (@convM w n (fst p), @convM w n (snd p)) in
      match prog with
      | [] => []
      | cons p ps =>
        let requiredCommaUsed := match p with
        | QAssign a =>
          match a with
          | ARegStack n r s   => g ([stackM s], [regM r; stackM s])
          | AStackReg n s r   => g ([regM r], [regM r; stackM s])
          | ARegMem n m r x i => g ([memM x i], [regM r; memM x i])
          | AMemReg n m x i r => g ([regM r], [regM r; memM x i])
          | ARegReg n a b     => g ([regM b], [regM a; regM b])
          | AConstInt n r c   => g ([], [regM r])
          end
        | QOp o =>
          match o with
          | IOpConst _ o a c     => g ([regM a], [regM a])
          | IOpReg _ o a b       => g ([regM a], [regM a; regM b])
          | IOpStack _ o a b     => g ([regM a], [regM a; stackM b])
          | IOpMem _ _ o a b i   => g ([regM a], [regM a; memM b i])
          | DOp _ o a b (Some x) => g ([regM a; regM b], [regM a; regM b; regM x])
          | DOp _ o a b None     => g ([regM a; regM b], [regM a; regM b])
          | ROp _ o a i          => g ([regM a], [regM a])
          | COp _ o a b          => g ([regM a], [regM a; regM b])
          end
        | QCond c _ =>
          match c with
          | CTrue => ([], [])
          | CZero n r => g ([], [regM r])
          | CReg n o a b => g ([], [regM a; regM b])
          | CConst n o a c => g ([], [regM a])
          end
        | _ => ([], [])
        end in match requiredCommaUsed with
        | (r, u) => ((f r) ++ (getInputs' n ps ((f u) ++ init)))
        end
      end.

    Definition getInputs (n: nat) (prog: list QhasmStatement) := getInputs' n prog [].

    Definition mappingDeclaration {n} (x: Mapping n): option string :=
      match x with
      | regM (reg _ w x) =>
        match w with
        | W32 => Some ("int32 " ++ (reg w x))%string
        | W64 => Some ("int64 " ++ (reg w x))%string
        end

      | stackM (stack _ w x) =>
        match w with
        | W32 => Some ("stack32 " ++ (stack w x))%string
        | W64 => Some ("stack64 " ++ (stack w x))%string
        end

      | memM _ (mem _ m w x) _ =>
        match w with
        | W32 => Some ("stack32 " ++ (@mem _ m w x))%string
        | W64 => Some ("stack64 " ++ (@mem _ m w x))%string
        end

      | _ => None
      end.

    Definition inputDeclaration {n} (x: Mapping n): option string :=
      match x with
      | regM r => Some ("input " ++ r)%string
      | stackM s => Some ("input " ++ s)%string
      | memM _ m i => Some ("input " ++ m)%string
      | _ => None
      end.

  End Parsing.

  (* Macroscopic Conversion Methods *)
  Definition optionToList {A} (o: option A): list A :=
    match o with
    | Some a => [a]
    | None => []
    end.

  Definition convertStatement (statement: QhasmStatement): list string :=
    match statement with
    | QAssign a => optionToList (assignmentToString a)
    | QOp o => optionToList (operationToString o)
    | QCond c l =>
      match (conditionalToString c) with
      | (s1, s2) =>
        let s' := ("goto lbl" ++ l ++ " if " ++ s2)%string in
        [s1; s']
      end
    | QLabel l => [("lbl" ++ l ++ ": ")%string]
    | QCall l => [("push %eip+2")%string; ("goto" ++ l)%string]
    | QRet => [("pop %eip")%string]
    end.

  Definition convertProgram (prog: Qhasm.Program): option string :=
    let decls := fun x => flatMapList (dedup (entries x prog))
      (compose optionToList mappingDeclaration) in

    let inputs := fun x => flatMapList (getInputs x prog)
      (compose optionToList inputDeclaration) in

    let stmts := (flatMapList prog convertStatement) in
    let enter := [("enter prog")%string] in
    let leave := [("leave")%string] in
    let blank := [EmptyString] in
    let newline := String (ascii_of_nat 10) EmptyString in

    Some (fold_left (fun x y => (x ++ newline ++ y)%string)
      (decls 32 ++ inputs 32 ++
       decls 64 ++ inputs 64 ++ blank ++
       enter ++ blank ++
       stmts ++ blank ++
       leave ++ blank) EmptyString).

  Lemma convert_spec: forall a a' b b' prog prog',
    convertProgram prog = Some prog' ->
    convertState a = Some a' -> convertState b = Some b' ->
    QhasmString.evaluatesTo prog' a b <-> Qhasm.evaluatesTo prog a' b'.
  Admitted.

End StringConversion.
