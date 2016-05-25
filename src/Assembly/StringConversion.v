Require Export Language Conversion.
Require Import QhasmCommon QhasmEvalCommon QhasmUtil Qhasm.
Require Export String Ascii.
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

    Coercion intConstToString {n} (c: IConst n): string :=
      match c with
      | constInt32 w => "0x" ++ w
      | constInt64 w => "0x" ++ w
      end.

    Coercion intRegToString {n} (r: IReg n): string :=
      match r with
      | regInt32 n => "w" ++ (nameSuffix n)
      | regInt64 n => "w" ++ (nameSuffix n)
      end.

    Coercion natToString (n: nat): string :=
      "0x" ++ (nToHex (N.of_nat n)).

    Coercion stackToString {n} (s: Stack n): string :=
      match s with
      | stack32 n => "ss" ++ (nameSuffix n)
      | stack64 n => "ls" ++ (nameSuffix n)
      | stack128 n => "qs" ++ (nameSuffix n)
      end.

    Coercion stringToSome (x: string): option string := Some x.

    Definition stackLocation {n} (s: Stack n): word 32 :=
      combine (natToWord 8 n) (natToWord 24 n).

    Definition assignmentToString (a: Assignment): option string :=
      let f := fun x => if (Nat.eq_dec x 32) then "32" else "64" in
      match a with
      | ARegStackInt n r s => r ++ " = *(int" ++ f n ++ " *)" ++ s
      | AStackRegInt n s r => "*(int" ++ f n ++ " *) " ++ s ++ " = " ++ r
      | ARegRegInt n a b => a ++ " = " ++ b
      | AConstInt n r c => r ++ " = " ++ c
      | AIndex n m a b i =>
        a ++ " = *(int" ++ f n ++ " *) (" ++ b ++ " + " ++ (m/n) ++ ")"
      | APtr n r s => r ++ " = " ++ s
      end.

    Coercion intOpToString (b: IntOp): string :=
      match b with
      | IPlus => "+"
      | IMinus => "-"
      | IXor => "^"
      | IAnd => "&"
      | IOr => "|"
      end.

    Coercion dualOpToString (b: DualOp): string :=
      match b with
      | IMult => "*"
      end.
 
    Coercion rotOpToString (r: RotOp): string :=
      match r with
      | Shl => "<<"
      | Shr => ">>"
      end.
 
    Definition operationToString (op: Operation): option string :=
      match op with
      | IOpConst n o r c => 
        r ++ " " ++ o ++ "= " ++ c
      | IOpReg n o a b =>
        a ++ " " ++ o ++ "= " ++ b
      | DOpReg n o a b x =>
        match x with
        | Some r =>
          "inline " ++ r ++ " " ++ a ++ " " ++ o ++ "= " ++ b
        | None => a ++ " " ++ o ++ "= " ++ b
        end
      | OpRot n o r i =>
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
      | TestTrue => ("=? 0", ">") (* these will be elided later on*)
      | TestFalse => (">? 0", ">")
      | TestInt n o a b =>
        match (testOpToString o) with
        | (true, s) =>
          (s ++ "? " ++ a ++ " - " ++ b, s)
        | (false, s) =>
          ("!" ++ s ++ "? " ++ a ++ " - " ++ b, "!" ++ s)
        end
      end.

  End Elements.

  Section Parsing.
    Inductive Entry :=
      | intEntry: forall n, IReg n -> Entry
      | stackEntry: forall n, Stack n -> Entry.

    Definition entryId (x: Entry): nat * nat * nat :=
      match x with
      | intEntry n (regInt32 v) => (0, n, v)
      | intEntry n (regInt64 v) => (1, n, v)
      | stackEntry n (stack32 v) => (2, n, v)
      | stackEntry n (stack64 v) => (3, n, v)
      | stackEntry n (stack128 v) => (4, n, v)
      end.

    Lemma id_equal: forall {x y}, x = y <-> entryId x = entryId y.
    Proof.
      intros; split; intros;
        destruct x as [nx x | nx x];
        destruct y as [ny y | ny y];
        try rewrite H;

        destruct x, y; subst;
        destruct (Nat.eq_dec n n0); subst;

        simpl in H; inversion H; intuition.
    Qed.

    Definition entry_dec (x y: Entry): {x = y} + {x <> y}.
      refine (_ (triple_dec (entryId x) (entryId y))).
      intros; destruct x0.

      - left; abstract (apply id_equal in e; intuition).
      - right; abstract (intro; apply id_equal in H; intuition).
    Defined.

    Fixpoint entries (prog: Program): list Entry :=
      match prog with
      | cons s next =>
        match s with
        | QAssign a =>
          match a with
          | ARegStackInt n r s => [intEntry n r; stackEntry n s]
          | AStackRegInt n s r => [intEntry n r; stackEntry n s]
          | ARegRegInt n a b => [intEntry n a; intEntry n b]
          | AConstInt n r c => [intEntry n r]
          | AIndex n m a b i => [intEntry n a; stackEntry m b]
          | APtr n r s => [intEntry 32 r; stackEntry n s]
          end
        | QOp o =>
          match o with
          | IOpConst n o r c => [intEntry n r]
          | IOpReg n o a b => [intEntry n a; intEntry n b]
          | DOpReg n o a b x =>
            match x with
            | Some r =>
              [intEntry n a; intEntry n b; intEntry n r]
            | None =>
              [intEntry n a; intEntry n b]
            end
          | OpRot n o r i => [intEntry n r]
          end
        | QJmp c _ =>
          match c with
          | TestInt n o a b => [intEntry n a; intEntry n b]
          | _ => []
          end
        | QLabel _ => []
        end ++ (entries next)
      | nil => nil
      end.

    Definition flatMapOpt {A B} (lst: list A) (f: A -> option B): list B :=
      fold_left
        (fun lst a => match (f a) with | Some x => cons x lst | _ => lst end)
        lst [].

    Definition flatMapList {A B} (lst: list A) (f: A -> list B): list B :=
      fold_left (fun lst a => lst ++ (f a)) lst [].

    Fixpoint dedup (l : list Entry) : list Entry :=
      match l with
      | [] => []
      | x::xs =>
        if in_dec entry_dec x xs
        then dedup xs
        else x::(dedup xs)
      end.

    Definition everyIReg32 (lst: list Entry): list (IReg 32) :=
      flatMapOpt (dedup lst) (fun e =>
        match e with | intEntry 32 r => Some r | _ => None end).

    Definition everyIReg64 (lst: list Entry): list (IReg 64) :=
      flatMapOpt (dedup lst) (fun e =>
        match e with | intEntry 64 r => Some r | _ => None end).

    Definition everyStack (n: nat) (lst: list Entry): list (Stack n).
      refine (flatMapOpt (dedup lst) (fun e =>
        match e with
        | stackEntry n' r =>
          if (Nat.eq_dec n n') then Some (convert r _) else None
        | _ => None
        end)); subst; reflexivity.
    Defined.

    Fixpoint getUsedBeforeInit' (prog: list QhasmStatement) (init: list Entry): list Entry :=
      let f := fun rs => filter (fun x => proj1_sig (bool_of_sumbool (in_dec entry_dec x init))) rs in
      match prog with
      | [] => []
      | cons p ps =>
        let requiredCommaUsed := match p with
        | QAssign a =>
          match a with
          | ARegStackInt n r s =>
            let re := intEntry n r in
            let se := stackEntry n s in
            ([se], [re; se])

          | AStackRegInt n s r =>
            let re := intEntry n r in
            let se := stackEntry n s in
            ([re], [re; se])

          | ARegRegInt n a b =>
            let ae := intEntry n a in
            let be := intEntry n b in
            ([be], [ae; be])

          | AConstInt n r c =>
            let re := intEntry n r in
            ([], [re])

          | AIndex n m a b i =>
            let ae := intEntry n a in
            let be := stackEntry m b in
            ([be], [ae; be])

          | APtr n r s =>
            let re := intEntry 32 r in
            let se := stackEntry n s in
            ([se], [re; se])
          end
        | QOp o =>
          match o with
          | IOpConst n o r c =>
            let re := intEntry n r in
            ([re], [re])

          | IOpReg n o a b =>
            let ae := intEntry n a in
            let be := intEntry n b in
            ([ae; be], [ae; be])

          | DOpReg n o a b x =>
            let ae := intEntry n a in
            let be := intEntry n b in

            match x with
            | Some r =>
              let xe := intEntry n r in
              ([ae; be], [ae; be; xe])
            | None => ([ae; be], [ae; be])
            end

          | OpRot n o r i =>
            let re := intEntry n r in
            ([re], [re])
          end
        | QJmp c _ =>
          match c with
          | TestInt n o a b =>
            let ae := intEntry n a in
            let be := intEntry n b in
            ([ae; be], [])

          | _ => ([], [])
          end
        | QLabel _ => ([], [])
        end in
        match requiredCommaUsed with
        | (r, u) =>
          ((f r) ++ (getUsedBeforeInit' ps ((f u) ++ init)))
        end
      end.

    Definition getUsedBeforeInit (prog: list QhasmStatement) := getUsedBeforeInit' prog [].

    Definition entryToString (e: Entry) :=
      match e with
      | intEntry n i => intRegToString i
      | stackEntry n s => stackToString s
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
    | QJmp c l =>
      match (conditionalToString c) with
      | (s1, s2) =>
        let s' := ("goto lbl" ++ l ++ " if " ++ s2)%string in
        [s1; s']
      end
    | QLabel l => [("lbl" ++ l ++ ": ")%string]
    end.

  Definition convertProgram (prog: Qhasm.Program): option string :=
    let es := (entries prog) in

    let ireg32s :=
        (map (fun x => "int32 " ++ (intRegToString x))%string
             (everyIReg32 es)) in
    let ireg64s :=
        (map (fun x => "int64 " ++ (intRegToString x))%string
             (everyIReg64 es)) in

    let stack32s :=
        (map (fun x => "stack32 " ++ (stackToString x))%string
             (everyStack 32 es)) in
    let stack64s := 
        (map (fun x => "stack64 " ++ (stackToString x))%string
             (everyStack 64 es)) in
    let stack128s := 
        (map (fun x => "stack128 " ++ (stackToString x))%string
             (everyStack 128 es)) in

    let inputs :=
        (map (fun x => "input " ++ (entryToString x))%string
             (getUsedBeforeInit prog)) in

    let stmts := (flatMapList prog convertStatement) in

    let enter := [("enter prog")%string] in
    let leave := [("leave")%string] in

    let blank := [EmptyString] in
    let newline := String (ascii_of_nat 10) EmptyString in

    Some (fold_left (fun x y => (x ++ newline ++ y)%string)
      (ireg32s ++ blank ++
       ireg64s ++ blank ++
       stack32s ++ blank ++
       stack64s ++ blank ++
       stack128s ++ blank ++
       inputs ++ blank ++ blank ++
       enter ++ blank ++
       stmts ++ blank ++ blank ++
       leave) EmptyString).

  Lemma convert_spec: forall a a' b b' prog prog',
    convertProgram prog = Some prog' ->
    convertState a = Some a' -> convertState b = Some b' ->
    QhasmString.evaluatesTo prog' a b <-> Qhasm.evaluatesTo prog a' b'.
  Admitted.

End StringConversion.
