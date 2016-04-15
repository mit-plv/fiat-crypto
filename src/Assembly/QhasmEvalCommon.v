Require Export QhasmCommon QhasmUtil State.
Require Export ZArith Sumbool.
Require Export Bedrock.Word.

Import State.
Import Util.

Definition evalTest {n} (o: TestOp) (a b: word n): bool :=
  let c := (N.compare (wordToN a) (wordToN b)) in

  let eqBit := match c with | Eq => true | _ => false end in
  let ltBit := match c with | Lt => true | _ => false end in
  let gtBit := match c with | Gt => true | _ => false end in

  match o with
  | TEq => eqBit
  | TLt => ltBit
  | TLe => orb (eqBit) (ltBit)
  | TGt => gtBit
  | TGe => orb (eqBit) (gtBit)
  end.

Definition evalCond (c: Conditional) (state: State): option bool.
  refine match c with
  | TestTrue => Some true
  | TestFalse => Some false
  | TestInt n t a b => 
    match (getIntReg a state) with
    | Some va =>
      match (getIntReg b state) with
      | Some vb => Some (evalTest t va vb)
      | _ => None
      end
    | _ => None
    end

  | TestFloat n t a b =>
    let aOpt := (getFloatReg a state) in
    let bOpt := convert (getFloatReg a state) _ in

    match aOpt with
    | Some va =>
      match bOpt with
      | Some vb => Some (evalTest t va vb)
      | _ => None
      end
    | _ => None
    end
  end; abstract (
    inversion a; inversion b;
    unfold aOpt, getFractionalBits;
    simpl; intuition).
Defined.

Definition evalOperation (o: Operation) (state: State): option State.
  refine (
  let evalIOp := fun {b} (io: IntOp) (x y: word b) =>
    match io with
    | IPlus => wplus x y
    | IMinus => wminus x y
    | IXor => wxor x y
    | IAnd => wand x y
    | IOr => wor x y
    end in

  let evalFOp := fun {b} (fo: FloatOp) (x y: word b) =>
    match fo with
    | FAnd => wand x y
    | FPlus => wplus x y
    | FMult => wmult x y
    end in

  let evalRotOp := fun {b} (ro: RotOp) (x: word b) (n: nat) =>
    match ro with
    | Shl => NToWord b (N.shiftl_nat (wordToN x) n)
    | Shr => NToWord b (N.shiftr_nat (wordToN x) n)
    end in

  let liftOpt := fun {A B C} (f: A -> B -> option C) (xo: option A) (yo: option B) =>
    match (xo, yo) with
    | (Some x, Some y) => f x y
    | _ => None
    end in

  match o with
  | IOpConst o r c =>
    liftOpt (fun x y => setIntReg r (evalIOp o x y) state)
      (getIntReg r state)
      (match c with | constInt32 v => Some v end)

  | IOpReg o a b =>
    liftOpt (fun x y => setIntReg a (evalIOp o x y) state)
      (getIntReg a state) (getIntReg b state)

  | FOpConst32 o r c =>
    liftOpt (fun x y => setFloatReg r (evalFOp o x y) state)
      (getFloatReg r state)
      (match c with | constFloat32 v => Some (convert v _) end)

  | FOpReg32 o a b =>
    liftOpt (fun x y => setFloatReg a (evalFOp o x y) state)
      (getFloatReg a state) (convert (getFloatReg b state) _)

  | FOpConst64 o r c =>
    liftOpt (fun x y => setFloatReg r (evalFOp o x y) state)
      (getFloatReg r state)
      (match c with | constFloat64 v => Some (convert v _) end)

  | FOpReg64 o a b =>
    liftOpt (fun x y => setFloatReg a (evalFOp o x y) state)
      (getFloatReg a state) (convert (getFloatReg b state) _)

  | OpRot o r i =>
   match (getIntReg r state) with
    | Some va => setIntReg r (evalRotOp o va i) state
    | None => None
    end
  end); abstract intuition.
Defined.

Definition getIConst {n} (c: IConst n): word n :=
  match c with
  | constInt32 v => v
  end.

Definition getFConst {n} (c: FConst n): word n :=
  match c with
  | constFloat32 v => v
  | constFloat64 v => v
  end.

Definition evalAssignment (a: Assignment) (state: State): option State :=
  let liftOpt := fun {A B} (f: A -> option B) (xo: option A) =>
    match xo with
    | (Some x') => f x'
    | _ => None
    end in

  match a with
  | ARegStackInt n r s =>
    liftOpt (fun x => setIntReg r x state) (getStack s state)

  | ARegStackFloat n r s =>
    liftOpt (fun x => setFloatReg r x state) (getStack s state)

  | AStackRegInt n s r =>
    liftOpt (fun x => setStack s x state) (getIntReg r state)

  | AStackRegFloat n s r =>
    liftOpt (fun x => setStack s x state) (getFloatReg r state)

  | ARegRegInt n a b =>
    liftOpt (fun x => setIntReg a x state) (getIntReg b state)

  | ARegRegFloat n a b =>
    liftOpt (fun x => setFloatReg a x state) (getFloatReg b state)

  | AConstInt n r c => setIntReg r (getIConst c) state

  | AConstFloat n r c => setFloatReg r (getFConst c) state

  | AIndex n m a b i =>
    match (getIntReg b state) with
    | Some v => setIntReg a (trunc n (getIndex v m i)) state
    | _ => None
    end

  | APtr n r s =>
    setIntReg r (NToWord 32 (N.of_nat (getStackIndex s))) state 
  end.
