Require Export QhasmCommon QhasmUtil State.
Require Export ZArith.
Require Export Bedrock.Word.

Import State.
Import Util.

Definition evalTest {n} (o: TestOp) (invert: bool) (a b: word n): bool :=
  xorb invert
  match o with
  | TEq => weqb a b
  | TLt =>
    match (Z.compare (wordToZ a) (wordToZ b)) with
    | Lt => true
    | _ => false
    end
  | TUnsignedLt =>
    match (N.compare (wordToN a) (wordToN b)) with
    | Lt => true
    | _ => false
    end
  | TGt =>
    match (Z.compare (wordToZ a) (wordToZ b)) with
    | Gt => true
    | _ => false
    end
  | TUnsignedGt =>
    match (N.compare (wordToN a) (wordToN b)) with
    | Gt => true
    | _ => false
    end
  end.

Definition evalCond (c: Conditional) (state: State): option bool :=
  match c with
  | TestTrue => Some true
  | TestFalse => Some false
  | TestReg32Reg32 o i r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r0 state) with
      | Some v1 => Some (evalTest o i v0 v1)
      | _ => None
      end
    | _ => None
    end
  | TestReg32Const o i r x =>
    match (getReg r state) with
    | Some v0 =>
      match x with
      | const32 v1 => Some (evalTest o i v0 v1)
      end
    | _ => None
    end
  end.

Definition evalBinOp {n} (o: BinOp) (a b: word n): word n :=
  match o with
  | Plus => wplus a b
  | Minus => wminus a b
  | Mult => wmult a b
  | Div => NToWord n ((wordToN a) / (wordToN b))%N
  | Or => wor a b
  | Xor => wxor a b
  | And => wand a b
  end.

Definition evalRotOp {n} (o: RotOp) (a: word n) (m: nat): word n :=
  match o with
  | Shl => NToWord n (N.shiftl_nat (wordToN a) m)
  | Shr => NToWord n (N.shiftr_nat (wordToN a) m)

  (* TODO (rsloan): not actually rotate operations *)
  | Rotl => NToWord n (N.shiftl_nat (wordToN a) m)
  | Rotr => NToWord n (N.shiftr_nat (wordToN a) m)
  end.

Definition evalOperation (o: Operation) (state: State): option State :=
  match o with
  | OpReg32Constant b r c =>
    match (getReg r state) with
    | Some v0 =>
      match c with
      | const32 v1 => setReg r (evalBinOp b v0 v1) state
      end
    | None => None
    end

  | OpReg32Reg32 b r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (evalBinOp b v0 v1) state
      | _ => None
      end
    | None => None
    end

  | RotReg32 b r m =>
    match (getReg r state) with
    | Some v0 => setReg r (evalRotOp b v0 m) state
    | None => None
    end

  | OpReg64Constant b r c =>
    match (getReg r state) with
    | Some v0 =>
      match c with
      | const64 v1 => setReg r (evalBinOp b v0 v1) state
      end
    | None => None
    end

  | OpReg64Reg64 b r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (evalBinOp b v0 v1) state
      | _ => None
      end
    | None => None
    end

  (* Don't implement the 128-wide ops yet:
     I think x86 doesn't do them like this *)
  | _ => None end.

Definition evalAssignment (a: Assignment) (state: State): option State :=
  match a with
  | Assign32Stack32 r s =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r v1 state
      | _ => None
      end
    | None => None
    end

  | Assign32Stack16 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (trunc 32 (getIndex v1 16 i)) state
      | _ => None
      end
    | None => None
    end
  | Assign32Stack8 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (trunc 32 (getIndex v1 8 i)) state
      | _ => None
      end
    | None => None
    end
  | Assign32Stack64 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (getIndex v1 32 i) state
      | _ => None
      end
    | None => None
    end
  | Assign32Stack128 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (getIndex v1 32 i) state
      | _ => None
      end
    | None => None
    end

  | Assign32Reg32 r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 v1 state
      | _ => None
      end
    | None => None
    end
  | Assign32Reg16 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (trunc 32 (getIndex v1 16 i)) state
      | _ => None
      end
    | None => None
    end
  | Assign32Reg8 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (trunc 32 (getIndex v1 8 i)) state
      | _ => None
      end
    | None => None
    end
  | Assign32Reg64 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (getIndex v1 32 i) state
      | _ => None
      end
    | None => None
    end
  | Assign32Reg128 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (getIndex v1 32 i) state
      | _ => None
      end
    | None => None
    end

  | Assign3232Stack32 r0 i s =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => None
      end
    | None => None
    end

  | Assign3232Stack64 r s =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r v1 state
      | _ => None
      end
    | None => None
    end

  | Assign3232Stack128 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (getIndex v1 64 i) state
      | _ => None
      end
    | None => None
    end

  | Assign3232Reg32 r0 i r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => None
      end
    | None => None
    end

  | Assign3232Reg64 r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 v1 state
      | _ => None
      end
    | None => None
    end

  | Assign3232Reg128 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (getIndex v1 64 i) state
      | _ => None
      end
    | None => None
    end

  | Assign6464Reg32 r0 i r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => None
      end
    | None => None
    end

  | Assign6464Reg64 r0 i r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => None
      end
    | None => None
    end

  | Assign6464Reg128 r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 v1 state
      | _ => None
      end
    | None => None
    end

  | AssignConstant r c =>
    match (getReg r state) with
    | Some v0 =>
      match c with
      | const32 v1 => setReg r v1 state
      end
    | None => None
    end
  end.

