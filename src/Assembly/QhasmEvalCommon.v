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

Definition evalCond (c: Conditional) (state: State): option bool :=
  match c with
  | CTrue => Some true
  | CZero n r =>
    omap (getReg r state) (fun v =>
      if (Nat.eq_dec O (wordToNat v))
      then Some true
      else Some false) 
  | CReg n o a b =>
    omap (getReg a state) (fun va =>
      omap (getReg b state) (fun vb =>
        Some (evalTest o va vb)))
  | CConst n o a c => 
    omap (getReg a state) (fun va =>
      Some (evalTest o va (constValueW c)))
  end.

Definition evalIntOp {b} (io: IntOp) (x y: word b): (word b) * option bool :=
  match io with
  | Add =>
    let v := (wordToN x + wordToN y)%N in
    let c := (N.compare v (Npow2 b)) in

    match c as c' return c' = c -> _ with
    | Lt => fun _ => (NToWord b v, Some false)
    | _ => fun _ => (NToWord b v, Some true)
    end eq_refl

  | Sub => (wminus x y, None)
  | Xor => (wxor x y, None)
  | And => (wand x y, None)
  | Or => (wor x y, None)
  end.

Definition evalCarryOp {b} (io: CarryOp) (x y: word b) (c: bool): (word b) * bool :=
  match io with
  | AddWidthCarry =>
    let v := (wordToN x + wordToN y + (if c then 1%N else 0%N))%N in
    let c := (N.compare v (Npow2 b)) in

    match c as c' return c' = c -> _ with
    | Lt => fun _ => (NToWord b v, false)
    | _ => fun _ => (NToWord b v, true)
    end eq_refl
  end.

Definition evalDualOp {b} (duo: DualOp) (x y: word b) :=
  match duo with
  | Mult =>
    let v := (wordToN x * wordToN y)%N in
    let wres := NToWord (b + b) v in
    (split1 b b wres, split2 b b wres)
  end.

Definition evalRotOp {b} (ro: RotOp) (x: word b) (n: nat) :=
  match ro with
  | Shl => NToWord b (N.shiftl_nat (wordToN x) n)
  | Shr => NToWord b (N.shiftr_nat (wordToN x) n)
  end.

Definition evalOperation (o: Operation) (state: State): option State :=
  match o with
  | IOpConst _ o r c =>
    omap (getReg r state) (fun v =>
      let (v', co) := (evalIntOp o v (constValueW c)) in
      Some (setCarryOpt co (setReg r v' state)))

  | IOpReg _ o a b =>
    omap (getReg a state) (fun va =>
      omap (getReg b state) (fun vb =>
        let (v', co) := (evalIntOp o va vb) in
        Some (setCarryOpt co (setReg a v' state))))

  | IOpMem _ _ o r m i => 
    omap (getReg r state) (fun va =>
      omap (getMem m i state) (fun vb =>
        let (v', co) := (evalIntOp o va vb) in
        Some (setCarryOpt co (setReg r v' state))))

  | DOp _ o a b (Some x) => 
    omap (getReg a state) (fun va =>
      omap (getReg b state) (fun vb =>
        let (low, high) := (evalDualOp o va vb) in
        Some (setReg x high (setReg a low state))))

  | DOp _ o a b None => 
    omap (getReg a state) (fun va =>
      omap (getReg b state) (fun vb =>
        let (low, high) := (evalDualOp o va vb) in
        Some (setReg a low state)))

  | ROp _ o r i => 
    omap (getReg r state) (fun v =>
      let v' := (evalRotOp o v i) in
      Some (setReg r v' state))

  | COp _ o a b => 
    omap (getReg a state) (fun va =>
      omap (getReg b state) (fun vb =>
        match (getCarry state) with
        | None => None
        | Some c0 => 
          let (v', c') := (evalCarryOp o va vb c0) in
          Some (setCarry c' (setReg a v' state))
        end))
  end.

Definition evalAssignment (a: Assignment) (state: State): option State :=
  match a with
  | ARegMem _ _ r m i => 
    omap (getMem m i state) (fun v => Some (setReg r v state))
  | AMemReg _ _ m i r =>
    omap (getReg r state) (fun v => Some (setMem m i v state))
  | AStackReg _ a b =>
    omap (getReg b state) (fun v => Some (setStack a v state))
  | ARegStack _ a b =>
    omap (getStack b state) (fun v => Some (setReg a v state))
  | ARegReg _ a b => 
    omap (getReg b state) (fun v => Some (setReg a v state))
  | AConstInt _ r c =>
    Some (setReg r (constValueW c) state)
  end.
