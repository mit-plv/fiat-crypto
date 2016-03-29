
Require Import String List.
Require Import Bedrock.Word.
Require Import ZArith NArith NPeano.
Require Import Coq.Structures.OrderedTypeEx.

Require Import FMapAVL FMapList.

Module NatM := FMapAVL.Make(Nat_as_OT).
Definition DefMap: Type := NatM.t N.
Definition StateMap: Type := NatM.t DefMap.
Definition LabelMap: Type := NatM.t nat.

(* A formalization of x86 qhasm *)

(* Basic Types *)
Definition Label := nat.
Definition Index (limit: nat) := {x: nat | (x < limit)%nat}.
Definition Invert := bool.

Definition indexToNat {lim: nat} (i: Index lim): nat := proj1_sig i.
Coercion indexToNat : Index >-> nat.

(* A constant upper-bound on the number of operations we run *)
Definition maxOps: nat := 1000.

(* Datatypes *)
Inductive Const: nat -> Set :=
  | const32: word 32 -> Const 32
  | const64: word 64 -> Const 64
  | const128: word 128 -> Const 128.

Inductive Reg: nat -> Set :=
  | reg32: nat -> Reg 32
  | reg3232: nat -> Reg 64
  | reg6464: nat -> Reg 128
  | reg80: nat -> Reg 80.

Inductive Stack: nat -> Set :=
  | stack32: nat -> Stack 32
  | stack64: nat -> Stack 64
  | stack128: nat -> Stack 128.

(* Assignments *)
Inductive Assignment : Set :=
  | Assign32Stack32: Reg 32 -> Stack 32 -> Assignment
  | Assign32Stack16: Reg 32 -> Stack 32 -> Index 2 -> Assignment
  | Assign32Stack8: Reg 32 -> Stack 32 -> Index 4 -> Assignment
  | Assign32Stack64: Reg 32 -> Stack 64 -> Index 2 -> Assignment
  | Assign32Stack128: Reg 32 -> Stack 128 -> Index 2 -> Assignment

  | Assign32Reg32: Reg 32 -> Reg 32 -> Assignment
  | Assign32Reg16: Reg 32 -> Reg 32 -> Index 2 -> Assignment
  | Assign32Reg8: Reg 32 -> Reg 32 -> Index 4 -> Assignment
  | Assign32Reg64: Reg 32 -> Reg 64 -> Index 2 -> Assignment
  | Assign32Reg128: Reg 32 -> Reg 128 -> Index 4 -> Assignment

  | Assign3232Stack32: Reg 64 -> Index 2 -> Stack 32 -> Assignment
  | Assign3232Stack64: Reg 64 -> Stack 64 -> Assignment
  | Assign3232Stack128: Reg 64 -> Stack 128 -> Index 2 -> Assignment

  | Assign3232Reg32: Reg 64 -> Index 2 -> Reg 32 -> Assignment
  | Assign3232Reg64: Reg 64 -> Reg 64 -> Assignment
  | Assign3232Reg128: Reg 64 -> Reg 128 -> Index 2 -> Assignment

  | Assign6464Reg32: Reg 128 -> Index 4 -> Reg 32 -> Assignment
  | Assign6464Reg64: Reg 128 -> Index 2 -> Reg 64 -> Assignment
  | Assign6464Reg128: Reg 128 -> Reg 128 -> Assignment

  | AssignConstant: Reg 32 -> Const 32 -> Assignment.

Hint Constructors Assignment.

(* Operations *)

Inductive BinOp :=
  | Plus: BinOp | Minus: BinOp | Mult: BinOp
  | Div: BinOp | Xor: BinOp | And: BinOp | Or: BinOp.

Inductive RotOp :=
  | Shl: RotOp | Shr: RotOp | Rotl: RotOp | Rotr: RotOp.

Inductive Operation :=
  | OpReg32Constant: BinOp -> Reg 32 -> Const 32 -> Operation
  | OpReg32Reg32: BinOp -> Reg 32 -> Reg 32 -> Operation
  | RotReg32: RotOp -> Reg 32 -> Index 32 -> Operation

  | OpReg64Constant: BinOp -> Reg 64 -> Const 64 -> Operation
  | OpReg64Reg64: BinOp -> Reg 64 -> Reg 64 -> Operation

  | OpReg128Constant: BinOp -> Reg 128 -> Const 32 -> Operation
  | OpReg128Reg128: BinOp -> Reg 128 -> Reg 128 -> Operation.

Hint Constructors Operation.

(* Control Flow *)

Inductive TestOp :=
  | TEq: TestOp
  | TLt: TestOp
  | TUnsignedLt: TestOp
  | TGt: TestOp
  | TUnsignedGt: TestOp.

Inductive Conditional :=
  | TestTrue: Conditional
  | TestFalse: Conditional
  | TestReg32Reg32: TestOp -> Invert -> Reg 32 -> Reg 32 -> Conditional
  | TestReg32Const: TestOp -> Invert -> Reg 32 -> Const 32 -> Conditional.

Definition invertConditional (c: Conditional): Conditional :=
  match c with
  | TestTrue => TestFalse
  | TestFalse => TestFalse
  | TestReg32Reg32 o i r0 r1 => TestReg32Reg32 o (negb i) r0 r1
  | TestReg32Const o i r c => TestReg32Const o (negb i) r c
  end.

Hint Constructors Conditional.

(* Program Types *)

Inductive AlmostQhasm :=
  | ASeq: AlmostQhasm -> AlmostQhasm -> AlmostQhasm
  | AAssign: Assignment -> AlmostQhasm
  | AOp: Operation -> AlmostQhasm 
  | ACond: Conditional -> AlmostQhasm -> AlmostQhasm
  | AWhile: Conditional -> AlmostQhasm -> AlmostQhasm.

Hint Constructors AlmostQhasm.

Inductive QhasmStatement :=
  | QAssign: Assignment -> QhasmStatement
  | QOp: Operation -> QhasmStatement
  | QJmp: Conditional -> Label -> QhasmStatement
  | QLabel: Label -> QhasmStatement.

Hint Constructors QhasmStatement.

Definition Qhasm := list QhasmStatement.

Import ListNotations.

(* AlmostQhasm -> Qhasm Conversion *)

Fixpoint almostToQhasm' (prog: AlmostQhasm) (startLabel: N): Qhasm :=
  let label0 := N.shiftl 1 startLabel in
  let label1 := N.succ label0 in

  match prog with
  | ASeq a b => (almostToQhasm' a label0) ++ (almostToQhasm' b label1)
  | AAssign a => [ QAssign a ]
  | AOp a => [ QOp a ]
  | ACond c a =>
    [QJmp (invertConditional c) (N.to_nat label0)] ++
    (almostToQhasm' a label1) ++
    [QLabel (N.to_nat label0)]
  | AWhile c a =>
    let start := N.to_nat (N.shiftl 1 label0) in
    let finish := S start in
    [ QJmp (invertConditional c) finish ;
      QLabel start ] ++
      (almostToQhasm' a label1) ++
    [ QJmp c start;
      QLabel finish ]
  end.

Definition almostToQhasm (prog: AlmostQhasm) := almostToQhasm' prog 0%N.

(* Machine State *)

Inductive State :=
| fullState (regState: StateMap) (stackState: StateMap): State.

Definition getReg {n} (reg: Reg n) (state: State): option (word n).
  destruct state; inversion reg as [L H | L H | L H | L H];
    destruct (NatM.find n regState) as [map |];
    first [ destruct (NatM.find L map) as [n0 |] | exact None ];
    first [ rewrite H; exact (Some (NToWord n n0)) | exact None ].
Defined.

Definition setReg {n} (reg: Reg n) (value: word n) (state: State): State.
  inversion state; inversion reg as [L H | L H | L H | L H];
    destruct (NatM.find n regState) as [map |];
    first [
       exact
         (fullState
           (NatM.add n
             (NatM.add L (wordToN value) map) regState)
             stackState)
     | exact state ].
Defined.

Definition getStack {n} (entry: Stack n) (state: State): option (word n).
  destruct state; inversion entry as [L H | L H | L H];
    destruct (NatM.find n stackState) as [map |];
    first [ destruct (NatM.find L map) as [n0 |] | exact None ];
    first [ rewrite H; exact (Some (NToWord n n0)) | exact None ].
Defined.

Definition setStack {n} (entry: Stack n) (value: word n) (state: State): State.
  inversion state; inversion entry as [L H | L H | L H];
    destruct (NatM.find n stackState) as [map |];
    first [
       exact
         (fullState regState
           (NatM.add n
             (NatM.add L (wordToN value) map) regState))
     | exact state ].
Defined.

Definition emptyState: State :=
  fullState (NatM.empty DefMap) (NatM.empty DefMap).

(* Magical Bitwise Manipulations *)

(* Force w to be m bits long, by truncation or zero-extension *)
Definition trunc {n} (m: nat) (w: word n): word m.
  destruct (lt_eq_lt_dec n m) as [s|s]; try destruct s as [s|s].

  - replace m with (n + (m - n)) by abstract intuition.
    refine (zext w (m - n)).

  - rewrite <- s; assumption.

  - replace n with (m + (n - m)) in w by abstract intuition.
    refine (split1 m (n-m) w).
Defined.

(* Get the index-th m-bit block of w *)
Definition getIndex {n} (w: word n) (m index: nat): word m.
  replace n with
    ((min n (m * index)) + (n - (min n (m * index))))%nat
    in w by abstract (
      assert ((min n (m * index)) <= n)%nat
        by apply Nat.le_min_l;
      intuition).

  refine
    (trunc m
      (split2 (min n (m * index)) (n - min n (m * index)) w)).
Defined.

(* set the index-th m-bit block of w to s *)
Definition setInPlace {n m} (w: word n) (s: word m) (index: nat): word n :=
  w ^& (wnot (trunc n (combine (wones m) (wzero (index * m)%nat))))
    ^| (trunc n (combine s (wzero (index * m)%nat))).

(* State Evaluation *)

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

Definition evalOperation (o: Operation) (state: State): State :=
  match o with
  | OpReg32Constant b r c =>
    match (getReg r state) with
    | Some v0 =>
      match c with
      | const32 v1 => setReg r (evalBinOp b v0 v1) state
      | _ => state
      end
    | None => state
    end
  | OpReg32Reg32 b r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (evalBinOp b v0 v1) state
      | _ => state
      end
    | None => state
    end
  | RotReg32 b r m =>
    match (getReg r state) with
    | Some v0 => setReg r (evalRotOp b v0 m) state
    | None => state
    end

  | OpReg64Constant b r c =>
    match (getReg r state) with
    | Some v0 =>
      match c with
      | const64 v1 => setReg r (evalBinOp b v0 v1) state
      | _ => state
      end
    | None => state
    end
  | OpReg64Reg64 b r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (evalBinOp b v0 v1) state
      | _ => state
      end
    | None => state
    end

  | OpReg128Constant b r c =>
    match (getReg r state) with
    | Some v0 =>
      match c with
      | const128 v1 => setReg r (evalBinOp b v0 v1) state
      | _ => state
      end
    | None => state
    end
  | OpReg128Reg128 b r0 r1 => 
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (evalBinOp b v0 v1) state
      | _ => state
      end
    | None => state
    end
  end.

Definition evalAssignment (a: Assignment) (state: State): State :=
  match a with
  | Assign32Stack32 r s =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r v1 state
      | _ => state
      end
    | None => state
    end
  | Assign32Stack16 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (trunc 32 (getIndex v1 16 i)) state
      | _ => state
      end
    | None => state
    end
  | Assign32Stack8 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (trunc 32 (getIndex v1 8 i)) state
      | _ => state
      end
    | None => state
    end
  | Assign32Stack64 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (getIndex v1 32 i) state
      | _ => state
      end
    | None => state
    end
  | Assign32Stack128 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (getIndex v1 32 i) state
      | _ => state
      end
    | None => state
    end

  | Assign32Reg32 r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 v1 state
      | _ => state
      end
    | None => state
    end
  | Assign32Reg16 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (trunc 32 (getIndex v1 16 i)) state
      | _ => state
      end
    | None => state
    end
  | Assign32Reg8 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (trunc 32 (getIndex v1 8 i)) state
      | _ => state
      end
    | None => state
    end
  | Assign32Reg64 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (getIndex v1 32 i) state
      | _ => state
      end
    | None => state
    end
  | Assign32Reg128 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (getIndex v1 32 i) state
      | _ => state
      end
    | None => state
    end

  | Assign3232Stack32 r0 i s =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => state
      end
    | None => state
    end

  | Assign3232Stack64 r s =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r v1 state
      | _ => state
      end
    | None => state
    end

  | Assign3232Stack128 r s i =>
    match (getReg r state) with
    | Some v0 =>
      match (getStack s state) with
      | Some v1 => setReg r (getIndex v1 64 i) state
      | _ => state
      end
    | None => state
    end

  | Assign3232Reg32 r0 i r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => state
      end
    | None => state
    end

  | Assign3232Reg64 r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 v1 state
      | _ => state
      end
    | None => state
    end

  | Assign3232Reg128 r0 r1 i =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (getIndex v1 64 i) state
      | _ => state
      end
    | None => state
    end

  | Assign6464Reg32 r0 i r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => state
      end
    | None => state
    end

  | Assign6464Reg64 r0 i r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 (setInPlace v0 v1 i) state
      | _ => state
      end
    | None => state
    end

  | Assign6464Reg128 r0 r1 =>
    match (getReg r0 state) with
    | Some v0 =>
      match (getReg r1 state) with
      | Some v1 => setReg r0 v1 state
      | _ => state
      end
    | None => state
    end

  | AssignConstant r c =>
    match (getReg r state) with
    | Some v0 =>
      match c with
      | const32 v1 => setReg r v1 state
      | _ => state
      end
    | None => state
    end
  end.

(* AlmostQhasm Evaluation *)


(* Only execute while loops a fixed number of times.
   TODO (rsloan): can we do any better? *)

Fixpoint almostEvalWhile (cond: Conditional) (prog: AlmostQhasm) (state: State) (horizon: nat): State :=
  match horizon with
  | (S m) => 
    if (evalCond cond state)
    then almostEvalWhile cond prog state m
    else state 
  | O => state
  end.

Fixpoint almostEval (prog: AlmostQhasm) (state: State): State :=
  match prog with
  | ASeq a b => almostEval b (almostEval a state)
  | AAssign a => evalAssignment a state
  | AOp a => evalOperation a state
  | ACond c a =>
    if (evalCond c state)
    then almostEval a state
    else state 
  | AWhile c a => almostEvalWhile c a state maxOps
  end.

Definition almostEvalReg {n} (prog: AlmostQhasm) (reg: Reg n): option (word n) :=
  getReg reg (almostEval prog emptyState).

Definition almostEvalStack {n} (prog: AlmostQhasm) (stack: Stack n): option (word n) :=
  getStack stack (almostEval prog emptyState).

(* Qhasm Evaluation *)

Fixpoint getLabelMap' (prog: Qhasm) (cur: LabelMap) (index: nat): LabelMap :=
  match prog with
  | p :: ps =>
    match p with
    | QLabel label => getLabelMap' ps (NatM.add label index cur) (S index)
    | _ => getLabelMap' ps cur (S index)
    end
  | [] => cur
  end.

Definition getLabelMap (prog: Qhasm): LabelMap :=
  getLabelMap' prog (NatM.empty nat) O.

Fixpoint eval' (prog: Qhasm) (state: State) (loc: nat) (horizon: nat) (labelMap: LabelMap) (maxLoc: nat): option State :=
  match horizon with
  | (S h) =>
    match (nth_error prog loc) with
    | Some stmt =>
      let (nextState, jmp) :=
        match stmt with
        | QAssign a => (evalAssignment a state, None)
        | QOp o => (evalOperation o state, None)
        | QLabel l => (state, None)
        | QJmp c l =>
          if (evalCond c state)
          then (state, Some l)
          else (state, None)
        end
      in
        match jmp with
        | None =>
          if (Nat.eq_dec loc maxLoc)
          then Some nextState
          else eval' prog nextState (S loc) h labelMap maxLoc
        | Some nextLoc =>
          eval' prog nextState nextLoc h labelMap nextLoc
        end
    | None => None
    end
  | O => None
  end.

Definition eval (prog: Qhasm) (state: State): option State :=
  eval' prog state O maxOps (getLabelMap prog) ((length prog) - 1).

Definition evalReg {n} (prog: Qhasm) (reg: Reg n): option (word n) :=
  match (eval prog emptyState) with
  | Some st => getReg reg st
  | None => None
  end.

Definition evalStack {n} (prog: Qhasm) (stack: Stack n): option (word n) :=
  match (eval prog emptyState) with
  | Some st => getStack stack st
  | None => None
  end.

(* world peace *)
