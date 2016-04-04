Require Export String List Logic.
Require Export Bedrock.Word.

Require Import ZArith NArith NPeano.
Require Import Coq.Structures.OrderedTypeEx.
Require Import FMapAVL FMapList.
Require Import JMeq.

Require Import QhasmUtil.

Import ListNotations.

Module NatM := FMapAVL.Make(Nat_as_OT).
Definition DefMap: Type := NatM.t N.
Definition StateMap: Type := NatM.t DefMap.
Definition LabelMap: Type := NatM.t nat.

(* Sugar *)

Definition W := word 32.

Definition convert {A B: Type} (x: A) (H: A = B): B :=
 eq_rect A (fun B0 : Type => B0) x B H.

Ltac create X Y :=
  let H := fresh in (
    assert (exists X, X = Y) as H
      by (exists Y; abstract intuition);
    destruct H).

Obligation Tactic := abstract intuition.

(* A formalization of x86 qhasm *)

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
  | stack128: nat -> Stack 128
  | stack256: nat -> Stack 256
  | stack512: nat -> Stack 512.

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
  | TestFalse => TestTrue
  | TestReg32Reg32 o i r0 r1 => TestReg32Reg32 o (negb i) r0 r1
  | TestReg32Const o i r c => TestReg32Const o (negb i) r c
  end.

Hint Constructors Conditional.

(* Machine State *)

Inductive State :=
| fullState (regState: StateMap) (stackState: DefMap): State.

(* Reg, Stack, Const Utilities *)

Definition getRegWords {n} (x: Reg n) :=
  match x with
  | reg32 loc => 1
  | reg3232 loc => 2
  | reg6464 loc => 4
  | reg80 loc => 2
  end.

Definition getStackWords {n} (x: Stack n) :=
  match x with
  | stack32 loc => 1
  | stack64 loc => 2
  | stack128 loc => 4
  | stack256 loc => 8
  | stack512 loc => 16
  end.

Definition getRegIndex {n} (x: Reg n): nat :=
  match x with
  | reg32 loc => loc
  | reg3232 loc => loc
  | reg6464 loc => loc
  | reg80 loc => loc
  end.

Definition getStackIndex {n} (x: Stack n): nat :=
  match x with
  | stack32 loc => loc
  | stack64 loc => loc
  | stack128 loc => loc
  | stack256 loc => loc
  | stack512 loc => loc
  end.

(* State Manipulations *)

Definition getReg {n} (reg: Reg n) (state: State): option (word n) :=
  match state with
  | fullState regState stackState =>
    match (NatM.find n regState) with
      | Some map =>
        match (NatM.find (getRegIndex reg) map) with
        | Some m => Some (NToWord n m)
        | _ => None
        end
      | None => None
    end
  end.

Definition setReg {n} (reg: Reg n) (value: word n) (state: State): option State :=
  match state with
  | fullState regState stackState =>
    match (NatM.find n regState) with
      | Some map =>
        Some (fullState
          (NatM.add n (NatM.add (getRegIndex reg) (wordToN value) map)
            regState) stackState)
      | None => None
    end
  end.

(* Per-word Stack Operations *)
Definition getStack32 (entry: Stack 32) (state: State): option (word 32) :=
  match state with
  | fullState regState stackState =>
    match entry with
    | stack32 loc =>
      match (NatM.find loc stackState) with
      | Some n => Some (NToWord 32 n)
      | _ => None
      end
    end
  end.

Definition setStack32 (entry: Stack 32) (value: word 32) (state: State): option State :=
  match state with
  | fullState regState stackState =>
    match entry with
    | stack32 loc =>
      (Some (fullState regState
                       (NatM.add loc (wordToN value) stackState)))
    end
  end.

Notation "'cast' e" := (convert e _) (at level 20).

(* Iterating Stack Operations *)
Lemma getStackWords_spec: forall {n} (x: Stack n), n = 32 * (getStackWords x).
Proof. intros; destruct x; simpl; intuition. Qed.

Definition segmentStackWord {n} (x: Stack n) (w: word n): word (32 * (getStackWords x)).
  intros; destruct x; simpl; intuition.
Defined.

Definition desegmentStackWord {n} (x: Stack n) (w: word (32 * (getStackWords x))): word n.
  intros; destruct x; simpl; intuition.
Defined.

Inductive Either A B := | xleft: A -> Either A B | xright: B -> Either A B.

Definition getWords' {n} (st: (list (word 32)) * word (32 * n)) :
    Either (list (word 32)) ((list (word 32)) * word (32 * (n - 1))).

  destruct (Nat.eq_dec n 0) as [H | H];
    destruct st as [lst w].

  - refine (xleft _ _ lst).

  - refine (xright _ _
             (cons (split1 32 (32 * (n - 1)) (cast w)) lst,
             (split2 32 (32 * (n - 1)) (cast w)))); intuition.
Defined.

Program Fixpoint getWords'_iter (n: nat) (st: (list (word 32)) * word (32 * n)): list (word 32) :=
  match n with
  | O => fst st
  | S m =>
    match (getWords' st) with
    | xleft lst => lst
    | xright st => cast (getWords'_iter m st)
    end
  end.

Definition getWords {len} (wd: word (32 * len)): list (word 32) :=
  getWords'_iter len ([], wd).

Definition joinWordOpts_expandTerm {n} (w: word (32 + 32 * n)): word (32 * S n).
  replace (32 * S n) with (32 + 32 * n) by abstract intuition; assumption.
Defined.

Fixpoint joinWordOpts (wds: list (option (word 32))) (len: nat): option (word (32 * (length wds))).
  refine match len with
  | O => None
  | S len' =>
    match wds with
    | nil => None
    | (cons wo wos) =>
        match wo with
        | None => None
        | Some w =>
          let f := fun x =>
            match x with 
            | None => None
            | (Some joined) => Some (cast (combine w joined))
            end in

          f (joinWordOpts wos len')
        end
    end
  end; 
    try replace (Datatypes.length (wo :: wos))
           with (1 + (Datatypes.length wos))
             by abstract intuition;
    intuition.
Defined.

Definition setStack {n} (entry: Stack n) (value: word n) (state: State) : option State :=
  (fix setStack_iter (wds: list (word 32)) (nextLoc: nat) (state: State) :=
     match wds with
     | [] => Some state
     | w :: ws =>
       match (setStack32 (stack32 nextLoc) w state) with 
       | Some st' => setStack_iter ws (S nextLoc) st'
       | None => None
       end
     end) (getWords (segmentStackWord entry value)) (getStackIndex entry) state.

Fixpoint getStack_iter (rem: nat) (loc: nat) (state: State): list (option (word 32)) :=
  match rem with
  | O => []
  | (S rem') =>
    (getStack32 (stack32 loc) state) ::
      (getStack_iter rem' (loc + 32) state)
  end.

Fixpoint getStack {n} (entry: Stack n) (state: State) : option (word n).
  refine (
    let m := getStackWords entry in
    let i := getStackIndex entry in
    let wos := (getStack_iter m i state) in
    let joined := (joinWordOpts wos) in
    option_map (fun a => cast a) joined
  ); intuition.

  replace (Datatypes.length _) with (getStackWords entry); intuition.
  unfold wds.
  induction (getStackWords entry); simpl; intuition.
  destruct entry.

  simpl; intuition.
Defined.

Definition emptyState: State :=
  fullState (NatM.empty DefMap) (NatM.empty DefMap).

(* For register allocation checking *)
Definition regCount (base: nat): nat :=
  match base with
  | 32 => 7   | 64 => 8
  | 128 => 8  | 80 => 8
  | _ => 0
  end.

