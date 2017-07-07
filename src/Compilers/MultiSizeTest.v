Require Import Coq.omega.Omega.
Require Import Crypto.Compilers.SmartMap.

Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Preliminaries: bounded and unbounded number types *)

Definition bound8 := 256.

Definition word8 := {n | n < bound8}.

Definition bound9 := 512.

Definition word9 := {n | n < bound9}.


(** * Expressions over unbounded words *)

Section unbounded.
  Variable var : Type.

  Inductive unbounded :=
  | Const : nat -> unbounded
  | Var : var -> unbounded
  | Plus : unbounded -> unbounded -> unbounded
  | LetIn : unbounded -> (var -> unbounded) -> unbounded.
End unbounded.

Arguments Const [var] _.

Definition Unbounded := forall var, unbounded var.

Fixpoint unboundedD (e : unbounded nat) : nat :=
  match e with
  | Const n => n
  | Var n => n
  | Plus e1 e2 => unboundedD e1 + unboundedD e2
  | LetIn e1 e2 => unboundedD (e2 (unboundedD e1))
  end.

Definition UnboundedD (E : Unbounded) : nat :=
  unboundedD (E _).

(** * Opt-in bounded types *)

Section bounded.
  Inductive type :=
  | Nat
  | Word8
  | Word9.

  Variable var : type -> Type.

  Inductive bounded : type -> Type :=
  | BConst : nat -> bounded Nat
  | BConst8 : word8 -> bounded Word8
  | BConst9 : word9 -> bounded Word9
  | BVar : forall t, var t -> bounded t
  | BPlus : bounded Nat -> bounded Nat -> bounded Nat
  | BPlus8 : bounded Word8 -> bounded Word8 -> bounded Word8
  | BPlus9 : bounded Word9 -> bounded Word9 -> bounded Word9
  | BLetIn : forall t1 t2, bounded t1 -> (var t1 -> bounded t2) -> bounded t2

  | Unbound : forall t, bounded t -> bounded Nat
  | Bound : forall t, bounded Nat -> bounded t.
End bounded.

Arguments BConst [var] _.
Arguments BConst8 [var] _.
Arguments BConst9 [var] _.
Arguments BVar [var t] _.
Arguments Unbound [var t] _.
Arguments Bound [var] _ _.

Definition Bounded t := forall var, bounded var t.

Definition typeD (t : type) : Type :=
  match t with
  | Nat => nat
  | Word8 => word8
  | Word9 => word9
  end.

Theorem O_lt_S : forall n, O < S n.
Proof.
  intros; omega.
Qed.

Definition plus8 (a b : word8) : word8 :=
  let n := proj1_sig a + proj1_sig b in
  match le_lt_dec bound8 n with
  | left _ => exist _ O (O_lt_S _)
  | right pf => exist _ n pf
  end.

Definition plus9 (a b : word9) : word9 :=
  let n := proj1_sig a + proj1_sig b in
  match le_lt_dec bound9 n with
  | left _ => exist _ O (O_lt_S _)
  | right pf => exist _ n pf
  end.

Infix "+8" := plus8 (at level 50).
Infix "+9" := plus9 (at level 50).

Definition unbound {t} : typeD t -> nat :=
  match t with
  | Nat => fun x => x
  | Word8 => fun x => proj1_sig x
  | Word9 => fun x => proj1_sig x
  end.

Definition bound {t} : nat -> typeD t :=
  match t return nat -> typeD t with
  | Nat => fun x => x
  | Word8 => fun x =>
               match le_lt_dec bound8 x with
               | left _ => exist _ O (O_lt_S _)
               | right pf => exist _ x pf
               end
  | Word9 => fun x =>
               match le_lt_dec bound9 x with
               | left _ => exist _ O (O_lt_S _)
               | right pf => exist _ x pf
               end
  end.

Fixpoint boundedD t (e : bounded typeD t) : typeD t :=
  match e with
  | BConst n => n
  | BConst8 n => n
  | BConst9 n => n
  | BVar _ n => n
  | BPlus e1 e2 => boundedD e1 + boundedD e2
  | BPlus8 e1 e2 => boundedD e1 +8 boundedD e2
  | BPlus9 e1 e2 => boundedD e1 +9 boundedD e2
  | BLetIn _ _ e1 e2 => boundedD (e2 (boundedD e1))
  | Unbound _ e1 => unbound (boundedD e1)
  | Bound _ e1 => bound (boundedD e1)
  end.

Definition BoundedD t (E : Bounded t) : typeD t :=
  boundedD (E _).


(** * Insertion of bounded types opportunistically *)

Definition fail {var} : nat * bounded var Nat := (0, BConst 0).

Fixpoint boundOf (eb : unbounded nat) : nat :=
  match eb with
  | Const n => n
  | Var n => n
  | Plus eb1 eb2 => boundOf eb1 + boundOf eb2
  | LetIn eb1 eb2 => boundOf (eb2 (boundOf eb1))
  end.

Fixpoint boundify {var} (eb : unbounded nat) (e : unbounded (var Nat)) : nat * bounded var Nat :=
  match e with
  | Const n => (n,
                match le_lt_dec bound8 n with
                | left _ =>
                  match le_lt_dec bound9 n with
                  | left _ => BConst n
                  | right pf => Unbound (BConst9 (exist _ n pf))
                  end
                | right pf => Unbound (BConst8 (exist _ n pf))
                end)
  | Var x =>
    match eb with
    | Var n => (n, BVar x)
    | _ => fail
    end
  | Plus e1 e2 =>
    match eb with
    | Plus eb1 eb2 =>
      let (n1, e1') := boundify eb1 e1 in
      let (n2, e2') := boundify eb2 e2 in
      (n1 + n2,
       if le_lt_dec bound8 (n1 + n2)
       then if le_lt_dec bound9 (n1 + n2)
            then BPlus e1' e2'
            else Unbound (BPlus9 (Bound _ e1') (Bound _ e2'))
       else Unbound (BPlus8 (Bound _ e1') (Bound _ e2')))
    | _ => fail
    end
  | LetIn e1 e2 =>
    match eb with
    | LetIn eb1 eb2 =>
      let (n1, e1') := boundify eb1 e1 in
      (boundOf (eb2 n1), BLetIn e1' (fun x => snd (boundify (eb2 n1) (e2 x))))
    | _ => fail
    end
  end.

Definition Boundify (E : Unbounded) : Bounded Nat :=
  fun _ => snd (boundify (E _) (E _)).


(** * Moving [Unbound] operators down from [LetIn]s to their use sites *)

Fixpoint movedown {var t} (e : bounded (bounded var) t) : bounded var t :=
  match e with
  | BConst n => BConst n
  | BConst8 n => BConst8 n
  | BConst9 n => BConst9 n
  | BVar _ e => e
  | BPlus e1 e2 => BPlus (movedown e1) (movedown e2)
  | BPlus8 e1 e2 => BPlus8 (movedown e1) (movedown e2)
  | BPlus9 e1 e2 => BPlus9 (movedown e1) (movedown e2)
  | BLetIn _ _ e1 e2 =>
    match movedown e1 in bounded _ t return (bounded _ t -> _) -> _ with
    | Unbound _ e1'' => fun e2_rec => BLetIn e1'' (fun x => e2_rec (Unbound (BVar x)))
    | e1' => fun e2_rec => BLetIn e1' (fun x => e2_rec (BVar x))
    end (fun x => movedown (e2 x))
  | Unbound _ e1 => Unbound (movedown e1)
  | Bound t e1 => Bound t (movedown e1)
  end.

Definition Movedown t (E : Bounded t) : Bounded t :=
  fun _ => movedown (E _).


(** * Canceling matching [Bound] and [Unbound] *)

Definition type_eq_dec : forall t1 t2 : type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

Fixpoint cancel {var t} (e : bounded var t) : bounded var t :=
  match e with
  | BConst n => BConst n
  | BConst8 n => BConst8 n
  | BConst9 n => BConst9 n
  | BVar _ x => BVar x
  | BPlus e1 e2 => BPlus (cancel e1) (cancel e2)
  | BPlus8 e1 e2 => BPlus8 (cancel e1) (cancel e2)
  | BPlus9 e1 e2 => BPlus9 (cancel e1) (cancel e2)
  | BLetIn _ _ e1 e2 => BLetIn (cancel e1) (fun x => cancel (e2 x))
  | Unbound _ e1 => Unbound (cancel e1)
  | Bound t e1 =>
    match cancel e1 with
    | Unbound t' e1' =>
      match type_eq_dec t' t with
      | left pf => match pf in _ = T return bounded _ T with
                   | eq_refl => e1'
                   end
      | right _ => Bound t (Unbound e1')
      end
    | e1' => Bound t e1'
    end
  end.

Definition Cancel t (E : Bounded t) : Bounded t :=
  fun _ => cancel (E _).


(** * Examples *)

Example ex1 : Unbounded := fun _ =>
  LetIn (Const 127) (fun a =>
  LetIn (Const 63) (fun b =>
  LetIn (Plus (Var a) (Var b)) (fun c =>
  Plus (Var c) (Var c)))).

Eval compute in (UnboundedD ex1).

Definition ex1b := Boundify ex1.
Eval compute in ex1b.

Definition ex1bm := Movedown (Boundify ex1).
Eval compute in ex1bm.

Definition ex1bmc := Cancel (Movedown (Boundify ex1)).
Eval compute in ex1bmc.
