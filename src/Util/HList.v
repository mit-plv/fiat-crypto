Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tuple.
Require Export Crypto.Util.FixCoqMistakes.

Fixpoint hlist' T n (f : T -> Type) : tuple' T n -> Type :=
  match n return tuple' _ n -> Type with
  | 0 => fun T => f T
  | S n' => fun Ts => (hlist' T n' f (fst Ts) * f (snd Ts))%type
  end.
Global Arguments hlist' {T n} f _.

Definition hlist {T n} (f : T -> Type) : forall (Ts : tuple T n), Type :=
  match n return tuple _ n -> Type with
  | 0 => fun _ => unit
  | S n' => @hlist' T n' f
  end.

(* tuple map *)
Fixpoint mapt' {n A F B} (f : forall x : A, F x -> B) : forall ts : tuple' A n, hlist' F ts -> tuple' B n
  := match n return forall ts : tuple' A n, hlist' F ts -> tuple' B n with
     | 0 => fun ts v => f _ v
     | S n' => fun ts v => (@mapt' n' A F B f _ (fst v), f _ (snd v))
     end.
Definition mapt {n A F B} (f : forall x : A, F x -> B)
  : forall ts : tuple A n, hlist F ts -> tuple B n
  := match n return forall ts : tuple A n, hlist F ts -> tuple B n with
     | 0 => fun ts v => tt
     | S n' => @mapt' n' A F B f
     end.
