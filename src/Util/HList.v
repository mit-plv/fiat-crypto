Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.IffT.
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

Fixpoint rhlist' T n (f : T -> Type) : rtuple' T n -> Type :=
  match n return rtuple' _ n -> Type with
  | 0 => fun T => f T
  | S n' => fun Ts => (f (fst Ts) * rhlist' T n' f (snd Ts))%type
  end.
Global Arguments rhlist' {T n} f _.

Definition rhlist {T n} (f : T -> Type) : forall (Ts : rtuple T n), Type :=
  match n return rtuple _ n -> Type with
  | 0 => fun _ => unit
  | S n' => @rhlist' T n' f
  end.

Fixpoint const' {T n F xs} (v : forall x, F x) : @hlist' T n F xs
  := match n return forall xs, @hlist' T n F xs with
     | 0 => fun _ => v _
     | S n' => fun _ => (@const' T n' F _ v, v _)
     end xs.
Definition const {T n F xs} (v : forall x, F x) : @hlist T n F xs
  := match n return forall xs, @hlist T n F xs with
     | 0 => fun _ => tt
     | S n' => fun xs => @const' T n' F xs v
     end xs.

(* tuple map *)
Fixpoint mapt' {n A F B} (f : forall x : A, F x -> B) : forall {ts : tuple' A n}, hlist' F ts -> tuple' B n
  := match n return forall ts : tuple' A n, hlist' F ts -> tuple' B n with
     | 0 => fun ts v => f _ v
     | S n' => fun ts v => (@mapt' n' A F B f _ (fst v), f _ (snd v))
     end.
Definition mapt {n A F B} (f : forall x : A, F x -> B)
  : forall {ts : tuple A n}, hlist F ts -> tuple B n
  := match n return forall ts : tuple A n, hlist F ts -> tuple B n with
     | 0 => fun ts v => tt
     | S n' => @mapt' n' A F B f
     end.

Lemma map'_mapt' {n A F B C} (g : B -> C) (f : forall x : A, F x -> B)
      {ts : tuple' A n} (ls : hlist' F ts)
  : Tuple.map (n:=S n) g (mapt' f ls) = mapt' (fun x v => g (f x v)) ls.
Proof.
  induction n as [|n IHn]; [ reflexivity | ].
  { simpl @mapt' in *.
    rewrite <- IHn.
    rewrite Tuple.map_S; reflexivity. }
Qed.

Lemma map_mapt {n A F B C} (g : B -> C) (f : forall x : A, F x -> B)
      {ts : tuple A n} (ls : hlist F ts)
  : Tuple.map g (mapt f ls) = mapt (fun x v => g (f x v)) ls.
Proof.
  destruct n as [|n]; [ reflexivity | ].
  apply map'_mapt'.
Qed.

Lemma map_is_mapt {n A F B} (f : A -> B) {ts : tuple A n} (ls : hlist F ts)
  : Tuple.map f ts = mapt (fun x _ => f x) ls.
Proof.
  destruct n as [|n]; [ reflexivity | ].
  induction n as [|n IHn]; [ reflexivity | ].
  { unfold mapt in *; simpl @mapt' in *.
    rewrite <- IHn; clear IHn.
    rewrite <- (@Tuple.map_S n _ _ f); destruct ts; reflexivity. }
Qed.

Lemma map_is_mapt' {n A F B} (f : A -> B) {ts : tuple A (S n)} (ls : hlist' F ts)
  : Tuple.map f ts = mapt' (fun x _ => f x) ls.
Proof. apply (@map_is_mapt (S n)). Qed.


Lemma hlist'_impl {n A F G} (xs:tuple' A n)
  : (hlist' (fun x => F x -> G x) xs) -> (hlist' F xs -> hlist' G xs).
Proof.
  induction n; simpl in *; intuition.
Defined.

Lemma hlist_impl {n A F G} (xs:tuple A n)
  : (hlist (fun x => F x -> G x) xs) -> (hlist F xs -> hlist G xs).
Proof.
  destruct n; [ constructor | apply hlist'_impl ].
Defined.

Local Arguments Tuple.map : simpl never.
Lemma hlist_map {n A B F} {f:A -> B} (xs:tuple A n)
  : hlist F (Tuple.map f xs) = hlist (fun x => F (f x)) xs.
Proof.
  destruct n as [|n]; [ reflexivity | ].
  induction n; [ reflexivity | ].
  specialize (IHn (fst xs)).
  destruct xs; rewrite Tuple.map_S.
  simpl @hlist in *; rewrite <- IHn.
  reflexivity.
Qed.

Lemma fold_right_and_True_hlist' {n A F} (xs:tuple' A n)
  : iffT (List.fold_right and True (List.map F (Tuple.to_list' _ xs))) (hlist' F xs).
Proof.
  induction n.
  { simpl; tauto. }
  { specialize (IHn (fst xs)).
    destruct xs; simpl in *.
    tauto. }
Qed.

Lemma fold_right_and_True_hlist {n A F} (xs:tuple A n)
  : iffT (List.fold_right and True (List.map F (Tuple.to_list _ xs))) (hlist F xs).
Proof.
  destruct n; [ simpl; tauto | apply fold_right_and_True_hlist' ].
Qed.

Global Instance mapt_Proper {n A F B}
  : Proper
      ((forall_relation (fun x => pointwise_relation _ Logic.eq))
         ==> forall_relation (fun ts => Logic.eq ==> Logic.eq))
      (@HList.mapt n A F B).
Proof.
  unfold forall_relation, pointwise_relation, respectful.
  repeat intro; subst; destruct n as [|n]; [ reflexivity | ].
  induction n; simpl in *; congruence.
Qed.

Module Tuple.
  Lemma map_id_ext {n A} (f : A -> A) (xs:tuple A n)
  : hlist (fun x => f x = x) xs -> Tuple.map f xs = xs.
  Proof.
    destruct n as [|n]; [cbv in *; destruct xs; trivial|].
    induction n as [|n IHn]; [cbv in *;trivial|].
    simpl in *. destruct xs. simpl in *; intros [??].
    rewrite map_S. eauto using f_equal2.
  Qed.
End Tuple.
