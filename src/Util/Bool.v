(*** Boolean Utility Lemmas and Databases *)
Require Import Coq.Bool.Bool.
Require Import Crypto.Util.Notations.

(** For equalities of booleans *)
Create HintDb bool_congr discriminated.
(** For properties of booleans, with, e.g., [iff] *)
Create HintDb bool_congr_setoid discriminated.
(** For generic simplifications of things involving booleans, e.g., if-statements *)
Create HintDb boolsimplify discriminated.

Global Hint Extern 1 => progress autorewrite with boolsimplify in * : boolsimplify.
Global Hint Extern 1 => progress autorewrite with bool_congr in * : bool_congr.
Global Hint Extern 1 => progress autorewrite with bool_congr_setoid in * : bool_congr_setoid.
Global Hint Extern 2 => progress rewrite_strat topdown hints bool_congr_setoid : bool_congr_setoid.

Hint Rewrite Bool.andb_diag Bool.orb_diag Bool.eqb_reflx Bool.negb_involutive Bool.eqb_negb1 Bool.eqb_negb2 Bool.orb_true_r Bool.orb_true_l Bool.orb_false_r Bool.orb_false_l Bool.orb_negb_r Bool.andb_false_r Bool.andb_false_l Bool.andb_true_r Bool.andb_false_r Bool.andb_negb_r Bool.xorb_false_r Bool.xorb_false_l Bool.xorb_true_r Bool.xorb_true_l Bool.xorb_nilpotent : bool_congr.
Hint Rewrite Bool.negb_if : boolsimplify.
Hint Rewrite <- Bool.andb_if Bool.andb_lazy_alt Bool.orb_lazy_alt : boolsimplify.
Hint Rewrite Bool.not_true_iff_false Bool.not_false_iff_true Bool.eqb_true_iff Bool.eqb_false_iff Bool.negb_true_iff Bool.negb_false_iff Bool.orb_true_iff Bool.orb_false_iff Bool.andb_true_iff Bool.andb_false_iff Bool.xorb_negb_negb : bool_congr_setoid.

Create HintDb push_orb discriminated.
Create HintDb pull_orb discriminated.
Create HintDb push_andb discriminated.
Create HintDb pull_andb discriminated.
Create HintDb push_negb discriminated.
Create HintDb pull_negb discriminated.
Global Hint Extern 1 => progress autorewrite with push_orb in * : push_orb.
Global Hint Extern 1 => progress autorewrite with pull_orb in * : pull_orb.
Global Hint Extern 1 => progress autorewrite with push_andb in * : push_andb.
Global Hint Extern 1 => progress autorewrite with pull_andb in * : pull_andb.
Global Hint Extern 1 => progress autorewrite with push_negb in * : push_negb.
Global Hint Extern 1 => progress autorewrite with pull_negb in * : pull_negb.
Hint Rewrite Bool.negb_orb Bool.negb_andb : push_negb.
Hint Rewrite Bool.xorb_negb_negb : pull_negb.
Hint Rewrite <- Bool.negb_orb Bool.negb_andb Bool.negb_xorb_l Bool.negb_xorb_r : pull_negb.
Hint Rewrite Bool.andb_orb_distrib_r Bool.andb_orb_distrib_l : push_andb.
Hint Rewrite <- Bool.orb_andb_distrib_r Bool.orb_andb_distrib_l : push_andb.
Hint Rewrite Bool.orb_andb_distrib_r Bool.orb_andb_distrib_l : pull_andb.
Hint Rewrite <- Bool.andb_orb_distrib_r Bool.andb_orb_distrib_l : pull_andb.
Hint Rewrite Bool.orb_andb_distrib_r Bool.orb_andb_distrib_l : push_orb.
Hint Rewrite <- Bool.andb_orb_distrib_r Bool.andb_orb_distrib_l : push_orb.
Hint Rewrite <- Bool.orb_andb_distrib_r Bool.orb_andb_distrib_l : pull_orb.
Hint Rewrite Bool.andb_orb_distrib_r Bool.andb_orb_distrib_l : pull_orb.

Definition pull_bool_if_dep {A B} (f : forall b : bool, A b -> B b) (b : bool) (x : A true) (y : A false)
  : (if b return B b then f _ x else f _ y) = f b (if b return A b then x else y)
  := if b return ((if b return B b then f _ x else f _ y) = f b (if b return A b then x else y))
     then eq_refl
     else eq_refl.

Definition pull_bool_if {A B} (f : A -> B) (b : bool) (x : A) (y : A)
  : (if b then f x else f y) = f (if b then x else y)
  := @pull_bool_if_dep (fun _ => A) (fun _ => B) (fun _ => f) b x y.

Definition reflect_iff_gen {P b} : reflect P b -> forall b' : bool, (if b' then P else ~P) <-> b = b'.
Proof.
  intros H; apply reflect_iff in H; intro b'; destruct b, b';
    intuition congruence.
Qed.

Definition andb_prop : forall a b : bool, a && b = true -> a = true /\ b = true. (* transparent version *)
Proof. destruct a, b; simpl; split; try reflexivity; assumption. Defined.

Definition andb_true_intro : forall a b : bool, a = true /\ b = true -> a && b = true. (* transparent version *)
Proof. destruct a, b; simpl; try reflexivity; intros [? ?]; assumption. Defined.

Definition andb_true_rect {a b : bool} (P : a && b = true -> Type) (f : forall p q, P (andb_true_intro a b (conj p q)))
  : forall p, P p.
Proof.
  destruct a, b; try specialize (f eq_refl eq_refl); cbn in *; intro p;
    first [ refine match p with eq_refl => f end
          | refine match p with eq_refl => I end ].
Defined.
Definition andb_true_rec {a b : bool} (P : a && b = true -> Set) := @andb_true_rect a b P.
Definition andb_true_ind {a b : bool} (P : a && b = true -> Prop) := @andb_true_rec a b P.

Definition andb_is_true_intro : forall a b : bool, is_true a /\ is_true b -> is_true (a && b)
  := andb_true_intro.

Definition andb_is_true_rect {a b : bool} (P : is_true (a && b) -> Type) (f : forall p q, P (andb_is_true_intro a b (conj p q)))
  : forall p, P p
  := @andb_true_rect a b P f.
Definition andb_is_true_rec {a b : bool} (P : is_true (a && b) -> Set) := @andb_is_true_rect a b P.
Definition andb_is_true_ind {a b : bool} (P : is_true (a && b) -> Prop) := @andb_is_true_rec a b P.

Ltac split_andb_step :=
  match goal with
  | [ H : andb _ _ = true |- _ ] => induction H using (@andb_true_rect _ _)
  | [ H : is_true (andb _ _) |- _ ] => induction H using (@andb_is_true_rect _ _)
  end.
Ltac split_andb := repeat split_andb_step.
Ltac split_andb_in_context_step :=
  match goal with
  | _ => split_andb_step
  | [ H : context[andb ?x ?y = true] |- _ ]
    => rewrite (Bool.andb_true_iff x y) in H
  | [ H : context[is_true (andb ?x ?y)] |- _ ]
    => change (is_true (andb x y)) with (andb x y = true) in H;
       rewrite Bool.andb_true_iff in H;
       change (x = true /\ y = true) with (is_true x /\ is_true y) in H
  end.
Ltac split_andb_in_context := repeat split_andb_in_context_step.

Lemma if_const A (b : bool) (x : A) : (if b then x else x) = x.
Proof. case b; reflexivity. Qed.

Lemma ex_bool_iff_or P : @ex bool P <-> (or (P true) (P false)).
Proof.
  split; [ intros [ [] ? ] | intros [?|?]; eexists ]; eauto.
Qed.

Lemma eqb_true_l x : Bool.eqb x true = x. Proof. now destruct x. Qed.
Lemma eqb_true_r x : Bool.eqb true x = x. Proof. now destruct x. Qed.
Lemma eqb_false_l x : Bool.eqb x false = negb x. Proof. now destruct x. Qed.
Lemma eqb_false_r x : Bool.eqb false x = negb x. Proof. now destruct x. Qed.
Hint Rewrite eqb_true_l eqb_true_r eqb_false_l eqb_false_r : boolsimplify.

Module Thunked.
  Local Notation lift0 f := (fun (v : unit) => f) (only parsing).
  Local Notation lift1 f := (fun (x : unit -> bool) (v : unit) => f (x v)) (only parsing).
  Local Notation lift2 f := (fun (x y : unit -> bool) (v : unit) => f (x v) (y v)) (only parsing).
  Local Notation lift3 f := (fun (x y z : unit -> bool) (v : unit) => f (x v) (y v) (z v)) (only parsing).
  Definition bool := unit -> bool.
  Definition true : bool := lift0 true.
  Definition false : bool := lift0 false.
  Definition orb (x y : bool) : bool
    := fun _ => if x tt then Datatypes.true else y tt.
  Definition xorb : bool -> bool -> bool := lift2 xorb.
  Definition andb (x y : bool) : bool
    := fun _ => if x tt then y tt else Datatypes.false.
  Definition implb (x y : bool) : bool
    := fun _ => if x tt then y tt else Datatypes.true.
  Definition eqb : bool -> bool -> bool := lift2 eqb.
  Definition ifb (c t f : bool) : bool
    := fun _ => if c tt then t tt else f tt.
  Definition eq : bool -> bool -> Prop := fun a b => a tt = b tt.

  Module Export Notations.
    Declare Scope thunked_bool_scope.
    Delimit Scope thunked_bool_scope with thunked_bool.
    Bind Scope thunked_bool_scope with bool.
    Infix "&&" := andb : thunked_bool_scope.
    Infix "||" := orb : thunked_bool_scope.
  End Notations.

  Local Infix "==" := eq.

  Create HintDb thunked_bool_helper discriminated.

  Local Ltac t :=
    cbv [true false bool orb xorb andb implb eqb ifb eq
              Datatypes.orb Datatypes.xorb Datatypes.andb Datatypes.implb Bool.eqb Bool.ifb] in *;
    repeat first [ progress intros
                 | progress subst
                 | reflexivity
                 | congruence
                 | match goal with
                   | [ x : unit |- _ ] => destruct x
                   | [ x : unit -> Datatypes.bool |- _ ] => generalize dependent (x tt); clear x; intros
                   | [ H : context[match ?x with _ => _ end] |- _ ] => is_var x; destruct x
                   | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ |- and _ _ ] => split
                   end ].

  Lemma unthunk_true : true tt = Datatypes.true.
  Proof. t. Qed.
  Hint Rewrite unthunk_true : unthunk_bool.
  Lemma unthunk_false : false tt = Datatypes.false.
  Proof. t. Qed.
  Hint Rewrite unthunk_false : unthunk_bool.
  Lemma unthunk_orb {x y} : orb x y tt = Datatypes.orb (x tt) (y tt).
  Proof. t. Qed.
  Hint Rewrite @unthunk_orb : unthunk_bool.
  Lemma unthunk_xorb {x y} : xorb x y tt = Datatypes.xorb (x tt) (y tt).
  Proof. t. Qed.
  Hint Rewrite @unthunk_xorb : unthunk_bool.
  Lemma unthunk_andb {x y} : andb x y tt = Datatypes.andb (x tt) (y tt).
  Proof. t. Qed.
  Hint Rewrite @unthunk_andb : unthunk_bool.
  Lemma unthunk_implb {x y} : implb x y tt = Datatypes.implb (x tt) (y tt).
  Proof. t. Qed.
  Hint Rewrite @unthunk_implb : unthunk_bool.
  Lemma unthunk_eqb {x y} : eqb x y tt = Bool.eqb (x tt) (y tt).
  Proof. t. Qed.
  Hint Rewrite @unthunk_eqb : unthunk_bool.
  Lemma unthunk_ifb {x y z} : ifb x y z tt = Bool.ifb (x tt) (y tt) (z tt).
  Proof. t. Qed.
  Hint Rewrite @unthunk_ifb : unthunk_bool.
  Lemma unthunk_eq {x y} : eq x y = (x tt = y tt).
  Proof. t. Qed.
  Hint Rewrite @unthunk_eq : unthunk_bool.

  Lemma andb_prop : forall a b : bool, a && b == true -> a == true /\ b == true.
  Proof. t. Qed.
  Lemma andb_true_intro : forall b1 b2 : bool, b1 == true /\ b2 == true -> b1 && b2 == true.
  Proof. t. Qed.
End Thunked.
