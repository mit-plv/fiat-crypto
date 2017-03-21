(*** Boolean Utility Lemmas and Databases *)
Require Import Coq.Bool.Bool.

(** For equalities of booleans *)
Create HintDb bool_congr discriminated.
(** For properties of booleans, with, e.g., [iff] *)
Create HintDb bool_congr_setoid discriminated.
(** For generic simplifications of things involving booleans, e.g., if-statements *)
Create HintDb boolsimplify discriminated.

Hint Extern 1 => progress autorewrite with boolsimplify in * : boolsimplify.
Hint Extern 1 => progress autorewrite with bool_congr in * : bool_congr.
Hint Extern 1 => progress autorewrite with bool_congr_setoid in * : bool_congr_setoid.
Hint Extern 2 => progress rewrite_strat topdown hints bool_congr_setoid : bool_congr_setoid.

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
Hint Extern 1 => progress autorewrite with push_orb in * : push_orb.
Hint Extern 1 => progress autorewrite with pull_orb in * : pull_orb.
Hint Extern 1 => progress autorewrite with push_andb in * : push_andb.
Hint Extern 1 => progress autorewrite with pull_andb in * : pull_andb.
Hint Extern 1 => progress autorewrite with push_negb in * : push_negb.
Hint Extern 1 => progress autorewrite with pull_negb in * : pull_negb.
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

Ltac split_andb :=
  repeat match goal with
         | [ H : andb _ _ = true |- _ ] => apply andb_prop in H; destruct H
         | [ H : is_true (andb ?x ?y) |- _ ]
           => apply andb_prop in H;
              change (is_true x /\ is_true y) in H;
              destruct H
         | [ H : context[andb ?x ?y = true] |- _ ]
           => rewrite (Bool.andb_true_iff x y) in H
         | [ H : context[is_true (andb ?x ?y)] |- _ ]
           => change (is_true (andb x y)) with (andb x y = true) in H;
              rewrite Bool.andb_true_iff in H;
              change (x = true /\ y = true) with (is_true x /\ is_true y) in H
         end.
