Require Import Crypto.Util.Tactics.Contains.

Ltac setoid_subst'' R x :=
  is_var x;
  match goal with
  | [ H : R x ?y |- _ ]
    => free_in x y; rewrite ?H in *; clear x H
  | [ H : R ?y x |- _ ]
    => free_in x y; rewrite <- ?H in *; clear x H
  | [ H : is_true (R x ?y) |- _ ]
    => free_in x y; rewrite ?H in *; clear x H
  | [ H : is_true (R ?y x) |- _ ]
    => free_in x y; rewrite <- ?H in *; clear x H
  | [ H : R x ?y = true |- _ ]
    => free_in x y; change (is_true (R x y)) in H; rewrite ?H in *; clear x H
  | [ H : R ?y x = true |- _ ]
    => free_in x y; change (is_true (R y x)) in H; rewrite <- ?H in *; clear x H
  end.

Ltac setoid_subst' x :=
  is_var x;
  match goal with
  | [ H : ?R x _ |- _ ] => setoid_subst'' R x
  | [ H : ?R _ x |- _ ] => setoid_subst'' R x
  | [ H : is_true (?R x _) |- _ ] => setoid_subst'' R x
  | [ H : is_true (?R _ x) |- _ ] => setoid_subst'' R x
  | [ H : ?R x _ = true |- _ ] => setoid_subst'' R x
  | [ H : ?R _ x = true |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel' R :=
  idtac;
  match goal with
  | [ H : R ?x _ |- _ ] => setoid_subst'' R x
  | [ H : R _ ?x |- _ ] => setoid_subst'' R x
  | [ H : is_true (R ?x _) |- _ ] => setoid_subst'' R x
  | [ H : is_true (R _ ?x) |- _ ] => setoid_subst'' R x
  | [ H : R ?x _ = true |- _ ] => setoid_subst'' R x
  | [ H : R _ ?x = true |- _ ] => setoid_subst'' R x
  end.

Ltac setoid_subst_rel R := repeat setoid_subst_rel' R.

Ltac setoid_subst_all :=
  repeat match goal with
         | [ H : ?R ?x ?y |- _ ] => is_var x; setoid_subst'' R x
         | [ H : ?R ?x ?y |- _ ] => is_var y; setoid_subst'' R y
         | [ H : is_true (?R ?x ?y) |- _ ] => is_var x; setoid_subst'' R x
         | [ H : is_true (?R ?x ?y) |- _ ] => is_var y; setoid_subst'' R y
         | [ H : ?R ?x ?y = true |- _ ] => is_var x; setoid_subst'' R x
         | [ H : ?R ?x ?y = true |- _ ] => is_var y; setoid_subst'' R y
         end.

Tactic Notation "setoid_subst" ident(x) := setoid_subst' x.
Tactic Notation "setoid_subst" := setoid_subst_all.
