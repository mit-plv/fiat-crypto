Require Import Crypto.Util.Tactics.Contains.

Ltac replace_with_rewrite_or_setoid_rewrite_in_all fwd x H :=
  move H at top;
  lazymatch goal with
  | [ |- context[x] ]
    => lazymatch fwd with
       | true  => first [ rewrite !H | setoid_rewrite H ]
       | false => first [ rewrite <- !H | setoid_rewrite <- H ]
       end;
       replace_with_rewrite_or_setoid_rewrite_in_all fwd x H
  | [ H' : context[x] |- _ ]
    => tryif constr_eq H H'
      then clear x H
      else (lazymatch fwd with
            | true  => first [ rewrite !H in H' | setoid_rewrite H in H' ]
            | false => first [ rewrite <- !H in H' | setoid_rewrite <- H in H' ]
            end;
            replace_with_rewrite_or_setoid_rewrite_in_all fwd x H)
  end.

Ltac setoid_subst'' R x :=
  is_var x;
  match goal with
  | [ H : R x ?y |- _ ]
    => free_in x y; replace_with_rewrite_or_setoid_rewrite_in_all true x H
  | [ H : R ?y x |- _ ]
    => free_in x y; replace_with_rewrite_or_setoid_rewrite_in_all false x H
  | [ H : is_true (R x ?y) |- _ ]
    => free_in x y; replace_with_rewrite_or_setoid_rewrite_in_all true x H
  | [ H : is_true (R ?y x) |- _ ]
    => free_in x y; replace_with_rewrite_or_setoid_rewrite_in_all false x H
  | [ H : R x ?y = true |- _ ]
    => free_in x y; change (is_true (R x y)) in H; replace_with_rewrite_or_setoid_rewrite_in_all true x H
  | [ H : R ?y x = true |- _ ]
    => free_in x y; change (is_true (R y x)) in H; replace_with_rewrite_or_setoid_rewrite_in_all false x H
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
