Require Import Coq.omega.Omega.
Require Import Coq.ZArith.BinInt.

Ltac rewrite_min_max_side_condition_t := omega.

Ltac revert_min_max :=
  repeat match goal with
         | [ H : context[Z.min _ _] |- _ ] => revert H
         | [ H : context[Z.max _ _] |- _ ] => revert H
         end.
Ltac rewrite_min_max_step_fast :=
  match goal with
  | [ H : (?a <= ?b)%Z |- context[Z.max ?a ?b] ]
    => rewrite (Z.max_r a b) by assumption
  | [ H : (?b <= ?a)%Z |- context[Z.max ?a ?b] ]
    => rewrite (Z.max_l a b) by assumption
  | [ H : (?a <= ?b)%Z |- context[Z.min ?a ?b] ]
    => rewrite (Z.min_l a b) by assumption
  | [ H : (?b <= ?a)%Z |- context[Z.min ?a ?b] ]
    => rewrite (Z.min_r a b) by assumption
  end.
Ltac rewrite_min_max_step :=
  match goal with
  | _ => rewrite_min_max_step_fast
  | [ |- context[Z.max ?a ?b] ]
    => first [ rewrite (Z.max_l a b) by rewrite_min_max_side_condition_t
             | rewrite (Z.max_r a b) by rewrite_min_max_side_condition_t ]
  | [ |- context[Z.min ?a ?b] ]
    => first [ rewrite (Z.min_l a b) by rewrite_min_max_side_condition_t
             | rewrite (Z.min_r a b) by rewrite_min_max_side_condition_t ]
  end.
Ltac only_split_min_max_step :=
  match goal with
  | _ => revert_min_max; progress repeat apply Z.min_case_strong; intros
  | _ => revert_min_max; progress repeat apply Z.max_case_strong; intros
  end.
Ltac split_min_max_step :=
  match goal with
  | _ => rewrite_min_max_step
  | _ => only_split_min_max_step
  end.
Ltac split_min_max := repeat split_min_max_step.
