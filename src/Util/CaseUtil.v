Require Import Arith.

Ltac case_max :=
  match goal with [ |- context[max ?x ?y] ] =>
      destruct (le_dec x y);
      match goal with
        | [ H : (?x <= ?y)%nat |- context[max ?x ?y] ] => rewrite Max.max_r by
          (exact H)
        | [ H : ~ (?x <= ?y)%nat   |- context[max ?x ?y] ] => rewrite Max.max_l by
          (exact (le_Sn_le _ _ (not_le _ _ H)))
      end
  end.
