Require Import Coq.Arith.Arith Coq.Arith.Max.

Ltac case_max :=
  match goal with [ |- context[max ?x ?y] ] =>
      destruct (le_dec x y);
      match goal with
        | [ H : (?x <= ?y)%nat |- context[max ?x ?y] ] => rewrite max_r by
          (exact H)
        | [ H : ~ (?x <= ?y)%nat   |- context[max ?x ?y] ] => rewrite max_l by
          (exact (le_Sn_le _ _ (not_le _ _ H)))
      end
  end.

Lemma pull_app_if_sumbool {A B X Y} (b : sumbool X Y) (f g : A -> B) (x : A)
  : (if b then f x else g x) = (if b then f else g) x.
Proof.
  destruct b; reflexivity.
Qed.
