Require Import Coq.omega.Omega Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Module Z.
  Ltac clean_neg :=
    repeat match goal with
           | [ H : (-?x) < 0 |- _ ] => assert (0 < x) by omega; clear H
           | [ H : 0 > (-?x) |- _ ] => assert (0 < x) by omega; clear H
           | [ H : (-?x) <= 0 |- _ ] => assert (0 <= x) by omega; clear H
           | [ H : 0 >= (-?x) |- _ ] => assert (0 <= x) by omega; clear H
           | [ H : -?x <= -?y |- _ ] => apply Z.opp_le_mono in H
           | [ |- -?x <= -?y ] => apply Z.opp_le_mono
           | _ => progress rewrite <- Z.opp_le_mono in *
           | [ H : 0 <= ?x, H' : 0 <= ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 <= ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 <= ?x, H' : 0 < ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 < ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 <= ?y, H'' : -?x < ?y |- _ ] => clear H''
           | [ H : 0 <= ?x, H' : 0 < ?y, H'' : -?x < ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 < ?y, H'' : -?x < ?y |- _ ] => clear H''
           end.
  Ltac replace_with_neg x :=
    assert (x = -(-x)) by (symmetry; apply Z.opp_involutive); generalize dependent (-x);
    let x' := fresh in
    rename x into x'; intro x; intros; subst x';
    clean_neg.
  Ltac replace_all_neg_with_pos :=
    repeat match goal with
           | [ H : ?x < 0 |- _ ] => replace_with_neg x
           | [ H : 0 > ?x |- _ ] => replace_with_neg x
           | [ H : ?x <= 0 |- _ ] => replace_with_neg x
           | [ H : 0 >= ?x |- _ ] => replace_with_neg x
           end.
End Z.
