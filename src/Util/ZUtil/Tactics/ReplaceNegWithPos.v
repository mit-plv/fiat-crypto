Require Import Coq.omega.Omega Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Module Z.
  Lemma push_minus_add a b : -(-a + b) = a + -b. Proof. omega. Qed.

  Ltac clean_neg_step _ :=
    match goal with
    | [ H : (-?x) < 0 |- _ ] => assert (0 < x) by omega; clear H
    | [ H : 0 > (-?x) |- _ ] => assert (0 < x) by omega; clear H
    | [ H : 0 <> -?x |- _ ] => assert (0 <> x) by omega; clear H
    | [ H : -?x <> 0 |- _ ] => assert (x <> 0) by omega; clear H
    | [ H : (-?x) <= 0 |- _ ] => assert (0 <= x) by omega; clear H
    | [ H : 0 >= (-?x) |- _ ] => assert (0 <= x) by omega; clear H
    | [ H : -?x <= -?y |- _ ] => rewrite <- Z.opp_le_mono in H
    | [ |- -?x <= -?y ] => rewrite <- Z.opp_le_mono
    | [ H : -?x < -?y |- _ ] => rewrite <- Z.opp_lt_mono in H
    | [ |- -?x < -?y ] => rewrite <- Z.opp_lt_mono
    | _ => progress rewrite <- Z.opp_le_mono in *
    | [ H : context[_ * _] |- _ ]
      => first [ rewrite !Z.mul_opp_opp in H
               | rewrite !Z.mul_opp_l in H
               | rewrite !Z.mul_opp_r in H ]
    | [ |- context[_ * _] ]
      => first [ rewrite !Z.mul_opp_opp
               | rewrite !Z.mul_opp_l
               | rewrite !Z.mul_opp_r ]
    | [ H : context[- - _] |- _ ] => rewrite !Z.opp_involutive in H
    | [ |- context[- - _] ] => rewrite !Z.opp_involutive
    | [ H : context[-_ + -_] |- _ ] => rewrite <- !Z.opp_add_distr in H
    | [ |- context[-_ + -_] ] => rewrite <- !Z.opp_add_distr
    | [ H : context[-(-?a + ?b)] |- _ ] => rewrite !push_minus_add in H
    | [ |- context[-(-?a + ?b)] ] => rewrite !push_minus_add
    | [ H : 0 <= ?x, H' : 0 <= ?y, H'' : -?x <= ?y |- _ ] => clear H''
    | [ H : 0 < ?x, H' : 0 <= ?y, H'' : -?x <= ?y |- _ ] => clear H''
    | [ H : 0 <= ?x, H' : 0 < ?y, H'' : -?x <= ?y |- _ ] => clear H''
    | [ H : 0 < ?x, H' : 0 < ?y, H'' : -?x <= ?y |- _ ] => clear H''
    | [ H : 0 < ?x, H' : 0 <= ?y, H'' : -?x < ?y |- _ ] => clear H''
    | [ H : 0 <= ?x, H' : 0 < ?y, H'' : -?x < ?y |- _ ] => clear H''
    | [ H : 0 < ?x, H' : 0 < ?y, H'' : -?x < ?y |- _ ] => clear H''
    | [ |- -_ = -_ ] => rewrite Z.opp_inj_wd
    | [ H : -_ = -_ |- _ ] => rewrite Z.opp_inj_wd in H
    end.
  Ltac clean_neg := repeat clean_neg_step ().
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
