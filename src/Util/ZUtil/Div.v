Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.CompareToSgn.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  Proof. intros. rewrite Z.mul_comm. apply Z.div_mul; auto. Qed.
  Hint Rewrite div_mul' using zutil_arith : zsimplify.

  Local Ltac replace_to_const c :=
    repeat match goal with
           | [ H : ?x = ?x |- _ ] => clear H
           | [ H : ?x = c, H' : context[?x] |- _ ] => rewrite H in H'
           | [ H : c = ?x, H' : context[?x] |- _ ] => rewrite <- H in H'
           | [ H : ?x = c |- context[?x] ] => rewrite H
           | [ H : c = ?x |- context[?x] ] => rewrite <- H
           end.

  Lemma lt_div_0 n m : n / m < 0 <-> ((n < 0 < m \/ m < 0 < n) /\ 0 < -(n / m)).
  Proof.
    Z.compare_to_sgn; rewrite Z.sgn_opp; simpl.
    pose proof (Zdiv_sgn n m) as H.
    pose proof (Z.sgn_spec (n / m)) as H'.
    repeat first [ progress intuition auto
                 | progress simpl in *
                 | congruence
                 | lia
                 | progress replace_to_const (-1)
                 | progress replace_to_const 0
                 | progress replace_to_const 1
                 | match goal with
                   | [ x : Z |- _ ] => destruct x
                   end ].
  Qed.
End Z.
