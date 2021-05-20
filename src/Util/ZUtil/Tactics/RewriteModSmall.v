Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Local Open Scope Z_scope.

Module Z.
  Lemma mod_mod_small a n m
        (Hnm : (m mod n = 0)%Z)
        (Hnm_le : (0 < n <= m)%Z)
        (H : (a mod m < n)%Z)
    : ((a mod n) mod m = a mod m)%Z.
  Proof.
    assert ((a mod n) < m)%Z
      by (eapply Z.lt_le_trans; [ apply Z.mod_pos_bound | ]; lia).
    rewrite (Z.mod_small _ m) by auto with zarith.
    apply Z.mod_divide in Hnm; [ | lia ].
    destruct Hnm as [x ?]; subst.
    repeat match goal with
           | [ H : context[(_ mod _)%Z] |- _ ]
             => revert H
           end.
    Z.div_mod_to_quot_rem_in_goal.
    lazymatch goal with
    | [ H : a = (?x * ?n * ?q) + _, H' : a = (?n * ?q') + _ |- _ ]
      => assert (q' = x * q) by nia; subst q'; nia
    end.
  Qed.

  (** [rewrite_mod_small] is a better version of [rewrite Z.mod_small
      by rewrite_mod_small_solver]; it backtracks across occurences
      that the solver fails to solve the side-conditions on. *)
  Ltac rewrite_mod_small_solver :=
    zutil_arith_more_inequalities.
  Ltac rewrite_mod_small :=
    repeat match goal with
           | [ |- context[?x mod ?y] ]
             => rewrite (Z.mod_small x y) by rewrite_mod_small_solver
           end.
  Ltac rewrite_mod_mod_small :=
    repeat match goal with
           | [ |- context[(?a mod ?n) mod ?m] ]
             => rewrite (mod_mod_small a n m) by rewrite_mod_small_solver
           end.
  Ltac rewrite_mod_small_more :=
    repeat (rewrite_mod_small || rewrite_mod_mod_small).
  Ltac rewrite_mod_small_in_hyps :=
    repeat match goal with
           | [ H : context[?x mod ?y] |- _ ]
             => rewrite (Z.mod_small x y) in H by rewrite_mod_small_solver
           end.
  Ltac rewrite_mod_mod_small_in_hyps :=
    repeat match goal with
           | [ H : context[(?a mod ?n) mod ?m] |- _ ]
             => rewrite (mod_mod_small a n m) in H by rewrite_mod_small_solver
           end.
  Ltac rewrite_mod_small_more_in_hyps :=
    repeat (rewrite_mod_small_in_hyps || rewrite_mod_mod_small_in_hyps).
  Ltac rewrite_mod_small_in_all := repeat (rewrite_mod_small || rewrite_mod_small_in_hyps).
  Ltac rewrite_mod_mod_small_in_all := repeat (rewrite_mod_mod_small || rewrite_mod_mod_small_in_hyps).
  Ltac rewrite_mod_small_more_in_all := repeat (rewrite_mod_small_more || rewrite_mod_small_more_in_hyps).
End Z.
