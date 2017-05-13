Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Div.
Local Open Scope Z_scope.

Module Z.
  (** * [Z.simplify_fractions_le] *)
  (** The culmination of this series of tactics,
      [Z.simplify_fractions_le], will use the fact that [a * (b / c) <=
      (a * b) / c], and do some reasoning modulo associativity and
      commutativity in [Z] to perform such a reduction.  It may leave
      over goals if it cannot prove that some denominators are non-zero.
      If the rewrite [a * (b / c)] → [(a * b) / c] is safe to do on the
      LHS of the goal, this tactic should not turn a solvable goal into
      an unsolvable one.

      After running, the tactic does some basic rewriting to simplify
      fractions, e.g., that [a * b / b = a]. *)
  Ltac split_sums_step :=
    match goal with
    | [ |- _ + _ <= _ ]
      => etransitivity; [ eapply Z.add_le_mono | ]
    | [ |- _ - _ <= _ ]
      => etransitivity; [ eapply Z.sub_le_mono | ]
    end.
  Ltac split_sums :=
    try (split_sums_step; [ split_sums.. | ]).
  Ltac pre_reorder_fractions_step :=
    match goal with
    | [ |- context[?x / ?y * ?z] ]
      => lazymatch z with
         | context[_ / _] => fail
         | _ => idtac
         end;
         rewrite (Z.mul_comm (x / y) z)
    | _ => let LHS := match goal with |- ?LHS <= ?RHS => LHS end in
           match LHS with
           | context G[?x * (?y / ?z)]
             => let G' := context G[(x * y) / z] in
                transitivity G'
           end
    end.
  Ltac pre_reorder_fractions :=
    try first [ split_sums_step; [ pre_reorder_fractions.. | ]
              | pre_reorder_fractions_step; [ .. | pre_reorder_fractions ] ].
  Ltac split_comparison :=
    match goal with
    | [ |- ?x <= ?x ] => reflexivity
    | [ H : _ >= _ |- _ ]
      => apply Z.ge_le_iff in H
    | [ |- ?x * ?y <= ?z * ?w ]
      => lazymatch goal with
         | [ H : 0 <= x |- _ ] => idtac
         | [ H : x < 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0)
         end;
         [ ..
         | lazymatch goal with
           | [ H : 0 <= y |- _ ] => idtac
           | [ H : y < 0 |- _ ] => fail
           | _ => destruct (Z_lt_le_dec y 0)
           end;
           [ ..
           | apply Zmult_le_compat; [ | | assumption | assumption ] ] ]
    | [ |- ?x / ?y <= ?z / ?y ]
      => lazymatch goal with
         | [ H : 0 < y |- _ ] => idtac
         | [ H : y <= 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec 0 y)
         end;
         [ apply Z_div_le; [ apply Z.gt_lt_iff; assumption | ]
         | .. ]
    | [ |- ?x / ?y <= ?x / ?z ]
      => lazymatch goal with
         | [ H : 0 <= x |- _ ] => idtac
         | [ H : x < 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0)
         end;
         [ ..
         | lazymatch goal with
           | [ H : 0 < z |- _ ] => idtac
           | [ H : z <= 0 |- _ ] => fail
           | _ => destruct (Z_lt_le_dec 0 z)
           end;
           [ apply Z.div_le_compat_l; [ assumption | split; [ assumption | ] ]
           | .. ] ]
    | [ |- _ + _ <= _ + _ ]
      => apply Z.add_le_mono
    | [ |- _ - _ <= _ - _ ]
      => apply Z.sub_le_mono
    | [ |- ?x * (?y / ?z) <= (?x * ?y) / ?z ]
      => apply Z.div_mul_le
    end.
  Ltac split_comparison_fin_step :=
    match goal with
    | _ => assumption
    | _ => lia
    | _ => progress subst
    | [ H : ?n * ?m < 0 |- _ ]
      => apply (proj1 (Z.lt_mul_0 n m)) in H; destruct H as [ [??]|[??] ]
    | [ H : ?n / ?m < 0 |- _ ]
      => apply (proj1 (Z.lt_div_0 n m)) in H; destruct H as [ [ [??]|[??] ] ? ]
    | [ H : (?x^?y) <= ?n < _, H' : ?n < 0 |- _ ]
      => assert (0 <= x^y) by Z.zero_bounds; lia
    | [ H : (?x^?y) < 0 |- _ ]
      => assert (0 <= x^y) by Z.zero_bounds; lia
    | [ H : (?x^?y) <= 0 |- _ ]
      => let H' := fresh in
         assert (H' : 0 <= x^y) by Z.zero_bounds;
         assert (x^y = 0) by lia;
         clear H H'
    | [ H : _^_ = 0 |- _ ]
      => apply Z.pow_eq_0_iff in H; destruct H as [ ?|[??] ]
    | [ H : 0 <= ?x, H' : ?x - 1 < 0 |- _ ]
      => assert (x = 0) by lia; clear H H'
    | [ |- ?x <= ?y ] => is_evar x; reflexivity
    | [ |- ?x <= ?y ] => is_evar y; reflexivity
    end.
  Ltac split_comparison_fin := repeat split_comparison_fin_step.
  Ltac simplify_fractions_step :=
    match goal with
    | _ => rewrite Z.div_mul by (try apply Z.pow_nonzero; Z.zero_bounds)
    | [ |- context[?x * ?y / ?x] ]
      => rewrite (Z.mul_comm x y)
    | [ |- ?x <= ?x ] => reflexivity
    end.
  Ltac simplify_fractions := repeat simplify_fractions_step.
  Ltac simplify_fractions_le :=
    pre_reorder_fractions;
    [ repeat split_comparison; split_comparison_fin; Z.zero_bounds..
    | simplify_fractions ].
End Z.
