Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.FixedWordSizesEquality.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.

Local Open Scope Z_scope.

Ltac break_t_step :=
  first [ progress destruct_head'_and
        | progress destruct_head'_or
        | progress destruct_head'_prod
        | progress split_andb
        | break_innermost_match_step ].

Ltac fin_t :=
  first [ reflexivity
        | assumption
        | match goal with
          | [ |- and _ _ ]
            => first [ split; [ | solve [ fin_t ] ]
                     | split; [ solve [ fin_t ] | ] ];
               try solve [ fin_t ]
          end
        | omega ].

Ltac specializer_t_step :=
  first [ progress specialize_by_assumption
        | progress specialize_by fin_t ].

Ltac Zarith_t_step :=
  first [ match goal with
          | [ H : (?x <= ?y)%Z, H' : (?y <= ?x)%Z |- _ ]
            => assert (x = y) by omega; clear H H'
          end
        | progress Z.ltb_to_lt_in_context ].
Ltac Zarith_land_lor_t_step :=
  match goal with
  | [ |- _ <= Z.lor _ _ <= _ ]
    => split; etransitivity; [ | apply Z.lor_bounds; omega | apply Z.lor_bounds; omega | ]
  | [ |- 2^Z.log2_up (?x + 1) - 1 <= 2^Z.log2_up (?y + 1) - 1 ]
    => let H := fresh in assert (H : x <= y) by omega; rewrite H; reflexivity
  end.
Ltac word_arith_t :=
  match goal with
  | [ |- (0 <= FixedWordSizes.wordToZ ?w <= 2^2^Z.of_nat ?logsz - 1)%Z ]
    => clear; pose proof (@wordToZ_range logsz w); autorewrite with push_Zof_nat zsimplify_const in *; try omega
  end.

Ltac revert_min_max :=
  repeat match goal with
         | [ H : context[Z.min _ _] |- _ ] => revert H
         | [ H : context[Z.max _ _] |- _ ] => revert H
         end.
Ltac split_min_max :=
  repeat match goal with
         | [ H : (?a <= ?b)%Z |- context[Z.max ?a ?b] ]
           => rewrite (Z.max_r a b) by omega
         | [ H : (?b <= ?a)%Z |- context[Z.max ?a ?b] ]
           => rewrite (Z.max_l a b) by omega
         | [ H : (?a <= ?b)%Z |- context[Z.min ?a ?b] ]
           => rewrite (Z.min_l a b) by omega
         | [ H : (?b <= ?a)%Z |- context[Z.min ?a ?b] ]
           => rewrite (Z.min_r a b) by omega
         | [ |- context[Z.max ?a ?b] ]
           => first [ rewrite (Z.max_l a b) by omega
                    | rewrite (Z.max_r a b) by omega ]
         | [ |- context[Z.min ?a ?b] ]
           => first [ rewrite (Z.min_l a b) by omega
                    | rewrite (Z.min_r a b) by omega ]
         | _ => revert_min_max; progress repeat apply Z.min_case_strong; intros
         | _ => revert_min_max; progress repeat apply Z.max_case_strong; intros
         end.

Ltac case_Zvar_nonneg_on x :=
  is_var x;
  lazymatch type of x with
  | Z => lazymatch goal with
         | [ H : (0 <= x)%Z |- _ ] => fail
         | [ H : (x < 0)%Z |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0); try omega
         end
  end.
Ltac case_Zvar_nonneg_step :=
  match goal with
  | [ |- context[?x] ]
    => case_Zvar_nonneg_on x
  end.
Ltac case_Zvar_nonneg := repeat case_Zvar_nonneg_step.

Ltac remove_binary_operation_le_hyps_step :=
  match goal with
  | [ H : (?f ?x ?y <= ?f ?x ?y')%Z |- _ ]
    => assert ((y = y') \/ (y < y' /\ 0 <= x))%Z by (assert (y <= y')%Z by omega; nia);
       clear H
  | [ H : (?f ?y ?x <= ?f ?y' ?x)%Z |- _ ]
    => assert ((y = y') \/ (y < y' /\ 0 <= x))%Z by (assert (y <= y')%Z by omega; nia);
       clear H
  | [ H : (?f ?x ?y <= ?f ?x ?y')%Z |- _ ]
    => assert ((y = y') \/ (y' < y /\ x <= 0))%Z by (assert (y' <= y)%Z by omega; nia);
       clear H
  | [ H : (?f ?y ?x <= ?f ?y' ?x)%Z |- _ ]
    => assert ((y = y') \/ (y' < y /\ x <= 0))%Z by (assert (y' <= y)%Z by omega; nia);
       clear H
  | [ H : ?T, H' : ?T |- _ ] => clear H'
  | [ H : ?A \/ (~?A /\ ?B), H' : ?A \/ (~?A /\ ?C) |- _ ]
    => assert (A \/ (~A /\ (B /\ C))) by (clear -H H'; tauto); clear H H'
  | _ => progress destruct_head' or; destruct_head' and; subst; try omega
  | [ |- (_ <= _ <= _)%Z ] => split
  | _ => case_Zvar_nonneg_step
  end.

Ltac saturate_with_shift_facts :=
  repeat match goal with
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?x << ?x'] ]
           => unique assert (x << x' <= y << y') by (apply Z.shiftl_le_mono; omega)
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?y << ?y'] ]
           => unique assert (x << x' <= y << y') by (apply Z.shiftl_le_mono; omega)
          | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?x >> ?y'] ]
            => unique assert (x >> y' <= y >> x') by (Z.shiftr_le_mono; omega)
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[?y >> ?x'] ]
           => unique assert (x >> y' <= y >> x') by (apply Z.shiftr_le_mono; omega)
         end.
Ltac saturate_with_all_shift_facts :=
  repeat match goal with
         | _ => progress saturate_with_shift_facts
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[Z.shiftl _ _] ]
           => unique assert (x << x' <= y << y') by (apply Z.shiftl_le_mono; omega)
         | [ H : ?x <= ?y, H' : ?x' <= ?y' |- context[Z.shiftr _ _] ]
           => unique assert (x >> y' <= y >> x') by (apply Z.shiftr_le_mono; omega)
         end.
Ltac preprocess_shift_min_max :=
  repeat first [ rewrite (Z.min_r (_ >> _) (_ >> _)) by (apply Z.shiftr_le_mono; omega)
               | rewrite (Z.min_l (_ >> _) (_ >> _)) by (apply Z.shiftr_le_mono; omega)
               | rewrite (Z.max_r (_ >> _) (_ >> _)) by (apply Z.shiftr_le_mono; omega)
               | rewrite (Z.max_l (_ >> _) (_ >> _)) by (apply Z.shiftr_le_mono; omega)
               | rewrite (Z.min_r (_ << _) (_ << _)) by (apply Z.shiftl_le_mono; omega)
               | rewrite (Z.min_l (_ << _) (_ << _)) by (apply Z.shiftl_le_mono; omega)
               | rewrite (Z.max_r (_ << _) (_ << _)) by (apply Z.shiftl_le_mono; omega)
               | rewrite (Z.max_l (_ << _) (_ << _)) by (apply Z.shiftl_le_mono; omega) ].
Ltac saturate_land_lor_facts :=
  repeat match goal with
         | [ |- context[Z.land ?x ?y] ]
           => let H := fresh in
              let H' := fresh in
              assert (H : 0 <= x) by omega;
              assert (H' : 0 <= y) by omega;
              unique pose proof (Z.land_upper_bound_r x y H H');
              unique pose proof (Z.land_upper_bound_l x y H H')
         | [ |- context[Z.land ?x ?y] ]
           => unique assert (0 <= Z.land x y) by (apply Z.land_nonneg; omega)
         | [ |- context[Z.land ?x ?y] ]
           => case_Zvar_nonneg_on x; case_Zvar_nonneg_on y
         | [ |- context[Z.lor ?x ?y] ]
           => let H := fresh in
              let H' := fresh in
              assert (H : 0 <= x) by omega;
              assert (H' : 0 <= y) by omega;
              unique pose proof (proj1 (Z.lor_bounds x y H H'));
              unique pose proof (proj2 (Z.lor_bounds x y H H'))
         | [ |- context[Z.lor ?x ?y] ]
           => unique assert (0 <= Z.lor x y) by (apply Z.lor_nonneg; omega)
         | [ |- context[Z.lor ?x ?y] ]
           => case_Zvar_nonneg_on x; case_Zvar_nonneg_on y
         end.
Ltac clean_neg :=
  repeat match goal with
         | [ H : (-?x) < 0 |- _ ] => assert (0 <= x) by omega; assert (x <> 0) by omega; clear H
         | [ H : -?x <= -?y |- _ ] => apply Z.opp_le_mono in H
         | [ |- -?x <= -?y ] => apply Z.opp_le_mono
         | _ => progress rewrite <- Z.opp_le_mono in *
         end.
Ltac replace_with_neg x :=
  assert (x = -(-x)) by omega; generalize dependent (-x);
  let x' := fresh in
  rename x into x'; intro x; intros; subst x';
  clean_neg.
Ltac replace_all_neg_with_pos :=
  repeat match goal with
         | [ H : ?x < 0 |- _ ] => replace_with_neg x
         end.
Ltac handle_shift_neg :=
  repeat first [ rewrite !Z.shiftr_opp_r
               | rewrite !Z.shiftl_opp_r
               | rewrite !Z.shiftr_opp_l
               | rewrite !Z.shiftl_opp_l ].

Ltac handle_four_corners_step_fast :=
  first [ progress destruct_head Bounds.t
        | progress cbv [Bounds.four_corners] in *
        | progress subst
        | Zarith_t_step
        | progress split_min_max
        | omega
        | nia ].
Ltac handle_four_corners_step :=
  first [ handle_four_corners_step_fast
        | remove_binary_operation_le_hyps_step ].
Ltac handle_four_corners :=
  lazymatch goal with
  | [ |- (ZRange.lower (Bounds.four_corners _ _ _) <= _ <= _)%Z ]
    => idtac
  end;
  repeat handle_four_corners_step.

Ltac rewriter_t :=
  first [ rewrite !Bool.andb_true_iff
        | rewrite !Bool.andb_false_iff
        | rewrite !Bool.orb_true_iff
        | rewrite !Bool.orb_false_iff
        | rewrite !Z.abs_opp
        | rewrite !Z.max_log2_up
        | rewrite !Z.add_max_distr_r
        | rewrite !Z.add_max_distr_l
        | rewrite wordToZ_ZToWord by (autorewrite with push_Zof_nat zsimplify_const; omega)
        | match goal with
          | [ H : _ |- _ ]
            => first [ rewrite !Bool.andb_true_iff in H
                     | rewrite !Bool.andb_false_iff in H
                     | rewrite !Bool.orb_true_iff in H
                     | rewrite !Bool.orb_false_iff in H ]
          end ].
