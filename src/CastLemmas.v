Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Export Crypto.Language.Pre.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Logic.ProdForall.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.

Import EqNotations.
Module ident.
  Local Transparent ident.cast.
  Section with_cast.
    Context {cast_outside_of_range : zrange -> Z -> Z}.

    Local Notation cast := (@ident.cast cast_outside_of_range).

    Lemma cast_opp' r v : (-cast (-r) (-v) = cast r v)%Z.
    Proof.
      pose proof (ZRange.goodb_normalize r); cbv [ZRange.goodb] in *.
      cbv [cast ident.is_more_pos_than_neg]; rewrite !ZRange.normalize_opp, !ZRange.opp_involutive, !Z.opp_involutive.
      repeat change (lower (-?r)) with (-upper r)%Z.
      repeat change (upper (-?r)) with (-lower r)%Z.
      destruct (ZRange.normalize r) as [l u]; clear r; cbn [lower upper] in *.
      rewrite !Z.abs_opp.
      repeat first [ progress split_andb
                   | progress rewrite ?Bool.andb_false_iff in *
                   | progress rewrite ?Bool.orb_true_iff in *
                   | progress rewrite ?Bool.orb_false_iff in *
                   | progress destruct_head'_and
                   | progress Z.ltb_to_lt
                   | progress subst
                   | rewrite !Z.sub_opp_r
                   | rewrite !Z.opp_involutive
                   | rewrite !Z.add_0_r
                   | rewrite !Z.sub_0_r
                   | rewrite !Z.sub_diag
                   | rewrite !Z.mod_1_r
                   | progress change (- (-1))%Z with 1%Z
                   | progress change (0 - 1)%Z with (-1)%Z
                   | progress change (-0)%Z with 0%Z
                   | lia
                   | match goal with
                     | [ H : ?x = ?x |- _ ] => clear H
                     | [ H : (?x <= ?x)%Z |- _ ] => clear H
                     | [ H : ?T, H' : ?T |- _ ] => clear H'
                     | [ H : (-?x = -?y)%Z |- _ ] => assert (x = y) by lia; clear H
                     | [ H : (0 <= - ?x)%Z |- _ ] => assert (x <= 0)%Z by lia; clear H
                     | [ H : (?x > ?y)%Z |- _ ] => assert (y < x)%Z by lia; clear H
                     | [ H : (?x >= ?y)%Z |- _ ] => assert (y <= x)%Z by lia; clear H
                     | [ H : (- ?y < -?x)%Z |- _ ] => assert (x < y)%Z by lia; clear H
                     | [ H : (?x <= ?y)%Z, H' : (?y <= ?x)%Z |- _ ] => assert (x = y) by lia; clear H H'
                     (*| [ H : Z.abs ?l = Z.abs ?u |- _ ] => progress cbv [ZRange.opp]; cbn [lower upper]*)
                     | [ H : (?l <= ?u)%Z, H' : (?u < 0)%Z, H'' : context[Z.abs ?l] |- _ ]
                       => rewrite (Z.abs_neq l), (Z.abs_neq u) in * by lia
                     | [ H : (?l <= ?u)%Z, H' : (0 < ?l)%Z, H'' : context[Z.abs ?l] |- _ ]
                       => rewrite (Z.abs_eq l), (Z.abs_eq u) in * by lia
                     | [ |- context[(?x mod (-?a + ?b + 1))%Z] ]
                       => replace (x mod (-a + b + 1))%Z with (-((-x) mod (- - (a - b - 1))))%Z
                         by (rewrite !Zmod_opp_opp, !Z.opp_involutive; apply f_equal2; lia)
                     | [ |- context[(?x mod (?a - ?b + 1))%Z] ]
                       => replace (x mod (a - b + 1))%Z with (-((-x) mod (- - (b - a - 1))))%Z
                         by (rewrite !Zmod_opp_opp, !Z.opp_involutive; apply f_equal2; lia)
                     | [ |- context[(?x mod (-1))%Z] ]
                       => replace ((x mod (-1)))%Z with (-((-x) mod (- - 1)))%Z
                         by (rewrite !Zmod_opp_opp, !Z.opp_involutive; apply f_equal2; lia)
                     end
                   | progress destruct_head'_or
                   | break_innermost_match_step ].
    Qed.

    Lemma cast_in_normalized_bounds r v : is_bounded_by_bool v (ZRange.normalize r) = true -> cast r v = v.
    Proof. cbv [cast is_bounded_by_bool]; break_innermost_match; congruence. Qed.

    Lemma cast_in_bounds r v : is_bounded_by_bool v r = true -> cast r v = v.
    Proof.
      intro; apply cast_in_normalized_bounds, ZRange.is_bounded_by_normalize; assumption.
    Qed.

    Lemma cast_always_bounded r v : is_bounded_by_bool (cast r v) (ZRange.normalize r) = true.
    Proof.
      pose proof (ZRange.goodb_normalize r); cbv [ZRange.goodb] in *.
      cbv [cast]; break_innermost_match; Z.div_mod_to_quot_rem.
      all: destruct (ZRange.normalize r) as [l u]; clear r; cbn [lower upper ZRange.opp] in *.
      all: cbv [is_bounded_by_bool]; cbn [lower upper].
      all: repeat first [ progress rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff in *
                        | rewrite !Z.leb_le in *
                        | progress destruct_head'_and
                        | lia ].
    Qed.

    Lemma cast_bounded r v : (lower r <= upper r)%Z -> is_bounded_by_bool (cast r v) r = true.
    Proof.
      intro H; replace r with (ZRange.normalize r) at 2; [ apply cast_always_bounded | ].
      cbv [ZRange.normalize lower upper] in *; destruct r; split_min_max; reflexivity.
    Qed.

    Lemma cast_cases r v
      : is_bounded_by_bool (cast r v) (ZRange.normalize r) = true
        /\ ((is_bounded_by_bool v (ZRange.normalize r) = true /\ cast r v = v)
            \/ is_bounded_by_bool v (ZRange.normalize r) = false).
    Proof.
      split; [ apply cast_always_bounded | ].
      pose proof (cast_in_normalized_bounds r v).
      edestruct is_bounded_by_bool; tauto.
    Qed.

    (*
    Lemma cast_out_of_bounds_in_range_pos r v
      : ident.is_more_pos_than_neg (ZRange.normalize r) v = true
        -> is_bounded_by_bool v (ZRange.normalize r) = false
        -> is_bounded_by_bool (cast_outside_of_range (ZRange.normalize r) v) (ZRange.normalize r) = true
        -> cast r v = cast_outside_of_range (ZRange.normalize r) v.
    Proof.
      cbv [cast is_bounded_by_bool]; break_innermost_match; try congruence; intros.
      pose proof (ZRange.goodb_normalize r); cbv [ZRange.goodb] in *.
      split_andb; Z.ltb_to_lt; try lia.
      match goal with
      | [ |- context[(?a mod ?b)%Z] ]
        => cut ((a / b) = 0)%Z
      end.
      all: Z.div_mod_to_quot_rem; nia.
    Qed.
     *)

    (*
    Lemma cast_out_of_bounds_in_range_neg r v
      : ident.is_more_pos_than_neg (ZRange.normalize r) v = false
        -> is_bounded_by_bool v (ZRange.normalize r) = false
        -> is_bounded_by_bool (-cast_outside_of_range (-ZRange.normalize r) (-v)) (ZRange.normalize r) = true
        -> cast r v = (-cast_outside_of_range (-ZRange.normalize r) (-v))%Z.
    Proof.
      cbv [cast is_bounded_by_bool]; break_innermost_match; try congruence; intros.
      pose proof (ZRange.goodb_normalize r); cbv [ZRange.goodb] in *.
      split_andb; Z.ltb_to_lt; try lia.
      repeat change (lower (-?r)) with (-upper r)%Z.
      repeat change (upper (-?r)) with (-lower r)%Z.
      match goal with
      | [ |- context[(?a mod ?b)%Z] ]
        => cut ((a / b) = 0)%Z
      end.
      all: Z.div_mod_to_quot_rem; nia.
    Qed.
     *)

    (*
    Lemma cast_out_of_bounds_in_range r v
      : is_bounded_by_bool v (ZRange.normalize r) = false
        -> (ident.is_more_pos_than_neg (ZRange.normalize r) v = true -> is_bounded_by_bool (cast_outside_of_range (ZRange.normalize r) v) (ZRange.normalize r) = true)
        -> (ident.is_more_pos_than_neg (ZRange.normalize r) v = false -> is_bounded_by_bool (-cast_outside_of_range (-ZRange.normalize r) (-v)) (ZRange.normalize r) = true)
        -> cast r v = if ident.is_more_pos_than_neg (ZRange.normalize r) v
                      then cast_outside_of_range (ZRange.normalize r) v
                      else (-cast_outside_of_range (-ZRange.normalize r) (-v))%Z.
    Proof.
      pose proof (cast_out_of_bounds_in_range_pos r v).
      pose proof (cast_out_of_bounds_in_range_neg r v).
      break_innermost_match; intros; auto.
    Qed.
     *)

    (*
    Lemma cast_out_of_bounds_simple r v
      : (is_bounded_by_bool v (ZRange.normalize r) = true -> cast_outside_of_range (ZRange.normalize r) v = v)
        -> (ident.is_more_pos_than_neg (ZRange.normalize r) v = false -> (is_bounded_by_bool (-v) (-ZRange.normalize r))%Z = true -> (-cast_outside_of_range (-ZRange.normalize r) (-v) = v)%Z)
        -> (ident.is_more_pos_than_neg (ZRange.normalize r) v = true -> is_bounded_by_bool (cast_outside_of_range (ZRange.normalize r) v) (ZRange.normalize r) = true)
        -> (ident.is_more_pos_than_neg (ZRange.normalize r) v = false -> is_bounded_by_bool (-cast_outside_of_range (-ZRange.normalize r) (-v)) (ZRange.normalize r) = true)
        -> cast r v = if ident.is_more_pos_than_neg (ZRange.normalize r) v
                      then cast_outside_of_range (ZRange.normalize r) v
                      else (-cast_outside_of_range (-ZRange.normalize r) (-v))%Z.
    Proof.
      pose proof (cast_out_of_bounds_in_range r v).
      assert (is_bounded_by_bool (-v) (-ZRange.normalize r) = is_bounded_by_bool v (ZRange.normalize r)).
      { cbv [is_bounded_by_bool].
        repeat change (lower (-?r)) with (-upper r)%Z.
        repeat change (upper (-?r)) with (-lower r)%Z.
        cbv [andb]; break_innermost_match; Z.ltb_to_lt; break_match; Z.ltb_to_lt; try lia; try reflexivity.
        symmetry; Z.ltb_to_lt; lia. }
      destruct (is_bounded_by_bool v (ZRange.normalize r)) eqn:?.
      { rewrite cast_in_normalized_bounds by assumption; intros; symmetry; break_innermost_match; auto. }
      { auto. }
    Qed.
     *)

    Lemma is_more_pos_then_neg_0_u u v
      : (0 <= u)%Z
        -> ident.is_more_pos_than_neg (ZRange.normalize r[0~>u]) v = true.
    Proof using Type.
      intro.
      cbv [ident.is_more_pos_than_neg]; cbn [upper lower].
      rewrite (proj1 ZRange.normalize_id_iff_goodb)
        by (cbv [ZRange.goodb lower upper]; Z.ltb_to_lt; assumption).
      cbn [lower upper].
      rewrite Z.abs_0, Z.abs_eq by assumption.
      cbv [andb orb]; break_innermost_match; Z.ltb_to_lt; try lia; reflexivity.
    Qed.

    (*
    Lemma cast_out_of_bounds_simple_0 u v
      : (0 <= u)%Z
        -> ((0 <= v <= u)%Z -> cast_outside_of_range r[0~>u] v = v)
        -> (0 <= cast_outside_of_range r[0~>u] v <= u)%Z
        -> cast r[0~>u] v = cast_outside_of_range r[0~>u] v.
    Proof.
      pose proof (cast_out_of_bounds_simple r[0~>u] v) as H.
      intro H0.
      pose proof (is_more_pos_then_neg_0_u u v H0) as H1.
      rewrite H1 in *.
      rewrite (proj1 ZRange.normalize_id_iff_goodb) in H
        by (cbv [ZRange.goodb lower upper]; Z.ltb_to_lt; assumption).
      cbv [is_bounded_by_bool ZRange.opp] in *; cbn [lower upper] in *; rewrite ?Bool.andb_true_iff, ?Z.leb_le in *.
      intros; apply H; intros; destruct_head'_and; repeat apply conj; Z.ltb_to_lt; auto; try congruence.
    Qed.
     *)
    (*
    Lemma cast_out_of_bounds_simple_0_mod u v
      : (0 <= u)%Z
        -> ((0 <= v <= u)%Z -> cast_outside_of_range r[0~>u] v = v)
        -> (cast r[0~>u] v = (cast_outside_of_range r[0~>u] v) mod (u + 1))%Z.
    Proof.
      intro H0.
      pose proof (is_more_pos_then_neg_0_u u v H0) as H1.
      cbv [cast]; rewrite H1.
      rewrite (proj1 ZRange.normalize_id_iff_goodb)
        by (cbv [ZRange.goodb lower upper]; Z.ltb_to_lt; assumption).
      cbn [lower upper].
      rewrite !Z.sub_0_r, !Z.add_0_r.
      break_innermost_match; split_andb; Z.ltb_to_lt; intro H';
        rewrite ?H' by lia; Z.rewrite_mod_small; reflexivity.
    Qed.
     *)

    Lemma cast_out_of_bounds_simple_0_mod u v
      : (0 <= u)%Z
        -> ((cast_outside_of_range r[0~>u] v) mod (u + 1) = v mod (u + 1))%Z
        -> (cast r[0~>u] v = (cast_outside_of_range r[0~>u] v) mod (u + 1))%Z.
    Proof.
      intro H0.
      pose proof (is_more_pos_then_neg_0_u u v H0) as H1.
      cbv [cast]; rewrite H1.
      rewrite (proj1 ZRange.normalize_id_iff_goodb)
        by (cbv [ZRange.goodb lower upper]; Z.ltb_to_lt; assumption).
      cbn [lower upper].
      rewrite !Z.sub_0_r, !Z.add_0_r.
      break_innermost_match; split_andb; Z.ltb_to_lt; intro H';
        rewrite ?H' by lia; Z.rewrite_mod_small; reflexivity.
    Qed.

    (* N.B. This lemma depends on the hard-coded behavior of casting
        out of range being modulo, and hence we label it
        "platform-specific". *)
    Lemma platform_specific_cast_0_is_mod u v
      : (0 <= u)%Z
        -> (cast r[0~>u] v = v mod (u + 1))%Z.
    Proof.
      intro H0.
      pose proof (is_more_pos_then_neg_0_u u v H0) as H1.
      cbv [cast]; rewrite H1.
      rewrite (proj1 ZRange.normalize_id_iff_goodb)
        by (cbv [ZRange.goodb lower upper]; Z.ltb_to_lt; assumption).
      cbn [lower upper].
      rewrite !Z.sub_0_r, !Z.add_0_r.
      break_innermost_match; split_andb; Z.ltb_to_lt; Z.rewrite_mod_small; reflexivity.
    Qed.

    Lemma cast_normalize r v : cast (ZRange.normalize r) v = cast r v.
    Proof.
      cbv [cast]; rewrite ZRange.normalize_idempotent; reflexivity.
    Qed.
  End with_cast.

  Lemma cast_idempotent_gen {cast_outside_of_range1 cast_outside_of_range2}
        r1 r2 v
    : is_tighter_than_bool (ZRange.normalize r1) (ZRange.normalize r2) = true
      -> ident.cast cast_outside_of_range2 r2 (ident.cast cast_outside_of_range1 r1 v)
         = ident.cast cast_outside_of_range1 r1 v.
  Proof.
    intro H; apply (@cast_in_normalized_bounds _ r2).
    eapply ZRange.is_bounded_by_of_is_tighter_than, cast_always_bounded; assumption.
  Qed.

  Lemma cast_idempotent {cast_outside_of_range1 cast_outside_of_range2}
        r v
    : ident.cast cast_outside_of_range2 r (ident.cast cast_outside_of_range1 r v)
      = ident.cast cast_outside_of_range1 r v.
  Proof.
    apply cast_idempotent_gen; change (is_true (is_tighter_than_bool (ZRange.normalize r) (ZRange.normalize r))); reflexivity.
  Qed.
End ident.
