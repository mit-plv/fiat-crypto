Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relations.
Require Export Crypto.Language.PreExtra.
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
    Local Notation cast := ident.cast (only parsing).

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

    Lemma cast_out_of_bounds_simple_0_mod u v
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
      break_innermost_match; split_andb; Z.ltb_to_lt;
        Z.rewrite_mod_small; reflexivity.
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

  Lemma cast_idempotent_gen
        r1 r2 v
    : is_tighter_than_bool (ZRange.normalize r1) (ZRange.normalize r2) = true
      -> ident.cast r2 (ident.cast r1 v)
         = ident.cast r1 v.
  Proof.
    intro H; apply (@cast_in_normalized_bounds r2).
    eapply ZRange.is_bounded_by_of_is_tighter_than, cast_always_bounded; assumption.
  Qed.

  Lemma cast_idempotent
        r v
    : ident.cast r (ident.cast r v)
      = ident.cast r v.
  Proof.
    apply cast_idempotent_gen; change (is_true (is_tighter_than_bool (ZRange.normalize r) (ZRange.normalize r))); reflexivity.
  Qed.
End ident.
