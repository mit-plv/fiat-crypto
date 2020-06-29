Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.DestructHead.

Module ZRange.
  Import Operations.ZRange.
  Local Open Scope zrange_scope.
  Local Coercion is_true : bool >-> Sortclass.

  Local Notation eta v := r[ lower v ~> upper v ].

  Local Ltac t_step :=
    first [ reflexivity
          | progress destruct_head' zrange
          | progress cbv -[Z.min Z.max Z.le Z.lt Z.ge Z.gt andb Z.leb Z.geb] in *
          | progress split_min_max
          | match goal with
            | [ |- _ = _ :> zrange ] => apply f_equal2
            end
          | lia
          | solve [ auto ] ].
  Local Ltac t := repeat t_step.

  Lemma flip_flip v : flip (flip v) = v.
  Proof. destruct v; reflexivity. Qed.

  Lemma normalize_flip v : normalize (flip v) = normalize v.
  Proof. t. Qed.

  Lemma normalize_idempotent v : normalize (normalize v) = normalize v.
  Proof. t. Qed.

  Definition normalize_or v : normalize v = v \/ normalize v = flip v.
  Proof. t. Qed.

  Lemma union_comm r1 r2 : union r1 r2 = union r2 r1.
  Proof. t. Qed.

  Lemma normalize_union_normalize r1 r2 : normalize (union (normalize r1) (normalize r2)) = union (normalize r1) (normalize r2).
  Proof. t. Qed.

  Local Ltac t2_step :=
    first [ t_step
          | rewrite !Bool.andb_true_iff
          | rewrite !Z.leb_le
          | rewrite !Z.leb_gt
          | rewrite Bool.andb_true_iff in *
          | rewrite Z.leb_le in *
          | rewrite Z.leb_gt in *
          | progress intros
          | match goal with
            | [ H : context[andb _ _ = true] |- _ ] => setoid_rewrite Bool.andb_true_iff in H
            | [ |- context[andb _ _ = true] ] => setoid_rewrite Bool.andb_true_iff
            | [ H : context[Z.leb _ _ = true] |- _ ] => setoid_rewrite Z.leb_le in H
            | [ |- context[Z.leb _ _ = true] ] => setoid_rewrite Z.leb_le
            | [ H : context[Z.leb _ _ = false] |- _ ] => setoid_rewrite Z.leb_gt in H
            | [ |- context[Z.leb _ _ = false] ] => setoid_rewrite Z.leb_gt
            | [ |- and _ _ ] => apply conj
            | [ |- or _ (true = false) ] => left
            | [ |- or _ (false = true) ] => left
            | [ |- or _ (?x = ?x) ] => right
            | [ H : true = false |- _ ] => exfalso; clear -H; discriminate
            | [ H : Build_zrange _ _ = Build_zrange _ _ |- _ ] => inversion H; clear H
            end
          | progress specialize_by lia
          | progress destruct_head'_or ].

  Lemma goodb_normalize r : goodb (normalize r) = true.
  Proof. repeat t2_step. Qed.

  Lemma normalize_id_iff_goodb {r} : goodb r = true <-> normalize r = r.
  Proof. repeat t2_step. Qed.

  Lemma normalize_id_pow2 (k : Z) (k_nonneg : (0 <= k)%Z)
    : normalize r[0 ~> 2 ^ k - 1] = r[0 ~> 2 ^ k - 1].
  Proof.
    assert (0 < 2 ^ k)%Z by auto with zarith.
    assert (0 <= 2 ^ k - 1)%Z by lia.
    repeat t2_step.
  Qed.

  Lemma is_tighter_than_bool_extend_land_lor_bounds r : is_tighter_than_bool r (extend_land_lor_bounds r) = true.
  Proof. repeat t2_step. Qed.

  Lemma is_bounded_by_iff_is_tighter_than r1 r2
    : (forall v, is_bounded_by_bool v r1 = true -> is_bounded_by_bool v r2 = true)
      <-> (is_tighter_than_bool r1 r2 = true \/ goodb r1 = false).
  Proof. repeat t2_step; specialize_all_ways; repeat t2_step. Qed.

  Lemma is_bounded_by_iff_is_tighter_than_good r1 r2 (Hgood : goodb r1 = true)
    : (forall v, is_bounded_by_bool v r1 = true -> is_bounded_by_bool v r2 = true)
      <-> (is_tighter_than_bool r1 r2 = true).
  Proof. rewrite is_bounded_by_iff_is_tighter_than; intuition (congruence || auto). Qed.

  Global Instance is_tighter_than_bool_Reflexive : Reflexive is_tighter_than_bool.
  Proof.
    cbv [is_tighter_than_bool is_true]; cbn [lower upper]; repeat intro.
    rewrite ?Bool.andb_true_iff, ?Z.leb_le_iff in *; repeat apply conj; reflexivity.
  Qed.
  Global Instance is_tighter_than_bool_Transitive : Transitive is_tighter_than_bool.
  Proof.
    cbv [is_tighter_than_bool is_true]; cbn [lower upper]; repeat intro.
    rewrite ?Bool.andb_true_iff, ?Z.leb_le_iff in *; repeat apply conj; etransitivity; destruct_head'_and; eassumption.
  Qed.

  Lemma is_bounded_by_normalize r
    : forall v, is_bounded_by_bool v r = true -> is_bounded_by_bool v (normalize r) = true.
  Proof.
    apply <- is_bounded_by_iff_is_tighter_than; destruct (goodb r) eqn:?; [ left | right; reflexivity ].
    rewrite (proj1 normalize_id_iff_goodb) by assumption; change (is_true (is_tighter_than_bool r r)); reflexivity.
  Qed.

  Lemma goodb_of_is_bounded_by_bool v r : is_bounded_by_bool v r = true -> goodb r = true.
  Proof. repeat t2_step. Qed.

  Lemma is_tighter_than_bool_normalize_of_goodb r : goodb r = true -> is_tighter_than_bool r (normalize r) = true.
  Proof. repeat t2_step. Qed.

  Lemma normalize_is_tighter_than_bool_of_goodb r : goodb r = true -> is_tighter_than_bool (normalize r) r = true.
  Proof. repeat t2_step. Qed.

  Lemma is_bounded_by_of_is_tighter_than r1 r2 (H : is_tighter_than_bool r1 r2 = true)
    : (forall v, is_bounded_by_bool v r1 = true -> is_bounded_by_bool v r2 = true).
  Proof. apply is_bounded_by_iff_is_tighter_than; auto. Qed.

  Lemma is_bounded_by_bool_Proper_if_sumbool_union_dep {A B} (b : sumbool A B) x y rx ry
    : (A -> is_bounded_by_bool x rx = true)
      -> (B -> is_bounded_by_bool y ry = true)
      -> is_bounded_by_bool (if b then x else y) (Operations.ZRange.union rx ry) = true.
  Proof.
    destruct b; cbv [Operations.ZRange.union is_bounded_by_bool];
      intros; specialize_by_assumption; Bool.split_andb; rewrite Bool.andb_true_iff; split; Z.ltb_to_lt; cbn [lower upper] in *; split_min_max.
    all: lia.
  Qed.

  Lemma is_bounded_by_bool_Proper_if_sumbool_union {A B} (b : sumbool A B) x y rx ry
    : is_bounded_by_bool x rx = true
      -> is_bounded_by_bool y ry = true
      -> is_bounded_by_bool (if b then x else y) (Operations.ZRange.union rx ry) = true.
  Proof. intros; apply is_bounded_by_bool_Proper_if_sumbool_union_dep; auto. Qed.

  Lemma is_bounded_by_bool_Proper_if_bool_union_dep (b : bool) x y rx ry
    : (b = true -> is_bounded_by_bool x rx = true)
      -> (b = false -> is_bounded_by_bool y ry = true)
      -> is_bounded_by_bool (if b then x else y) (Operations.ZRange.union rx ry) = true.
  Proof. pose proof (is_bounded_by_bool_Proper_if_sumbool_union_dep (Sumbool.sumbool_of_bool b) x y rx ry); destruct b; assumption. Qed.

  Lemma is_bounded_by_bool_Proper_if_bool_union (b : bool) x y rx ry
    : is_bounded_by_bool x rx = true
      -> is_bounded_by_bool y ry = true
      -> is_bounded_by_bool (if b then x else y) (Operations.ZRange.union rx ry) = true.
  Proof. intros; apply is_bounded_by_bool_Proper_if_bool_union_dep; auto. Qed.

  Lemma is_bounded_by_bool_opp x r : is_bounded_by_bool (Z.opp x) (ZRange.opp r) = is_bounded_by_bool x r.
  Proof.
    cbv [is_bounded_by_bool andb opp]; cbn [lower upper]; break_match; Z.ltb_to_lt; break_match; Z.ltb_to_lt;
      try (symmetry; progress Z.ltb_to_lt);
      try reflexivity;
      try lia.
  Qed.

  Lemma normalize_opp r : normalize (-r) = -(normalize r).
  Proof.
    cbv [normalize ZRange.opp]; cbn [lower upper].
    rewrite <- !Z.opp_min_distr, <- !Z.opp_max_distr.
    reflexivity.
  Qed.

  Lemma opp_involutive r : - - r = r.
  Proof.
    cbv [opp upper lower]; destruct r; rewrite !Z.opp_involutive; reflexivity.
  Qed.

  Lemma normalize_constant v : normalize (constant v) = constant v.
  Proof. repeat t2_step. Qed.

  Lemma is_bounded_by_bool_move_opp_normalize r v
    : is_bounded_by_bool v (ZRange.normalize (-r))
      = is_bounded_by_bool (-v) (ZRange.normalize r).
  Proof.
    rewrite <- is_bounded_by_bool_opp at 1.
    rewrite normalize_opp, opp_involutive; reflexivity.
  Qed.

  Lemma is_tighter_than_bool_constant r v
    : is_tighter_than_bool (ZRange.constant v) r
      = is_bounded_by_bool v r.
  Proof. reflexivity. Qed.

  Lemma is_bounded_by_bool_constant v
    : is_bounded_by_bool v (ZRange.constant v) = true.
  Proof. repeat t2_step. Qed.

  Lemma is_bounded_by_bool_normalize_constant v
    : is_bounded_by_bool v (ZRange.normalize (ZRange.constant v)) = true.
  Proof. repeat t2_step. Qed.

  Lemma is_bounded_by_bool_constant_iff v1 v2
    : is_bounded_by_bool v1 (ZRange.constant v2) = true <-> v1 = v2.
  Proof. repeat t2_step. Qed.

  Lemma is_bounded_by_bool_normalize_constant_iff v1 v2
    : is_bounded_by_bool v1 (ZRange.normalize (ZRange.constant v2)) = true <-> v1 = v2.
  Proof. repeat t2_step. Qed.

  Lemma is_tighter_than_bool_union_l r1 r2 : is_tighter_than_bool r1 (union r1 r2).
  Proof. repeat t2_step. Qed.

  Lemma is_tighter_than_bool_union_r r1 r2 : is_tighter_than_bool r2 (union r1 r2).
  Proof. repeat t2_step. Qed.

  Section goodb.
    Local Open Scope Z_scope.
    Local Open Scope zrange_scope.

    Lemma goodb_constant v : goodb (constant v) = true.
    Proof. repeat t2_step. Qed.

    Lemma goodb_apply_to_range f r
      : goodb (f (lower r)) = true -> goodb (f (upper r)) = true -> goodb (apply_to_range f r) = true.
    Proof. repeat t2_step. Qed.

    Lemma goodb_union r1 r2
      : goodb r1 = true -> goodb r2 = true -> goodb (union r1 r2) = true.
    Proof. repeat t2_step. Qed.

    Lemma goodb_apply_to_split_range f r
      : (lower r < 0 -> upper r <= -1 -> goodb (f r) = true)
        -> (lower r < 0 -> -1 < upper r -> goodb (f r[lower r ~> -1]) = true)
        -> (lower r <= 0 -> 0 <= upper r -> goodb (f r[0 ~> 0]) = true)
        -> (lower r < 1 -> 0 < upper r -> goodb (f r[1 ~> upper r]) = true)
        -> (1 <= lower r -> 0 < upper r -> goodb (f r) = true)
        -> goodb r = true \/ goodb (f r) = true
        -> goodb (apply_to_split_range f r) = true.
    Proof.
      cbv [apply_to_split_range split_range_at_0 lower upper orb andb]; break_innermost_match; Z.ltb_to_lt; intros.
      all: repeat first [ assumption
                        | match goal with
                          | [ H : goodb r[?l ~> ?u] = true |- _ ]
                            => let H' := fresh in
                               assert (H' : u < l) by lia; exfalso; clear -H H'; cbv [goodb ZRange.lower ZRange.upper] in H
                          end
                        | lia
                        | apply goodb_union
                        | progress specialize_by lia
                        | progress split_min_max
                        | progress destruct_head'_or
                        | progress Z.ltb_to_lt ].
    Qed.

    Local Ltac corners_t :=
      repeat ((apply goodb_apply_to_split_range + apply goodb_apply_to_range + apply goodb_constant); intros);
      try (constructor; solve [ corners_t ]).

    Lemma goodb_two_corners f r : goodb (two_corners f r) = true.
    Proof. corners_t. Qed.

    Lemma goodb_four_corners f r1 r2 : goodb (four_corners f r1 r2) = true.
    Proof. corners_t. Qed.

    Lemma goodb_eight_corners f r1 r2 r3 : goodb (eight_corners f r1 r2 r3) = true.
    Proof. corners_t. Qed.

    Lemma goodb_two_corners_and_zero f r1 : goodb (two_corners_and_zero f r1) = true.
    Proof. corners_t. Qed.

    Lemma goodb_four_corners_and_zero f r1 r2 : goodb (four_corners_and_zero f r1 r2) = true.
    Proof. corners_t. Qed.

    Lemma goodb_eight_corners_and_zero f r1 r2 r3 : goodb (eight_corners_and_zero f r1 r2 r3) = true.
    Proof. corners_t. Qed.

    Lemma goodb_log2 r : goodb (ZRange.log2 r) = true.
    Proof. apply goodb_two_corners. Qed.
    Lemma goodb_log2_up r : goodb (ZRange.log2_up r) = true.
    Proof. apply goodb_two_corners. Qed.
    Lemma goodb_add r1 r2 : goodb (ZRange.add r1 r2) = true.
    Proof. apply goodb_four_corners. Qed.
    Lemma goodb_sub r1 r2 : goodb (ZRange.sub r1 r2) = true.
    Proof. apply goodb_four_corners. Qed.
    Lemma goodb_mul r1 r2 : goodb (ZRange.mul r1 r2) = true.
    Proof. apply goodb_four_corners. Qed.
    Lemma goodb_div r1 r2 : goodb (ZRange.div r1 r2) = true.
    Proof. apply goodb_four_corners_and_zero. Qed.
    Lemma goodb_shiftr r1 r2 : goodb (ZRange.shiftr r1 r2) = true.
    Proof. apply goodb_four_corners_and_zero. Qed.
    Lemma goodb_shiftl r1 r2 : goodb (ZRange.shiftl r1 r2) = true.
    Proof. apply goodb_four_corners_and_zero. Qed.
    Lemma goodb_land r1 r2 : goodb (ZRange.land r1 r2) = true.
    Proof. apply goodb_four_corners_and_zero. Qed.
    Lemma goodb_lor r1 r2 : goodb (ZRange.lor r1 r2) = true.
    Proof. apply goodb_four_corners_and_zero. Qed.
    Lemma goodb_cc_m s r : goodb (ZRange.cc_m s r) = true.
    Proof. apply goodb_two_corners. Qed.
  End goodb.

  Section normalize.
    Lemma normalize_two_corners f r : normalize (two_corners f r) = two_corners f r.
    Proof. now rewrite (proj1 normalize_id_iff_goodb) by apply goodb_two_corners. Qed.

    Lemma normalize_four_corners f r1 r2 : normalize (four_corners f r1 r2) = four_corners f r1 r2.
    Proof. now rewrite (proj1 normalize_id_iff_goodb) by apply goodb_four_corners. Qed.

    Lemma normalize_eight_corners f r1 r2 r3 : normalize (eight_corners f r1 r2 r3) = eight_corners f r1 r2 r3.
    Proof. now rewrite (proj1 normalize_id_iff_goodb) by apply goodb_eight_corners. Qed.

    Lemma normalize_two_corners_and_zero f r1 : normalize (two_corners_and_zero f r1) = two_corners_and_zero f r1.
    Proof. now rewrite (proj1 normalize_id_iff_goodb) by apply goodb_two_corners_and_zero. Qed.

    Lemma normalize_four_corners_and_zero f r1 r2 : normalize (four_corners_and_zero f r1 r2) = four_corners_and_zero f r1 r2.
    Proof. now rewrite (proj1 normalize_id_iff_goodb) by apply goodb_four_corners_and_zero. Qed.

    Lemma normalize_eight_corners_and_zero f r1 r2 r3 : normalize (eight_corners_and_zero f r1 r2 r3) = eight_corners_and_zero f r1 r2 r3.
    Proof. now rewrite (proj1 normalize_id_iff_goodb) by apply goodb_eight_corners_and_zero. Qed.

    Lemma normalize_log2 r : normalize (ZRange.log2 r) = ZRange.log2 r.
    Proof. apply normalize_two_corners. Qed.
    Lemma normalize_log2_up r : normalize (ZRange.log2_up r) = ZRange.log2_up r.
    Proof. apply normalize_two_corners. Qed.
    Lemma normalize_add r1 r2 : normalize (ZRange.add r1 r2) = ZRange.add r1 r2.
    Proof. apply normalize_four_corners. Qed.
    Lemma normalize_sub r1 r2 : normalize (ZRange.sub r1 r2) = ZRange.sub r1 r2.
    Proof. apply normalize_four_corners. Qed.
    Lemma normalize_mul r1 r2 : normalize (ZRange.mul r1 r2) = ZRange.mul r1 r2.
    Proof. apply normalize_four_corners. Qed.
    Lemma normalize_div r1 r2 : normalize (ZRange.div r1 r2) = ZRange.div r1 r2.
    Proof. apply normalize_four_corners_and_zero. Qed.
    Lemma normalize_shiftr r1 r2 : normalize (ZRange.shiftr r1 r2) = ZRange.shiftr r1 r2.
    Proof. apply normalize_four_corners_and_zero. Qed.
    Lemma normalize_shiftl r1 r2 : normalize (ZRange.shiftl r1 r2) = ZRange.shiftl r1 r2.
    Proof. apply normalize_four_corners_and_zero. Qed.
    Lemma normalize_land r1 r2 : normalize (ZRange.land r1 r2) = ZRange.land r1 r2.
    Proof. apply normalize_four_corners_and_zero. Qed.
    Lemma normalize_lor r1 r2 : normalize (ZRange.lor r1 r2) = ZRange.lor r1 r2.
    Proof. apply normalize_four_corners_and_zero. Qed.
    Lemma normalize_cc_m s r : normalize (ZRange.cc_m s r) = ZRange.cc_m s r.
    Proof. apply normalize_two_corners. Qed.
  End normalize.
End ZRange.
