Require Import Coq.Classes.Morphisms.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.N2Z.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.ZUtil.Pow2.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.NUtil.WithoutReferenceToZ.
Local Open Scope Z_scope.

Module Z.
  Lemma lor_range : forall x y n, 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n ->
                                  0 <= Z.lor x y < 2 ^ n.
  Proof.
    intros x y n H H0; assert (0 <= n) by auto with zarith lia.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => rewrite Z.lor_spec
           | |- _ => rewrite Z.testbit_eqb by auto with zarith lia
           | |- _ => rewrite !Z.div_small by (split; try lia; eapply Z.lt_le_trans;
                             [ intuition eassumption | apply Z.pow_le_mono_r; lia])
           | |- _ => split
           | |- _ => apply Z.testbit_false_bound
           | |- _ => solve [auto with zarith]
           | |- _ => solve [apply Z.lor_nonneg; intuition auto]
           end.
  Qed.
  Hint Resolve lor_range : zarith.

  Lemma lor_shiftl_bounds : forall x y n m,
      (0 <= n)%Z -> (0 <= m)%Z ->
      (0 <= x < 2 ^ m)%Z ->
      (0 <= y < 2 ^ n)%Z ->
      (0 <= Z.lor y (Z.shiftl x n) < 2 ^ (n + m))%Z.
  Proof.
    intros x y n m H H0 H1 H2.
    apply Z.lor_range.
    { split; try lia.
      apply Z.lt_le_trans with (m := (2 ^ n)%Z); try lia.
      apply Z.pow_le_mono_r; lia. }
    { rewrite Z.shiftl_mul_pow2 by lia.
      rewrite Z.pow_add_r by lia.
      split; Z.zero_bounds.
      rewrite Z.mul_comm.
      apply Z.mul_lt_mono_pos_l; lia. }
  Qed.

  Lemma land_upper_bound_l : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= a.
  Proof.
    intros a b H H0.
    destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
    cbv [Z.land].
    rewrite <-N2Z.inj_pos, <-N2Z.inj_le.
    auto using N.Pos_land_upper_bound_l.
  Qed.

  Lemma land_upper_bound_r : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= b.
  Proof.
    intros.
    rewrite Z.land_comm.
    auto using Z.land_upper_bound_l.
  Qed.

  Section ZInequalities.
    Lemma land_le' : forall x y, (0 <= x)%Z -> (Z.land x y <= x)%Z.
    Proof.
      intros x y H; apply Z.ldiff_le; [assumption|].
      rewrite Z.ldiff_land, Z.land_comm, Z.land_assoc.
      rewrite <- Z.land_0_l with (a := y); f_equal.
      rewrite Z.land_comm, Z.land_lnot_diag.
      reflexivity.
    Qed.

    Lemma lor_lower : forall x y, (0 <= x -> 0 <= y)%Z -> (x <= Z.lor x y)%Z.
    Proof.
      intros x y H.
      destruct (Z_lt_le_dec x 0).
      { Z.replace_all_neg_with_pos.
        replace (-x) with (Z.lnot (x - 1)) by (cbv [Z.pred Z.lnot]; lia).
        rewrite <- (Z.lnot_involutive y).
        rewrite <- Z.lnot_land.
        cbv [Z.lnot].
        rewrite <- !Z.sub_1_r.
        Z.peel_le.
        apply land_le'; lia. }
      { apply Z.ldiff_le; [apply Z.lor_nonneg; auto|].
        rewrite Z.ldiff_land.
        apply Z.bits_inj_iff'; intros k Hpos; apply Z.le_ge in Hpos.
        rewrite Z.testbit_0_l, Z.land_spec, Z.lnot_spec, Z.lor_spec;
          [|apply Z.ge_le; assumption].
        induction (Z.testbit x k), (Z.testbit y k); cbv; reflexivity. }
    Qed.

    Lemma land_le : forall x y, (0 <= y -> 0 <= x)%Z -> (Z.land x y <= x)%Z.
    Proof.
      intros x y H.
      destruct (Z_lt_le_dec y 0), (Z_lt_le_dec x 0); auto using land_le' with lia.
      Z.replace_all_neg_with_pos.
      replace (-x) with (Z.lnot (x - 1)) by (cbv [Z.pred Z.lnot]; lia).
      replace (-y) with (Z.lnot (y - 1)) by (cbv [Z.pred Z.lnot]; lia).
      rewrite <- Z.lnot_lor.
      cbv [Z.lnot].
      rewrite <- !Z.sub_1_r.
      Z.peel_le.
      apply lor_lower; lia.
    Qed.

    Lemma land_le_neg_l_lower :
      forall x y, (x < 0)%Z -> (0 <= y) -> (x <= Z.land x y)%Z.
    Proof.
      intros x y ? ?. destruct x, y; cbn [Z.land]; lia.
    Qed.

    Lemma land_le_neg_l_upper :
      forall x y, (x < 0)%Z -> (0 <= y) -> (Z.land x y <= y)%Z.
    Proof.
      intros; rewrite Z.land_comm. auto using land_le'.
    Qed.

    Lemma land_neg_l_range :
      forall x y, x < 0 -> 0 <= y -> x <= Z.land x y <= y.
    Proof.
      auto using land_le_neg_l_lower, land_le_neg_l_upper.
    Qed.
    Lemma land_neg_r_range :
      forall x y, 0 <= x -> y < 0 -> y <= Z.land x y <= x.
    Proof.
      intros; rewrite Z.land_comm. auto using land_neg_l_range.
    Qed.

    Lemma lor_neg_lower :
      forall x y, x < 0 -> y < 0 -> (Z.max x y <= Z.lor x y)%Z.
    Proof.
      intros x y ? ?. destruct x, y; cbn [Z.lor]; try lia.
      apply Z.opp_le_mono.
      repeat first [ rewrite N.pos_pred_spec
                   | rewrite N.succ_pos_spec
                   | rewrite Z.opp_max_distr
                   | rewrite Pos2Z.opp_neg
                   | rewrite <-!positive_N_Z
                   | rewrite N.succ_pos_spec ].
      rewrite !N2Z.inj_succ, !N2Z.inj_land,
      !N2Z.inj_pred, !N2Z.inj_pos by lia.
      match goal with
      | |- context [Z.land ?a ?b] =>
        let Hab := fresh in
        let Hba := fresh in
        pose proof (land_le a b ltac:(lia)) as Hab;
          pose proof (land_le b a ltac:(lia)) as Hba;
          rewrite Z.land_comm in Hba
      end.
      lia.
    Qed.

    Lemma land_neg_lower' :
      forall x y n, x < 0 -> y < 0 ->
                    - 2 ^ n <= x ->
                    - 2 ^ n <= y ->
                    - 2 ^ n <= Z.land x y.
    Proof.
      intros x y n. intros.
      destruct x, y; cbn [Z.land]; try lia; [ ].
      apply Z.opp_le_mono.
      repeat first [ rewrite N.pos_pred_spec
                   | rewrite N.succ_pos_spec
                   | rewrite Z.opp_max_distr
                   | rewrite Pos2Z.opp_neg
                   | rewrite <-!positive_N_Z
                   | rewrite N.succ_pos_spec
                   | rewrite Z.opp_involutive
                   | rewrite Z.opp_succ ].
      rewrite !N2Z.inj_succ, !N2Z.inj_lor,
      !N2Z.inj_pred, !N2Z.inj_pos by lia.
      match goal with
      | |- context [Z.lor ?a ?b] =>
        pose proof (lor_range a b n ltac:(lia) ltac:(lia))
      end.
      lia.
    Qed.

    Lemma land_neg_lower :
      forall x y,
        x < 0 -> y < 0 ->
        - 2 ^ (Z.max (Z.log2_up (-x)) (Z.log2_up (-y))) <= Z.land x y.
    Proof.
      intros x y. intros.
      pose proof (Z.log2_log2_up_spec (-x) ltac:(lia)).
      pose proof (Z.log2_log2_up_spec (-y) ltac:(lia)).
      pose proof (Z.pow_le_mono 2 (Z.log2_up (-x))
                                2 (Z.log2_up (-y)) ltac:(lia)).
      pose proof (Z.pow_le_mono 2 (Z.log2_up (-y))
                                2 (Z.log2_up (-x)) ltac:(lia)).
      apply land_neg_lower'; auto; [ | ].
      { apply Z.opp_le_mono.
        rewrite Z.opp_involutive.
        apply Z.max_case_strong; lia. }
      { apply Z.opp_le_mono.
        rewrite Z.opp_involutive.
        apply Z.max_case_strong; lia. }
    Qed.

    Lemma lor_le : forall x y z,
        (0 <= x)%Z
        -> (x <= y)%Z
        -> (y <= z)%Z
        -> (Z.lor x y <= (2 ^ Z.log2_up (z+1)) - 1)%Z.
    Proof.
      intros x y z H H0 H1; apply Z.ldiff_le.

      - apply Z.le_add_le_sub_r.
        replace 1%Z with (2 ^ 0)%Z by (cbv; reflexivity).
        rewrite Z.add_0_l.
        apply Z.pow_le_mono_r; [cbv; reflexivity|].
        apply Z.log2_up_nonneg.

      - destruct (Z_lt_dec 0 z).

        + assert (forall a, a - 1 = Z.pred a)%Z as HP by (intro; lia);
            rewrite HP, <- Z.ones_equiv; clear HP.
          apply Z.ldiff_ones_r_low; [apply Z.lor_nonneg; split; lia|].
          rewrite Z.log2_up_eqn, Z.log2_lor; try lia.
          apply Z.lt_succ_r.
          apply Z.max_case_strong; intros; apply Z.log2_le_mono; lia.

        + replace z with 0%Z by lia.
          replace y with 0%Z by lia.
          replace x with 0%Z by lia.
          cbv; reflexivity.
    Qed.

    Local Ltac solve_pow2 :=
      repeat match goal with
             | [|- _ /\ _] => split
             | [|- (0 < 2 ^ _)%Z] => apply Z.pow2_gt_0
             | [|- (0 <= 2 ^ _)%Z] => apply Z.pow2_ge_0
             | [|- (2 ^ _ <= 2 ^ _)%Z] => apply Z.pow_le_mono_r
             | [|- (_ <= _)%Z] => lia
             | [|- (_ < _)%Z] => lia
             end.

    Lemma pow2_mod_range : forall a n m,
        (0 <= n) ->
        (n <= m) ->
        (0 <= Z.pow2_mod a n < 2 ^ m).
    Proof.
      intros; unfold Z.pow2_mod.
      rewrite Z.land_ones; [|assumption].
      split; [apply Z.mod_pos_bound, Z.pow2_gt_0; assumption|].
      eapply Z.lt_le_trans; [apply Z.mod_pos_bound, Z.pow2_gt_0; assumption|].
      apply Z.pow_le_mono; [|assumption].
      split; simpl; lia.
    Qed.

    Lemma shiftr_range : forall a n m,
        (0 <= n)%Z ->
        (0 <= m)%Z ->
        (0 <= a < 2 ^ (n + m))%Z ->
        (0 <= Z.shiftr a n < 2 ^ m)%Z.
    Proof.
      intros a n m H0 H1 H2; destruct H2.
      split; [apply Z.shiftr_nonneg; assumption|].
      rewrite Z.shiftr_div_pow2; [|assumption].
      apply Z.div_lt_upper_bound; [apply Z.pow2_gt_0; assumption|].
      eapply Z.lt_le_trans; [eassumption|apply Z.eq_le_incl].
      apply Z.pow_add_r; lia.
    Qed.


    Lemma shiftr_le_mono: forall a b c d,
        (0 <= a)%Z
        -> (0 <= d)%Z
        -> (a <= c)%Z
        -> (d <= b)%Z
        -> (Z.shiftr a b <= Z.shiftr c d)%Z.
    Proof.
      intros.
      repeat rewrite Z.shiftr_div_pow2; [|lia|lia].
      etransitivity; [apply Z.div_le_compat_l | apply Z.div_le_mono]; solve_pow2.
    Qed.

    Lemma shiftl_le_mono: forall a b c d,
        (0 <= a)%Z
        -> (0 <= b)%Z
        -> (a <= c)%Z
        -> (b <= d)%Z
        -> (Z.shiftl a b <= Z.shiftl c d)%Z.
    Proof.
      intros.
      repeat rewrite Z.shiftl_mul_pow2; [|lia|lia].
      etransitivity; [apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonneg_r]; solve_pow2.
    Qed.
  End ZInequalities.

  Lemma lor_bounds x y : 0 <= x -> 0 <= y
                         -> Z.max x y <= Z.lor x y <= 2^Z.log2_up (Z.max x y + 1) - 1.
  Proof.
    apply Z.max_case_strong; intros; split;
      try solve [ eauto using lor_lower, Z.le_trans, lor_le with lia
                | rewrite Z.lor_comm; eauto using lor_lower, Z.le_trans, lor_le with lia ].
  Qed.
  Lemma lor_bounds_lower x y : 0 <= x -> 0 <= y
                               -> Z.max x y <= Z.lor x y.
  Proof. intros; apply lor_bounds; assumption. Qed.
  Lemma lor_bounds_upper x y : Z.lor x y <= 2^Z.log2_up (Z.max x y + 1) - 1.
  Proof.
    pose proof (proj2 (Z.lor_neg x y)).
    destruct (Z_lt_le_dec x 0), (Z_lt_le_dec y 0);
      try solve [ intros; apply lor_bounds; assumption ];
      transitivity (2^0-1);
      try apply Z.sub_le_mono_r, Z.pow_le_mono_r, Z.log2_up_nonneg;
      simpl; lia.
  Qed.
  Lemma lor_bounds_gen_lower x y l : 0 <= x -> 0 <= y -> l <= Z.max x y
                                     -> l <= Z.lor x y.
  Proof.
    intros; etransitivity;
      solve [ apply lor_bounds; auto
            | eauto ].
  Qed.
  Lemma lor_bounds_gen_upper x y u : x <= u -> y <= u
                                     -> Z.lor x y <= 2^Z.log2_up (u + 1) - 1.
  Proof.
    intros; etransitivity; [ apply lor_bounds_upper | ].
    apply Z.sub_le_mono_r, Z.pow_le_mono_r, Z.log2_up_le_mono, Z.max_case_strong;
      lia.
  Qed.
  Lemma lor_bounds_gen x y l u : 0 <= x -> 0 <= y -> l <= Z.max x y -> x <= u -> y <= u
                                 -> l <= Z.lor x y <= 2^Z.log2_up (u + 1) - 1.
  Proof. auto using lor_bounds_gen_lower, lor_bounds_gen_upper. Qed.

  Lemma shiftl_le_Proper2 y
    : Proper (Z.le ==> Z.le) (fun x => Z.shiftl x y).
  Proof.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 y) as Hx.
    intros x x' H.
    pose proof (Zle_cases 0 x) as Hy.
    pose proof (Zle_cases 0 x') as Hy'.
    destruct (0 <=? y), (0 <=? x), (0 <=? x');
      autorewrite with Zshift_to_pow;
      Z.replace_all_neg_with_pos;
      autorewrite with pull_Zopp;
      rewrite ?Z.div_opp_l_complete;
      repeat destruct (Z_zerop _);
      autorewrite with zsimplify_const pull_Zopp;
      auto with zarith;
      repeat match goal with
             | [ |- context[-?x - ?y] ]
               => replace (-x - y) with (-(x + y)) by lia
             | _ => rewrite <- Z.opp_le_mono
             | _ => rewrite <- Z.add_le_mono_r
             | _ => solve [ auto with zarith ]
             | [ |- ?x <= ?y + 1 ]
               => cut (x <= y); [ lia | solve [ auto with zarith ] ]
             | [ |- -_ <= _ ]
               => solve [ transitivity (-0); auto with zarith ]
             end.
    { repeat match goal with H : context[_ mod _] |- _ => revert H end;
        Z.div_mod_to_quot_rem_in_goal; nia. }
  Qed.

  Lemma shiftl_le_Proper1 x
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
    : Proper (R (0 <=? x) ==> Z.le) (Z.shiftl x).
  Proof.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 x) as Hx.
    intros y y' H.
    pose proof (Zle_cases 0 y) as Hy.
    pose proof (Zle_cases 0 y') as Hy'.
    destruct (0 <=? x), (0 <=? y), (0 <=? y'); subst R; cbv beta iota in *;
      autorewrite with Zshift_to_pow;
      Z.replace_all_neg_with_pos;
      autorewrite with pull_Zopp;
      rewrite ?Z.div_opp_l_complete;
      repeat destruct (Z_zerop _);
      autorewrite with zsimplify_const pull_Zopp;
      auto with zarith;
      repeat match goal with
             | [ |- context[-?x - ?y] ]
               => replace (-x - y) with (-(x + y)) by lia
             | _ => rewrite <- Z.opp_le_mono
             | _ => rewrite <- Z.add_le_mono_r
             | _ => solve [ auto with zarith ]
             | [ |- ?x <= ?y + 1 ]
               => cut (x <= y); [ lia | solve [ auto with zarith ] ]
             | [ |- context[2^?x] ]
               => lazymatch goal with
                  | [ H : 1 < 2^x |- _ ] => fail
                  | [ H : 0 < 2^x |- _ ] => fail
                  | [ H : 0 <= 2^x |- _ ] => fail
                  | _ => first [ assert (1 < 2^x) by auto with zarith
                               | assert (0 < 2^x) by auto with zarith
                               | assert (0 <= 2^x) by auto with zarith ]
                  end
             | [ H : ?x <= ?y |- _ ]
               => is_var x; is_var y;
                    lazymatch goal with
                    | [ H : 2^x <= 2^y |- _ ] => fail
                    | [ H : 2^x < 2^y |- _ ] => fail
                    | _ => assert (2^x <= 2^y) by auto with zarith
                    end
             | [ H : ?x <= ?y, H' : ?f ?x = ?k, H'' : ?f ?y <> ?k |- _ ]
               => let Hn := fresh in
                  assert (Hn : x <> y) by congruence;
                    assert (x < y) by lia; clear H Hn
             | [ H : ?x <= ?y, H' : ?f ?x <> ?k, H'' : ?f ?y = ?k |- _ ]
               => let Hn := fresh in
                  assert (Hn : x <> y) by congruence;
                    assert (x < y) by lia; clear H Hn
             | _ => solve [ repeat match goal with H : context[_ mod _] |- _ => revert H end;
                            Z.div_mod_to_quot_rem_in_goal; subst;
                            lazymatch goal with
                            | [ |- _ <= (?a * ?q + ?r) * ?q' ]
                              => transitivity (q * (a * q') + r * q');
                                 [ assert (0 < a * q') by nia; nia
                                 | nia ]
                            end ]
             end.
    { replace y' with (y + (y' - y)) by lia.
      rewrite Z.pow_add_r, <- Zdiv_Zdiv by auto with zarith.
      assert (y < y') by (assert (y <> y') by congruence; lia).
      assert (1 < 2^(y'-y)) by auto with zarith.
      assert (0 < x / 2^y)
        by (repeat match goal with H : context[_ mod _] |- _ => revert H end;
            Z.div_mod_to_quot_rem_in_goal; nia).
      assert (2^y <= x)
        by (repeat match goal with H : context[_ / _] |- _ => revert H end;
            Z.div_mod_to_quot_rem_in_goal; nia).
      match goal with
      | [ |- ?x + 1 <= ?y ] => cut (x < y); [ lia | ]
      end.
      auto with zarith. }
  Qed.

  Lemma shiftr_le_Proper2 y
    : Proper (Z.le ==> Z.le) (fun x => Z.shiftr x y).
  Proof. apply shiftl_le_Proper2. Qed.

  Lemma shiftr_le_Proper1 x
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
    : Proper (R (x <? 0) ==> Z.le) (Z.shiftr x).
  Proof.
    subst R; intros y y' H'; unfold Z.shiftr; apply shiftl_le_Proper1.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 x).
    pose proof (Zlt_cases x 0).
    destruct (0 <=? x), (x <? 0); try lia.
  Qed.
End Z.
