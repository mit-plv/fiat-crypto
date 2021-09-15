Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Lnot.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Hints.Ztestbit.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.Log2.
Require Import Crypto.Util.ZUtil.Pow.
Require Import Crypto.Util.Bool.LeCompat.
Local Open Scope Z_scope.

Module Z.
  Lemma ones_spec : forall n m, 0 <= n -> 0 <= m -> Z.testbit (Z.ones n) m = if Z_lt_dec m n then true else false.
  Proof using Type.
    intros.
    break_match.
    + apply Z.ones_spec_low. lia.
    + apply Z.ones_spec_high. lia.
  Qed.
  Hint Rewrite ones_spec using zutil_arith : Ztestbit.

  Lemma ones_spec' n m (Hn : 0 <= n) (Hm : 0 <= m) :
    Z.testbit (Z.ones n) m = if (m <? n) then true else false.
  Proof using Type. rewrite ones_spec by assumption.
         destruct (Z_lt_dec m n) as [lt|lt];
           [apply Z.ltb_lt in lt|apply Z.ltb_nlt in lt];
           rewrite lt; reflexivity. Qed.

  Lemma ones_spec_full : forall n m, Z.testbit (Z.ones n) m
                                     = if Z_lt_dec m 0
                                       then false
                                       else if Z_lt_dec n 0
                                            then true
                                            else if Z_lt_dec m n then true else false.
  Proof using Type.
    intros n m.
    repeat (break_match || autorewrite with Ztestbit); try reflexivity; try lia.
    unfold Z.ones.
    rewrite <- Z.shiftr_opp_r, Z.shiftr_eq_0 by (simpl; lia); simpl.
    destruct m; simpl in *; try reflexivity.
    exfalso; auto using Zlt_neg_0.
  Qed.
  Hint Rewrite ones_spec_full : Ztestbit_full.

  Lemma testbit_pow2_mod : forall a n i, 0 <= n ->
  Z.testbit (Z.pow2_mod a n) i = if Z_lt_dec i n then Z.testbit a i else false.
  Proof using Type.
    cbv [Z.pow2_mod]; intros a n i H; destruct (Z_le_dec 0 i);
      repeat match goal with
          | |- _ => rewrite Z.testbit_neg_r by lia
          | |- _ => break_innermost_match_step
          | |- _ => lia
          | |- _ => reflexivity
          | |- _ => progress autorewrite with Ztestbit
          end.
  Qed.
  Hint Rewrite testbit_pow2_mod using zutil_arith : Ztestbit.

  Lemma testbit_pow2_mod_full : forall a n i,
      Z.testbit (Z.pow2_mod a n) i = if Z_lt_dec n 0
                                     then if Z_lt_dec i 0 then false else Z.testbit a i
                                     else if Z_lt_dec i n then Z.testbit a i else false.
  Proof using Type.
    intros a n i; destruct (Z_lt_dec n 0); [ | apply testbit_pow2_mod; lia ].
    unfold Z.pow2_mod.
    autorewrite with Ztestbit_full;
      repeat break_match;
      autorewrite with Ztestbit;
      reflexivity.
  Qed.
  Hint Rewrite testbit_pow2_mod_full : Ztestbit_full.

  Lemma bits_above_pow2 a n : 0 <= a < 2^n -> Z.testbit a n = false.
  Proof using Type.
    intros.
    destruct (Z_zerop a); subst; autorewrite with Ztestbit; trivial.
    apply Z.bits_above_log2; auto with zarith concl_log2.
  Qed.
  Hint Rewrite bits_above_pow2 using zutil_arith : Ztestbit.

  Lemma testbit_low : forall n x i, (0 <= i < n) ->
    Z.testbit x i = Z.testbit (Z.land x (Z.ones n)) i.
  Proof using Type.
    intros.
    rewrite Z.land_ones by lia.
    symmetry.
    apply Z.mod_pow2_bits_low.
    lia.
  Qed.

  Lemma testbit_add_shiftl_low : forall i, (0 <= i) -> forall a b n, (i < n) ->
    Z.testbit (a + Z.shiftl b n) i = Z.testbit a i.
  Proof using Type.
    intros i H a b n H0.
    erewrite Z.testbit_low; eauto.
    rewrite Z.land_ones, Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 n); lia).
    auto using Z.mod_pow2_bits_low.
  Qed.
  Hint Rewrite testbit_add_shiftl_low using zutil_arith : Ztestbit.

  Lemma testbit_sub_pow2 n i x (i_range:0 <= i < n) (x_range:0 < x < 2 ^ n) :
    Z.testbit (2 ^ n - x) i = negb (Z.testbit (x - 1)  i).
  Proof using Type.
    rewrite <-Z.lnot_spec, Z.lnot_sub1 by lia.
    rewrite <-(Z.mod_pow2_bits_low (-x) _ _ (proj2 i_range)).
    f_equal.
    rewrite Z.mod_opp_l_nz; autorewrite with zsimplify; lia.
  Qed.

  Lemma testbit_false_bound : forall a x, 0 <= x ->
    (forall n, ~ (n < x) -> Z.testbit a n = false) ->
    a < 2 ^ x.
  Proof using Type.
    intros a x H H0.
    assert (H1 : a = Z.pow2_mod a x). {
     apply Z.bits_inj'; intros.
     rewrite Z.testbit_pow2_mod by lia; break_match; auto.
    }
    rewrite H1.
    cbv [Z.pow2_mod]; rewrite Z.land_ones by auto.
    try apply Z.mod_pos_bound; Z.zero_bounds.
  Qed.

  Lemma testbit_neg_eq_if x n :
    0 <= n ->
    - (2 ^ n) <= x  < 2 ^ n ->
    Z.b2z (if x <? 0 then true else Z.testbit x n) = - (x / 2 ^ n) mod 2.
  Proof using Type.
    intros. break_match; Z.ltb_to_lt.
    { autorewrite with zsimplify. reflexivity. }
    { autorewrite with zsimplify.
      rewrite Z.bits_above_pow2 by lia.
      reflexivity. }
  Qed.

  Lemma shiftl_spec_full a n m : Z.testbit (a << n) m = if (0 <=? m) then Z.testbit a (m - n) else false.
  Proof using Type.
    break_innermost_match; Z.ltb_to_lt; now autorewrite with Ztestbit.
  Qed.
  Hint Rewrite shiftl_spec_full : Ztestbit_full.

  Lemma shiftr_spec_full a n m : Z.testbit (a >> n) m = if (0 <=? m) then Z.testbit a (m + n) else false.
  Proof using Type.
    break_innermost_match; Z.ltb_to_lt; now autorewrite with Ztestbit.
  Qed.
  Hint Rewrite shiftr_spec_full : Ztestbit_full.

  Lemma mod_pow2_ones a m :
    a mod 2 ^ m = if (Z_lt_dec m 0) then ltac:(match eval hnf in (1 mod 0) with | 0 => exact 0 | _ => exact a end) else a &' Z.ones m.
  Proof using Type. destruct (Z_lt_dec m 0). rewrite Z.pow_neg_r, Zmod_0_r; lia.
         symmetry; apply Z.land_ones; lia. Qed.

  Lemma bits_1 m :
    Z.testbit 1 m = if Z.eq_dec m 0 then true else false.
  Proof using Type.
    destruct (Z.eq_dec m 0); subst. reflexivity.
    destruct (Z_lt_dec m 0). rewrite Z.testbit_neg_r by lia. reflexivity.
    rewrite Z.bits_above_log2; simpl; try reflexivity; lia. Qed.

  Lemma bits_opp_full a i :
    Z.testbit (- a) i = if (Z_lt_dec i 0) then false else negb (Z.testbit (Z.pred a) i).
  Proof using Type.
    destruct (Z_lt_dec i 0). rewrite Z.testbit_neg_r by lia. reflexivity.
    apply Z.bits_opp; lia. Qed.

  Lemma pow2_bits_full m i :
    Z.testbit (2 ^ m) i =
    if (Z_lt_dec m 0) then false else if (Z.eq_dec i m) then true else false.
  Proof using Type.
    destruct (Z_lt_dec m 0); [now rewrite Z.pow_neg_r, Z.bits_0|].
    destruct (Z.eq_dec i m); subst.
    - apply Z.pow2_bits_true; lia.
    - apply Z.pow2_bits_false; lia. Qed.


  Definition bit_compare (b1 b2 : bool) : comparison
    := match b1, b2 with
       | true, true => Eq
       | true, false => Lt
       | false, false => Eq
       | false, true => Gt
       end.

  Lemma bit_compare_refl (b  : bool) : bit_compare b b = Eq.
  Proof using Type. now destruct b. Qed.
  Hint Rewrite bit_compare_refl : Ztestbit.

  Lemma bit_compare_eq_iff (b1 b2 : bool)
    : bit_compare b1 b2 = Eq <-> b1 = b2.
  Proof using Type. now destruct b1, b2. Qed.

  Lemma bit_compare_gt_iff (b1 b2 : bool)
    : bit_compare b1 b2 = Gt <-> (b1 = false /\ b2 = true).
  Proof using Type. now destruct b1, b2. Qed.

  Lemma bit_compare_lt_iff (b1 b2 : bool)
    : bit_compare b1 b2 = Lt <-> (b1 = true /\ b2 = false).
  Proof using Type. now destruct b1, b2. Qed.

  Lemma bits_const_iff z b
    : (forall n, 0 <= n -> Z.testbit z n = b)
      <-> z = if b then -1 else 0.
  Proof using Type.
    destruct b; [ rewrite <- (Z.bits_inj_iff z (-(1))) | rewrite <- (Z.bits_inj_iff z 0) ];
      cbv [Z.eqf];
      split; intros H n; specialize (H n); intros; destruct (Z_le_gt_dec 0 n);
        try specialize (H ltac:(assumption)); try lia;
        revert H;
        rewrite ?Z.bits_0, ?Z.bits_m1, ?Z.testbit_neg_r by lia; trivial.
  Qed.

  Lemma compare_by_bits_impl z1 z2 c
    : (forall n, 0 <= n -> bit_compare (Z.testbit z1 n) (Z.testbit z2 n) = c)
      -> Z.compare z1 z2 = c.
  Proof using Type.
    destruct (Z.compare_spec z1 z2), c; subst.
    all: repeat first [ progress setoid_rewrite bit_compare_refl
                      | progress setoid_rewrite bit_compare_eq_iff
                      | progress setoid_rewrite bit_compare_gt_iff
                      | progress setoid_rewrite bit_compare_lt_iff
                      | reflexivity
                      | assumption
                      | congruence
                      | lia
                      | progress subst
                      | progress intros
                      | progress split_and
                      | match goal with
                        | [ H : forall n, 0 <= n -> ?T |- _ ] => assert T by (eapply H; reflexivity); clear H
                        | [ H : forall n, 0 <= n -> Z.testbit _ _ = Z.testbit _ _ |- _ ]
                          => apply Z.bits_inj' in H
                        | [ H : forall n, 0 <= n -> Z.testbit _ n = ?b |- _ ]
                          => apply bits_const_iff in H
                        end ].
  Qed.

  Lemma testbit_small_neg a b
        (Ha : - 2^b <= a < 0)
        (Hb : 0 < b) :
    Z.testbit a b = true.
  Proof using Type.
    destruct Ha; apply Z_le_lt_eq_dec in H; destruct H.
    - apply Z.bits_iff_neg with (n:=b) in H0; [assumption|].
      apply Log2.Z.log2_lt_pow2_alt; try lia.
    - subst; replace (- 2 ^ b) with ((-1) * 2 ^ b) by ring.
      rewrite Z.mul_pow2_bits, Z.sub_diag, Z.bit0_odd by lia; reflexivity. Qed.

  Lemma testbit_large a b
        (Ha : 2 ^ (b - 1) <= a < 2 ^ b)
        (Hb : 0 < b) :
    Z.testbit a (b - 1) = true.
  Proof using Type.
    destruct (Z.testbit a (b - 1)) eqn:E; try reflexivity.
    rewrite Z.testbit_false in * by lia.
    apply Z.div_exact in E; [|lia].
    rewrite Div.Z.div_between_1 in E; auto with zarith.
    rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia. Qed.

   Lemma testbit_b2z a m :
     Z.testbit a m = negb (Z.b2z (Z.testbit a m) =? 0).
   Proof using Type. destruct (Z.testbit a m); reflexivity. Qed.

   Lemma pos_le_bitwise a b (H : forall i, Bool.le (Pos.testbit a i) (Pos.testbit b i))
     : Pos.le a b.
   Proof using Type.
     revert dependent a; induction b as [b IHb|b IHb|], a as [a|a|]; intros; try lia;
       try solve [ change (a <= b)%positive;
                   apply IHb;
                   intro i; specialize (H (N.succ i)); destruct i; cbn in H; rewrite ?Pos.pred_N_succ in H; try assumption ].
     all: first [ cbv [Pos.le]; cbn; rewrite Pos.compare_cont_Lt_not_Gt
                | cbv [Pos.le]; cbn; rewrite Pos.compare_cont_Gt_not_Gt
                | idtac ].
     all: try solve [ apply IHb;
                      intro i; specialize (H (N.succ i)); destruct i; cbn in H; rewrite ?Pos.pred_N_succ in H; try assumption
                    | specialize (H 0%N); cbn in H; congruence ].
     all: specialize (fun i => H (Npos i)).
     all: lazymatch type of H with
          | forall i, Bool.le (Pos.testbit ?a _) (Pos.testbit ?b _)
            => change (forall i, Bool.le (Z.testbit (Zpos a) (Zpos i)) (Z.testbit (Zpos b) (Zpos i))) in H;
                 specialize (H (Z.to_pos (Z.log2 (Zpos a))))
          end.
     all: rewrite Z2Pos.id in H by (apply Z.log2_pos; lia).
     all: rewrite Z.bit_log2 in H by lia.
     all: rewrite Z.bits_above_log2 in H; try apply Z.log2_pos; try lia.
     all: cbn in H; try congruence.
   Qed.

   Lemma le_bitwise a b (Ha : 0 <= a) (Hb : 0 <= b)  (H : forall i, 0 <= i -> Bool.le (Z.testbit a i) (Z.testbit b i))
     : Z.le a b.
   Proof using Type.
     destruct a as [|a|a], b as [|b|b]; try lia.
     { specialize (H (Z.log2 (Zpos a)) (Z.log2_nonneg (Zpos a))).
       rewrite Z.testbit_0_l, Z.bit_log2 in H by lia.
       cbn in H; congruence. }
     { apply pos_le_bitwise.
       intro i; destruct i.
       { specialize (H 0 ltac:(lia)); cbn in H.
         destruct a, b; cbn in *; try reflexivity; try congruence. }
       { refine (H (Zpos _) _); lia. } }
   Qed.
End Z.
