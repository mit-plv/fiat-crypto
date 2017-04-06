Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Coq.funind.Recdef.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.BoundedArithmetic.Pow2Base.
Require Import Crypto.BoundedArithmetic.BaseSystemProofs.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.Bool.
Require Export Crypto.Util.FixCoqMistakes.
Local Open Scope Z_scope.

Create HintDb simpl_add_to_nth discriminated.
Create HintDb push_upper_bound discriminated.
Create HintDb pull_upper_bound discriminated.
Create HintDb push_base_from_limb_widths discriminated.
Create HintDb pull_base_from_limb_widths discriminated.

Hint Extern 1 => progress autorewrite with push_upper_bound in * : push_upper_bound.
Hint Extern 1 => progress autorewrite with pull_upper_bound in * : pull_upper_bound.
Hint Extern 1 => progress autorewrite with push_base_from_limb_widths in * : push_base_from_limb_widths.
Hint Extern 1 => progress autorewrite with pull_base_from_limb_widths in * : pull_base_from_limb_widths.

Section Pow2BaseProofs.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma base_from_limb_widths_length ls : length (base_from_limb_widths ls) = length ls.
  Proof using Type.
    clear limb_widths limb_widths_nonneg.
    induction ls; [ reflexivity | simpl in * ].
    autorewrite with distr_length; auto.
  Qed.
  Hint Rewrite base_from_limb_widths_length : distr_length.

  Lemma base_from_limb_widths_cons : forall l0 l,
    base_from_limb_widths (l0 :: l) = 1 :: map (Z.mul (two_p l0)) (base_from_limb_widths l).
  Proof using Type. reflexivity. Qed.
  Hint Rewrite base_from_limb_widths_cons : push_base_from_limb_widths.
  Hint Rewrite <- base_from_limb_widths_cons : pull_base_from_limb_widths.

  Lemma base_from_limb_widths_nil : base_from_limb_widths nil = nil.
  Proof using Type. reflexivity. Qed.
  Hint Rewrite base_from_limb_widths_nil : push_base_from_limb_widths.

  Lemma firstn_base_from_limb_widths : forall n, firstn n (base_from_limb_widths limb_widths) = base_from_limb_widths (firstn n limb_widths).
  Proof using Type.
    clear limb_widths_nonneg. (* don't use this in the inductive hypothesis *)
    induction limb_widths as [|l ls IHls]; intros [|n]; try reflexivity.
    autorewrite with push_base_from_limb_widths push_firstn; boring.
  Qed.
  Hint Rewrite <- @firstn_base_from_limb_widths : push_base_from_limb_widths.
  Hint Rewrite <- @firstn_base_from_limb_widths : pull_firstn.
  Hint Rewrite @firstn_base_from_limb_widths : pull_base_from_limb_widths.
  Hint Rewrite @firstn_base_from_limb_widths : push_firstn.

  Lemma sum_firstn_limb_widths_nonneg : forall n, 0 <= sum_firstn limb_widths n.
  Proof using Type*.
    unfold sum_firstn; intros.
    apply fold_right_invariant; try omega.
    eauto using Z.add_nonneg_nonneg, limb_widths_nonneg, In_firstn.
  Qed. Hint Resolve sum_firstn_limb_widths_nonneg.

  Lemma two_sum_firstn_limb_widths_pos n : 0 < 2^sum_firstn limb_widths n.
  Proof using Type*. auto with zarith. Qed.

  Lemma two_sum_firstn_limb_widths_nonzero n : 2^sum_firstn limb_widths n <> 0.
  Proof using Type*. pose proof (two_sum_firstn_limb_widths_pos n); omega. Qed.

  Lemma base_from_limb_widths_step : forall i b w, (S i < length limb_widths)%nat ->
    nth_error base i = Some b ->
    nth_error limb_widths i = Some w ->
    nth_error base (S i) = Some (two_p w * b).
  Proof using Type.
    clear limb_widths_nonneg. (* don't use this in the inductive hypothesis *)
    induction limb_widths; intros ? ? ? ? nth_err_w nth_err_b;
      unfold base_from_limb_widths in *; fold base_from_limb_widths in *;
      [rewrite (@nil_length0 Z) in *; omega | ].
    simpl in *.
    case_eq i; intros; subst.
    + subst; apply nth_error_first in nth_err_w.
      apply nth_error_first in nth_err_b; subst.
      apply map_nth_error.
      case_eq l; intros; subst; [simpl in *; omega | ].
      unfold base_from_limb_widths; fold base_from_limb_widths.
      reflexivity.
    + simpl in nth_err_w.
      apply nth_error_map in nth_err_w.
      destruct nth_err_w as [x [A B] ].
      subst.
      replace (two_p w * (two_p a * x)) with (two_p a * (two_p w * x)) by ring.
      apply map_nth_error.
      apply IHl; auto. omega.
  Qed.


  Lemma nth_error_base : forall i, (i < length limb_widths)%nat ->
    nth_error base i = Some (two_p (sum_firstn limb_widths i)).
  Proof using Type*.
    induction i; intros.
    + unfold sum_firstn, base_from_limb_widths in *; case_eq limb_widths; try reflexivity.
      intro lw_nil; rewrite lw_nil, (@nil_length0 Z) in *; omega.
    + assert (i < length limb_widths)%nat as lt_i_length by omega.
      specialize (IHi lt_i_length).
      destruct (nth_error_length_exists_value _ _ lt_i_length) as [w nth_err_w].
      erewrite base_from_limb_widths_step; eauto.
      f_equal.
      simpl.
      destruct (NPeano.Nat.eq_dec i 0).
      - subst; unfold sum_firstn; simpl.
        apply nth_error_exists_first in nth_err_w.
        destruct nth_err_w as [l' lw_destruct]; subst.
        simpl; ring_simplify.
        f_equal; ring.
      - erewrite sum_firstn_succ; eauto.
        symmetry.
        apply two_p_is_exp; auto using sum_firstn_limb_widths_nonneg.
        apply limb_widths_nonneg.
        eapply nth_error_value_In; eauto.
  Qed.

  Lemma nth_default_base : forall d i, (i < length limb_widths)%nat ->
    nth_default d base i = 2 ^ (sum_firstn limb_widths i).
  Proof using Type*.
    intros ? ? i_lt_length.
    apply nth_error_value_eq_nth_default.
    rewrite nth_error_base, two_p_correct by assumption.
    reflexivity.
  Qed.

  Lemma base_succ : forall i, ((S i) < length limb_widths)%nat ->
    nth_default 0 base (S i) mod nth_default 0 base i = 0.
  Proof using Type*.
    intros.
    repeat rewrite nth_default_base by omega.
    apply Z.mod_same_pow.
    split; [apply sum_firstn_limb_widths_nonneg | ].
    destruct (NPeano.Nat.eq_dec i 0); subst.
      + case_eq limb_widths; intro; unfold sum_firstn; simpl; try omega; intros l' lw_eq.
        apply Z.add_nonneg_nonneg; try omega.
        apply limb_widths_nonneg.
        rewrite lw_eq.
        apply in_eq.
      + assert (i < length limb_widths)%nat as i_lt_length by omega.
        apply nth_error_length_exists_value in i_lt_length.
        destruct i_lt_length as [x nth_err_x].
        erewrite sum_firstn_succ; eauto.
        apply nth_error_value_In in nth_err_x.
        apply limb_widths_nonneg in nth_err_x.
        omega.
   Qed.

   Lemma nth_error_subst : forall i b, nth_error base i = Some b ->
     b = 2 ^ (sum_firstn limb_widths i).
   Proof using Type*.
     intros i b nth_err_b.
     pose proof (nth_error_value_length _ _ _ _ nth_err_b).
     rewrite base_from_limb_widths_length in *.
     rewrite nth_error_base in nth_err_b by assumption.
     rewrite two_p_correct in nth_err_b.
     congruence.
   Qed.

   Lemma base_positive : forall b : Z, In b base -> b > 0.
   Proof using Type*.
     intros b In_b_base.
     apply In_nth_error_value in In_b_base.
     destruct In_b_base as [i nth_err_b].
     apply nth_error_subst in nth_err_b.
     rewrite nth_err_b.
     apply Z.gt_lt_iff.
     apply Z.pow_pos_nonneg; omega || auto using sum_firstn_limb_widths_nonneg.
   Qed.

   Lemma b0_1 : forall x : Z, limb_widths <> nil -> nth_default x base 0 = 1.
   Proof using Type.
     case_eq limb_widths; intros; [congruence | reflexivity].
   Qed.

  Lemma base_from_limb_widths_app : forall l0 l
                                           (l0_nonneg : forall x, In x l0 -> 0 <= x)
                                           (l_nonneg : forall x, In x l -> 0 <= x),
      base_from_limb_widths (l0 ++ l)
      = base_from_limb_widths l0 ++ map (Z.mul (two_p (sum_firstn l0 (length l0)))) (base_from_limb_widths l).
  Proof using Type.
    induction l0 as [|?? IHl0].
    { simpl; intros; rewrite <- map_id at 1; apply map_ext; intros; omega. }
    { simpl; intros; rewrite !IHl0, !map_app, map_map, sum_firstn_succ_cons, two_p_is_exp by auto with znonzero.
      do 2 f_equal; apply map_ext; intros; lia. }
  Qed.

  Lemma skipn_base_from_limb_widths : forall n, skipn n (base_from_limb_widths limb_widths) = map (Z.mul (two_p (sum_firstn limb_widths n))) (base_from_limb_widths (skipn n limb_widths)).
  Proof using Type*.
    intro n; pose proof (base_from_limb_widths_app (firstn n limb_widths) (skipn n limb_widths)) as H.
    specialize_by eauto using In_firstn, In_skipn.
    autorewrite with simpl_firstn simpl_skipn in *.
    rewrite H, skipn_app, skipn_all by auto with arith distr_length; clear H.
    simpl; distr_length.
    apply Min.min_case_strong; intro;
      unfold sum_firstn; autorewrite with natsimplify simpl_skipn simpl_firstn;
        reflexivity.
  Qed.
  Hint Rewrite <- @skipn_base_from_limb_widths : push_base_from_limb_widths.
  Hint Rewrite <- @skipn_base_from_limb_widths : pull_skipn.
  Hint Rewrite @skipn_base_from_limb_widths : pull_base_from_limb_widths.
  Hint Rewrite @skipn_base_from_limb_widths : push_skipn.

  Lemma pow2_mod_bounded :forall lw us i, (forall w, In w lw -> 0 <= w) -> bounded lw us ->
                                          Z.pow2_mod (nth_default 0 us i) (nth_default 0 lw i) = nth_default 0 us i.
  Proof using Type.
    clear.
    repeat match goal with
           | |- _ => progress (cbv [bounded]; intros)
           | |- _ => break_if
           | |- _ => apply Z.bits_inj'
           | |- _ => rewrite Z.testbit_pow2_mod by (apply nth_default_preserves_properties; auto; omega)
           | |- _ => reflexivity
           end.
    specialize (H0 i).
    symmetry.
    rewrite <- (Z.mod_pow2_bits_high (nth_default 0 us i) (nth_default 0 lw i) n);
      [ rewrite Z.mod_small by omega; reflexivity | ].
    split; try omega.
    apply nth_default_preserves_properties; auto; omega.
  Qed.

  Lemma pow2_mod_bounded_iff :forall lw us, (forall w, In w lw -> 0 <= w) -> (bounded lw us <->
    (forall i, Z.pow2_mod (nth_default 0 us i) (nth_default 0 lw i) = nth_default 0 us i)).
  Proof using Type.
    clear.
    split; intros; auto using pow2_mod_bounded.
    cbv [bounded]; intros.
    assert (0 <= nth_default 0 lw i) by (apply nth_default_preserves_properties; auto; omega).
    split.
    + specialize (H0 i).
      rewrite Z.pow2_mod_spec in H0 by assumption.
      apply Z.mod_small_iff in H0; [ | apply Z.pow_nonzero; (assumption || omega)].
      destruct H0; try omega.
      pose proof (Z.pow_nonneg 2 (nth_default 0 lw i)).
      specialize_by omega; omega.
    + apply Z.testbit_false_bound; auto.
      intros.
      rewrite <-H0.
      rewrite Z.testbit_pow2_mod by assumption.
      break_if; reflexivity || omega.
  Qed.

  Lemma bounded_nil_iff : forall us, bounded nil us <-> (forall u, In u us -> u = 0).
  Proof using Type.
    clear.
    split; cbv [bounded]; intros.
    + edestruct (In_nth_error_value us u); try assumption.
      specialize (H x).
      replace u with (nth_default 0 us x) by (auto using nth_error_value_eq_nth_default).
      rewrite nth_default_nil, Z.pow_0_r in H.
      omega.
    + rewrite nth_default_nil, Z.pow_0_r.
      apply nth_default_preserves_properties; try omega.
      intros.
      apply H in H0.
      omega.
  Qed.

  Lemma bounded_iff : forall lw us, bounded lw us <-> forall i, 0 <= nth_default 0 us i < 2 ^ nth_default 0 lw i.
  Proof using Type.
    clear.
    cbv [bounded]; intros.
    reflexivity.
  Qed.

  Lemma digit_select : forall us i, bounded limb_widths us ->
                                    nth_default 0 us i = Z.pow2_mod (BaseSystem.decode base us >> sum_firstn limb_widths i) (nth_default 0 limb_widths i).
  Proof using Type*.
    intro; revert limb_widths limb_widths_nonneg; induction us; intros.
    + rewrite nth_default_nil, decode_nil, Z.shiftr_0_l, Z.pow2_mod_spec, Z.mod_0_l by
          (try (apply Z.pow_nonzero; try omega); apply nth_default_preserves_properties; auto; omega).
      reflexivity.
    + destruct i.
      - rewrite nth_default_cons, sum_firstn_0, Z.shiftr_0_r.
        destruct limb_widths as [|w lw].
        * cbv [base_from_limb_widths].
          rewrite <-pow2_mod_bounded with (lw := nil); rewrite bounded_nil_iff in *; auto using in_cons;
            try solve [intros; exfalso; eauto using in_nil].
          rewrite !nth_default_nil, decode_base_nil; auto.
          cbv. auto using in_eq.
        * rewrite nth_default_cons, base_from_limb_widths_cons, peel_decode.
          fold (BaseSystem.mul_each (two_p w)).
          rewrite <-mul_each_base, mul_each_rep.
          rewrite two_p_correct, (Z.mul_comm (2 ^ w)).
          rewrite <-Z.shiftl_mul_pow2 by auto using in_eq.
          rewrite bounded_iff in *.
          specialize (H 0%nat); rewrite !nth_default_cons in H.
          rewrite <-Z.lor_shiftl by (auto using in_eq; omega).
          apply Z.bits_inj'; intros.
          rewrite Z.testbit_pow2_mod by auto using in_eq.
          break_if. {
            autorewrite with Ztestbit; break_match;
              try rewrite Z.testbit_neg_r with (n := n - w) by omega;
              autorewrite with bool_congr;
              f_equal; ring.
          } {
            replace a with (a mod 2 ^ w) by (auto using Z.mod_small).
            apply Z.mod_pow2_bits_high. split; auto using in_eq; omega.
          }
      - rewrite nth_default_cons_S.
        destruct limb_widths as [|w lw].
        * cbv [base_from_limb_widths].
          rewrite <-pow2_mod_bounded with (lw := nil); rewrite bounded_nil_iff in *; auto using in_cons.
          rewrite sum_firstn_nil, !nth_default_nil, decode_base_nil, Z.shiftr_0_r.
          apply nth_default_preserves_properties; intros; auto using in_cons.
          f_equal; auto using in_cons.
        * rewrite sum_firstn_succ_cons, nth_default_cons_S, base_from_limb_widths_cons, peel_decode.
          fold (BaseSystem.mul_each (two_p w)).
          rewrite <-mul_each_base, mul_each_rep.
          rewrite two_p_correct, (Z.mul_comm (2 ^ w)).
          rewrite <-Z.shiftl_mul_pow2 by auto using in_eq.
          rewrite bounded_iff in *.
          rewrite Z.shiftr_add_shiftl_high by first
            [ pose proof (sum_firstn_nonnegative i lw); split; auto using in_eq; specialize_by auto using in_cons; omega
            | specialize (H 0%nat); rewrite !nth_default_cons in H; omega ].
          rewrite IHus with (limb_widths := lw) by
              (auto using in_cons; rewrite ?bounded_iff; intro j; specialize (H (S j));
               rewrite !nth_default_cons_S in H; assumption).
          repeat f_equal; try ring.
  Qed.

  Lemma nth_default_limb_widths_nonneg : forall i, 0 <= nth_default 0 limb_widths i.
  Proof using Type*.
    intros; apply nth_default_preserves_properties; auto; omega.
  Qed. Hint Resolve nth_default_limb_widths_nonneg.

  Lemma parity_decode : forall x,
    (0 < nth_default 0 limb_widths 0) ->
    length x = length limb_widths ->
    Z.odd (BaseSystem.decode base x) = Z.odd (nth_default 0 x 0).
  Proof using Type*.
    intros.
    destruct limb_widths, x; simpl in *; try discriminate; try reflexivity.
    rewrite peel_decode, nth_default_cons.
    fold (BaseSystem.mul_each (two_p z)).
    rewrite <-mul_each_base, mul_each_rep.
    rewrite Z.odd_add_mul_even; [ f_equal; ring | ].
    rewrite <-Z.even_spec, two_p_correct.
    apply Z.even_pow.
    rewrite @nth_default_cons in *; auto.
  Qed.

  Lemma decode_firstn_pow2_mod : forall us i,
    (i <= length us)%nat ->
    length us = length limb_widths ->
    bounded limb_widths us ->
    BaseSystem.decode' base (firstn i us) = Z.pow2_mod (BaseSystem.decode' base us) (sum_firstn limb_widths i).
  Proof using Type*.
    intros; induction i;
    repeat match goal with
           | |- _ => rewrite sum_firstn_0, decode_nil, Z.pow2_mod_0_r; reflexivity
           | |- _ => progress distr_length
           | |- _ => progress autorewrite with simpl_firstn
           | |- _ => rewrite firstn_succ with (d := 0)
           | |- _ => rewrite set_higher
           | |- _ => rewrite nth_default_base
           | |- _ => rewrite IHi
           | |- _ => rewrite <-Z.lor_shiftl by (rewrite ?Z.pow2_mod_spec; try apply Z.mod_pos_bound; zero_bounds)
           | |- appcontext[min ?x ?y] => (rewrite Nat.min_l by omega || rewrite Nat.min_r by omega)
           | |- appcontext[2 ^ ?a * _] => rewrite (Z.mul_comm (2 ^ a)); rewrite <-Z.shiftl_mul_pow2
           | |- _ => solve [auto]
           | |- _ => lia
           end.
    rewrite digit_select by assumption; apply Z.bits_inj'.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => rewrite Z.testbit_pow2_mod by (omega || trivial)
           | |- _ => break_if; try omega
           | H : ?a < ?b |- appcontext[Z.testbit _ (?a - ?b)] =>
             rewrite (Z.testbit_neg_r _ (a-b)) by omega
           | |- _ => reflexivity
           | |- _ => solve [f_equal; ring]
           | |- _ => rewrite sum_firstn_succ_default in *;
                       pose proof (nth_default_limb_widths_nonneg i); omega
           end.
  Qed.

  Lemma testbit_decode_firstn_high : forall us i n,
    (i <= length us)%nat ->
    length us = length limb_widths ->
    bounded limb_widths us ->
    sum_firstn limb_widths i <= n ->
    Z.testbit (BaseSystem.decode base (firstn i us)) n = false.
  Proof using Type*.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => rewrite decode_firstn_pow2_mod
           | |- _ => rewrite Z.testbit_pow2_mod
           | |- _ => break_if
           | |- _ => assumption
           | |- _ => solve [auto]
           | H : ?a <= ?b |- 0 <= ?b => assert (0 <= a) by (omega || auto); omega
           end.
  Qed.

  Lemma testbit_decode_high : forall us n,
    length us = length limb_widths ->
    bounded limb_widths us ->
    sum_firstn limb_widths (length us) <= n ->
    Z.testbit (BaseSystem.decode base us) n = false.
  Proof using Type*.
    intros.
    erewrite <-(firstn_all _ us) by reflexivity.
    auto using testbit_decode_firstn_high.
  Qed.

  (** TODO: Figure out how to automate and clean up this proof *)
  Lemma decode_nonneg : forall us,
    length us = length limb_widths ->
    bounded limb_widths us ->
    0 <= BaseSystem.decode base us.
  Proof using Type*.
    intros.
    unfold bounded, BaseSystem.decode, BaseSystem.decode' in *; simpl in *.
    pose 0 as zero.
    assert (0 <= zero) by reflexivity.
    replace base with (map (Z.mul (two_p zero)) base)
      by (etransitivity; [ | apply map_id ]; apply map_ext; auto with zarith).
    clearbody zero.
    revert dependent zero.
    generalize dependent limb_widths.
    induction us as [|u us IHus]; intros [|w limb_widths'] ?? Hbounded ??; simpl in *;
      try (reflexivity || congruence).
    pose proof (Hbounded 0%nat) as Hbounded0.
    pose proof (fun n => Hbounded (S n)) as HboundedS.
    unfold nth_default, nth_error in Hbounded0.
    unfold nth_default in HboundedS.
    rewrite map_map.
    unfold BaseSystem.accumulate at 1; simpl.
    assert (0 < two_p zero) by (rewrite two_p_equiv; auto with zarith).
    replace (map (fun x => two_p zero * (two_p w * x)) (base_from_limb_widths limb_widths')) with (map (Z.mul (two_p (zero + w))) (base_from_limb_widths limb_widths'))
      by (apply map_ext; rewrite two_p_is_exp by auto with zarith omega; auto with zarith).
    change 0 with (0 + 0) at 1.
    apply Z.add_le_mono; simpl in *; auto with zarith.
  Qed.

  Lemma decode_upper_bound : forall us,
    length us = length limb_widths ->
    bounded limb_widths us ->
    0 <= BaseSystem.decode base us < upper_bound limb_widths.
  Proof using Type*.
    cbv [upper_bound]; intros.
    split.
    { apply decode_nonneg; auto. }
    { apply Z.testbit_false_bound; auto; intros.
      rewrite testbit_decode_high; auto;
        replace (length us) with (length limb_widths); try omega. }
  Qed.

  Lemma decode_firstn_succ : forall us i,
      (S i <= length us)%nat ->
      bounded limb_widths us ->
      length us = length limb_widths ->
      BaseSystem.decode base (firstn (S i) us) =
      Z.lor (BaseSystem.decode base (firstn i us)) (nth_default 0 us i << sum_firstn limb_widths i).
  Proof using Type*.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => progress change BaseSystem.decode with BaseSystem.decode'
           | |- _ => rewrite sum_firstn_succ_default in *
           | |- _ => apply Z.bits_inj'
           | |- _ => break_if
           | |- appcontext [Z.testbit _ (?a - sum_firstn ?l ?i)] =>
                  destruct (Z_le_dec (sum_firstn l i) a);
                  [ rewrite (testbit_decode_firstn_high _ i a)
                  | rewrite (Z.testbit_neg_r _ (a - sum_firstn l i))]
           | |- appcontext [Z.testbit (BaseSystem.decode' _ (firstn ?i _)) _] =>
                  rewrite (decode_firstn_pow2_mod _ i)
           | |- _ => rewrite digit_select by auto
           | |- _ => rewrite Z.testbit_pow2_mod
           | |- _ => assumption
           | |- _ => reflexivity
           | |- _ => omega
           | |- _ => f_equal; ring
           | |- _ => solve [auto]
           | |- _ => solve [zero_bounds]
           | H : appcontext [nth_default 0 limb_widths ?i] |- _ =>
             pose proof (nth_default_limb_widths_nonneg i); omega
           | |- appcontext [nth_default 0 limb_widths ?i] =>
             pose proof (nth_default_limb_widths_nonneg i); omega
           end.
  Qed.

  Lemma testbit_decode_digit_select : forall us n i,
    bounded limb_widths us ->
    sum_firstn limb_widths i <= n < sum_firstn limb_widths (S i) ->
    Z.testbit (BaseSystem.decode base us) n = Z.testbit (nth_default 0 us i) (n - sum_firstn limb_widths i).
  Proof using Type*.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => erewrite digit_select by eauto
           | |- _ => progress rewrite sum_firstn_succ_default in *
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => break_if
           | |- _ => omega
           | |- _ => solve [f_equal;ring]
           end.
  Qed.

  Lemma testbit_bounded_high : forall i n us, bounded limb_widths us ->
                                            nth_default 0 limb_widths i <= n ->
                                            Z.testbit (nth_default 0 us i) n = false.
  Proof using Type*.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => break_if
           | |- _ => omega
           | |- _ => reflexivity
           | |- _ => assumption
           | |- _ => apply nth_default_limb_widths_nonneg; auto
           | H : nth_default 0 limb_widths ?i <= ?n |- 0 <= ?n => etransitivity; [ | eapply H]
           | |- _ => erewrite <-pow2_mod_bounded by eauto; rewrite Z.testbit_pow2_mod
           end.
  Qed.

  Lemma decode_shift_app : forall us0 us1, (length (us0 ++ us1) <= length limb_widths)%nat ->
    BaseSystem.decode base (us0 ++ us1) = (BaseSystem.decode (base_from_limb_widths (firstn (length us0) limb_widths)) us0) + ((BaseSystem.decode (base_from_limb_widths (skipn (length us0) limb_widths)) us1) << sum_firstn limb_widths (length us0)).
  Proof using Type*.
    unfold BaseSystem.decode; intros us0 us1 ?.
    assert (0 <= sum_firstn limb_widths (length us0)) by auto using sum_firstn_nonnegative.
    rewrite decode'_splice; autorewrite with push_firstn.
    apply Z.add_cancel_l.
    autorewrite with pull_base_from_limb_widths Zshift_to_pow zsimplify.
    rewrite decode'_map_mul, two_p_correct; nia.
  Qed.

  Lemma decode_shift : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << (nth_default 0 limb_widths 0)).
  Proof using Type*.
    intros; etransitivity; [ apply (decode_shift_app (u0::nil)); assumption | ].
    transitivity (u0 * 1 + 0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << (nth_default 0 limb_widths 0 + 0))); [ | autorewrite with zsimplify; reflexivity ].
    destruct limb_widths; distr_length; reflexivity.
  Qed.

  Lemma upper_bound_nil : upper_bound nil = 1.
  Proof using Type. reflexivity. Qed.

  Lemma upper_bound_cons x xs : 0 <= x -> 0 <= sum_firstn xs (length xs) -> upper_bound (x::xs) = 2^x * upper_bound xs.
  Proof using Type.
    intros Hx Hxs.
    unfold upper_bound; simpl.
    autorewrite with simpl_sum_firstn pull_Zpow.
    reflexivity.
  Qed.

  Lemma upper_bound_app xs ys : 0 <= sum_firstn xs (length xs) -> 0 <= sum_firstn ys (length ys) -> upper_bound (xs ++ ys) = upper_bound xs * upper_bound ys.
  Proof using Type.
    intros Hxs Hys.
    unfold upper_bound; simpl.
    autorewrite with distr_length simpl_sum_firstn pull_Zpow.
    reflexivity.
  Qed.

  Lemma bounded_nil_r : forall l, (forall x, In x l -> 0 <= x) -> bounded l nil.
  Proof using Type.
    cbv [bounded]; intros.
    rewrite nth_default_nil.
    apply nth_default_preserves_properties; intros; split; zero_bounds.
  Qed.

  Section make_base_vector.
    Local Notation k := (sum_firstn limb_widths (length limb_widths)).
    Context (limb_widths_match_modulus : forall i j,
                (i < length base)%nat ->
                (j < length base)%nat ->
                (i + j >= length base)%nat ->
                let w_sum := sum_firstn limb_widths in
                k + w_sum (i + j - length base)%nat <= w_sum i + w_sum j)
            (limb_widths_good : forall i j, (i + j < length limb_widths)%nat ->
                                            sum_firstn limb_widths (i + j) <=
                                            sum_firstn limb_widths i + sum_firstn limb_widths j).

    Lemma base_matches_modulus: forall i j,
      (i   <  length base)%nat ->
      (j   <  length base)%nat ->
      (i+j >= length base)%nat->
      let b := nth_default 0 base in
      let r := (b i * b j)  /   (2^k * b (i+j-length base)%nat) in
                b i * b j = r * (2^k * b (i+j-length base)%nat).
    Proof using limb_widths_match_modulus limb_widths_nonneg.
      intros.
      rewrite (Z.mul_comm r).
      subst r.
      rewrite base_from_limb_widths_length in *;
      assert (i + j - length limb_widths < length limb_widths)%nat by omega.
      rewrite Z.mul_div_eq by (apply Z.gt_lt_iff; subst b; rewrite ?nth_default_base; zero_bounds;
        assumption).
      rewrite (Zminus_0_l_reverse (b i * b j)) at 1.
      f_equal.
      subst b.
      repeat rewrite nth_default_base by auto.
      do 2 rewrite <- Z.pow_add_r by auto using sum_firstn_limb_widths_nonneg.
      symmetry.
      apply Z.mod_same_pow.
      split.
      + apply Z.add_nonneg_nonneg; auto using sum_firstn_limb_widths_nonneg.
      + auto using limb_widths_match_modulus.
    Qed.

    Lemma base_good : forall i j : nat,
                 (i + j < length base)%nat ->
                 let b := nth_default 0 base in
                 let r := b i * b j / b (i + j)%nat in
                 b i * b j = r * b (i + j)%nat.
    Proof using limb_widths_good limb_widths_nonneg.
      intros; subst b r.
      clear limb_widths_match_modulus.
      rewrite base_from_limb_widths_length in *.
      repeat rewrite nth_default_base by omega.
      rewrite (Z.mul_comm _ (2 ^ (sum_firstn limb_widths (i+j)))).
      rewrite Z.mul_div_eq by (apply Z.gt_lt_iff; zero_bounds;
        auto using sum_firstn_limb_widths_nonneg).
      rewrite <- Z.pow_add_r by auto using sum_firstn_limb_widths_nonneg.
      rewrite Z.mod_same_pow; try ring.
      split; [ auto using sum_firstn_limb_widths_nonneg | ].
      apply limb_widths_good.
      assumption.
    Qed.
  End make_base_vector.
End Pow2BaseProofs.
Hint Rewrite base_from_limb_widths_cons base_from_limb_widths_nil : push_base_from_limb_widths.
Hint Rewrite <- base_from_limb_widths_cons : pull_base_from_limb_widths.

Hint Rewrite <- @firstn_base_from_limb_widths : push_base_from_limb_widths.
Hint Rewrite <- @firstn_base_from_limb_widths : pull_firstn.
Hint Rewrite @firstn_base_from_limb_widths : pull_base_from_limb_widths.
Hint Rewrite @firstn_base_from_limb_widths : push_firstn.
Hint Rewrite <- @skipn_base_from_limb_widths : push_base_from_limb_widths.
Hint Rewrite <- @skipn_base_from_limb_widths : pull_skipn.
Hint Rewrite @skipn_base_from_limb_widths : pull_base_from_limb_widths.
Hint Rewrite @skipn_base_from_limb_widths : push_skipn.

Hint Rewrite @base_from_limb_widths_length : distr_length.
Hint Rewrite @upper_bound_nil @upper_bound_cons @upper_bound_app using solve [ eauto with znonzero ] : push_upper_bound.
Hint Rewrite <- @upper_bound_cons @upper_bound_app using solve [ eauto with znonzero ] : pull_upper_bound.

Section BitwiseDecodeEncode.
  Context {limb_widths} (limb_widths_nonnil : limb_widths <> nil)
          (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w)
          (limb_widths_good : forall i j, (i + j < length limb_widths)%nat ->
                                          sum_firstn limb_widths (i + j) <=
                                          sum_firstn limb_widths i + sum_firstn limb_widths j).
  Local Hint Resolve limb_widths_nonneg.
  Local Hint Resolve nth_default_limb_widths_nonneg.
  Local Hint Resolve sum_firstn_limb_widths_nonneg.
  Local Notation "w[ i ]" := (nth_default 0 limb_widths i).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation upper_bound := (upper_bound limb_widths).

  Lemma encode'_spec : forall x i, (i <= length limb_widths)%nat ->
    encode' limb_widths x i = BaseSystem.encode' base x upper_bound i.
  Proof using limb_widths_nonneg.
    induction i; intros.
    + rewrite encode'_zero. reflexivity.
    + rewrite encode'_succ, <-IHi by omega.
      simpl; do 2 f_equal.
      rewrite Z.land_ones, Z.shiftr_div_pow2 by auto.
      match goal with H : (S _ <= length limb_widths)%nat |- _ =>
        apply le_lt_or_eq in H; destruct H end.
      - repeat f_equal; rewrite nth_default_base by (omega || auto); reflexivity.
      - repeat f_equal; try solve [rewrite nth_default_base by (omega || auto); reflexivity].
        rewrite nth_default_out_of_bounds by (distr_length; omega).
        unfold Pow2Base.upper_bound.
        congruence.
  Qed.

  Lemma length_encode' : forall lw z i, length (encode' lw z i) = i.
  Proof using Type.
    induction i; intros; simpl encode'; distr_length.
  Qed.
  Hint Rewrite length_encode' : distr_length.

  Lemma bounded_encode' : forall z i, (0 <= z) ->
    bounded (firstn i limb_widths) (encode' limb_widths z i).
  Proof using limb_widths_nonneg.
    intros; induction i; simpl encode';
      repeat match goal with
             | |- _ => progress intros
             | |- _ => progress autorewrite with push_nth_default in *
             | |- _ => progress autorewrite with Ztestbit
             | |- _ => progress rewrite ?firstn_O, ?Nat.sub_diag in *
             | |- _ => rewrite Z.testbit_pow2_mod by auto
             | |- _ => rewrite Z.ones_spec by zero_bounds
             | |- _ => rewrite sum_firstn_succ_default
             | |- _ => rewrite nth_default_out_of_bounds by distr_length
             | |- _ => break_if; distr_length
             | |- _ => apply bounded_nil_r
             | |- appcontext[nth_default _ (_ :: nil) ?i] => case_eq i; intros; autorewrite with push_nth_default
             | |- Z.pow2_mod (?a >> ?b) _ = (?a >> ?b) => apply Z.bits_inj'
             | IH : forall i, _ = nth_default 0 (encode' _ _ _) i
                              |- appcontext[nth_default 0 limb_widths ?i] => specialize (IH i)
             | H : In _ (firstn _ _) |- _ => apply In_firstn in H
             | H1 : ~ (?a < ?b)%nat, H2 : (?a < S ?b)%nat |- _ =>
               progress replace a with b in * by omega
             | H : bounded _ _ |- bounded _ _ =>
               apply pow2_mod_bounded_iff; rewrite pow2_mod_bounded_iff in H
             | |- _ => solve [auto]
             | |- _ => contradiction
             | |- _ => reflexivity
             end.
  Qed.

  Lemma bounded_encodeZ : forall z, (0 <= z) ->
    bounded limb_widths (encodeZ limb_widths z).
  Proof using limb_widths_nonneg.
    cbv [encodeZ]; intros.
    pose proof (bounded_encode' z (length limb_widths)) as Hencode'.
    rewrite firstn_all in Hencode'; auto.
  Qed.

  Lemma base_upper_bound_compatible : @base_max_succ_divide base upper_bound.
  Proof using limb_widths_nonneg.
    unfold base_max_succ_divide; intros i lt_Si_length.
    rewrite base_from_limb_widths_length in lt_Si_length.
    rewrite Nat.lt_eq_cases in lt_Si_length; destruct lt_Si_length;
      rewrite !nth_default_base by (omega || auto).
    + erewrite sum_firstn_succ by (eapply nth_error_Some_nth_default with (x := 0); omega).
      rewrite Z.pow_add_r; eauto.
      apply Z.divide_factor_r.
    + rewrite nth_default_out_of_bounds by (distr_length; omega).
      unfold Pow2Base.upper_bound.
      replace (length limb_widths) with (S (pred (length limb_widths))) by omega.
      replace i with (pred (length limb_widths)) by omega.
      erewrite sum_firstn_succ by (eapply nth_error_Some_nth_default with (x := 0); omega).
      rewrite Z.pow_add_r; eauto.
      apply Z.divide_factor_r.
  Qed.
  Hint Resolve base_upper_bound_compatible.

  Lemma encodeZ_spec : forall x,
    BaseSystem.decode base (encodeZ limb_widths x) = x mod upper_bound.
  Proof.
    intros.
    assert (length base = length limb_widths) by distr_length.
    unfold encodeZ; rewrite encode'_spec by omega.
    erewrite BaseSystemProofs.encode'_spec; unfold Pow2Base.upper_bound;
      zero_bounds; intros; eauto using base_positive, b0_1. {
      rewrite nth_default_out_of_bounds by omega.
      reflexivity.
    } {
      econstructor; try apply base_good;
        eauto using base_positive, b0_1.
    }
  Qed.

  Lemma encodeZ_length : forall x, length (encodeZ limb_widths x) = length limb_widths.
  Proof using limb_widths_nonneg.
    cbv [encodeZ]; intros.
    rewrite encode'_spec by omega.
    apply encode'_length.
  Qed.

  Definition decode_bitwise'_invariant us i acc :=
    forall n, 0 <= n -> Z.testbit acc n = Z.testbit (BaseSystem.decode base us) (n + sum_firstn limb_widths i).

  Lemma decode_bitwise'_invariant_step : forall us,
    length us = length limb_widths ->
    bounded limb_widths us ->
    forall i acc, decode_bitwise'_invariant us (S i) acc ->
                  decode_bitwise'_invariant us i (Z.lor (nth_default 0 us i) (acc << nth_default 0 limb_widths i)).
  Proof using limb_widths_nonneg.
    repeat match goal with
      | |- _ => progress cbv [decode_bitwise'_invariant]; intros
      | |- _ => erewrite testbit_bounded_high by (omega || eauto)
      | |- _ => progress autorewrite with Ztestbit
      | |- _ => progress rewrite sum_firstn_succ_default
      | |- appcontext[Z.testbit _ ?n] => rewrite (Z.testbit_neg_r _ n) by omega
      | H : forall n, 0 <= n -> Z.testbit _ n = _ |- _ => rewrite H by omega
      | |- _ => solve [f_equal; ring]
      | |- appcontext[Z.testbit _ (?x + sum_firstn limb_widths ?i)] =>
        erewrite testbit_decode_digit_select with (i0 := i) by
          (eauto; rewrite sum_firstn_succ_default; omega)
      | |- appcontext[Z.testbit _ (?a - ?b)] => destruct (Z_lt_dec a b)
      | _ => progress break_if
      end.
  Qed.

  Lemma decode_bitwise'_invariant_holds : forall i us acc,
    length us = length limb_widths ->
    bounded limb_widths us ->
    decode_bitwise'_invariant us i acc ->
    decode_bitwise'_invariant us 0 (decode_bitwise' limb_widths us i acc).
  Proof using limb_widths_nonneg.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => solve [auto using decode_bitwise'_invariant_step]
           | |- appcontext[decode_bitwise' ?a ?b ?c ?d] =>
                functional induction (decode_bitwise' a b c d)
            end.
  Qed.

  Lemma decode_bitwise_spec : forall us, bounded limb_widths us ->
    length us = length limb_widths ->
    decode_bitwise limb_widths us = BaseSystem.decode base us.
  Proof using limb_widths_nonneg.
    repeat match goal with
           | |- _ => progress cbv [decode_bitwise decode_bitwise'_invariant] in *
           | |- _ => progress intros
           | |- _ => rewrite sum_firstn_0
           | |- _ => erewrite testbit_decode_high by (assumption || omega)
           | H0 : ?P ?x , H1 : ?P ?x -> _ |- _ => specialize (H1 H0)
           | H : _ -> forall n, 0 <= n -> Z.testbit _ n = _ |- _ => rewrite H
           | |- decode_bitwise' ?a ?b ?c ?d = _ =>
                  let H := fresh "H" in
                  pose proof (decode_bitwise'_invariant_holds c b d) as H;
                    apply Z.bits_inj'
           | |- _ => apply Z.testbit_0_l
           | |- _ => assumption
           | |- _ => solve [f_equal; ring]
           end.
  Qed.

End BitwiseDecodeEncode.

Section UniformBase.
  Context {width : Z} (limb_width_nonneg : 0 <= width).
  Context (limb_widths : list Z)
    (limb_widths_uniform : forall w, In w limb_widths -> w = width).
  Local Notation base := (base_from_limb_widths limb_widths).

   Lemma bounded_uniform : forall us, (length us <= length limb_widths)%nat ->
     (bounded limb_widths us <-> (forall u, In u us -> 0 <= u < 2 ^ width)).
   Proof using Type*.
     cbv [bounded]; split; intro A; intros.
     + let G := fresh "G" in
       match goal with H : In _ us |- _ =>
         eapply In_nth in H; destruct H as [? G]; destruct G as [? G];
         rewrite <-nth_default_eq in G; rewrite <-G end.
       specialize (A x).
       split; try eapply A.
       eapply Z.lt_le_trans; try apply A.
       apply nth_default_preserves_properties; [ | apply Z.pow_le_mono_r; omega ] .
       intros; apply Z.eq_le_incl.
       f_equal; auto.
     + apply nth_default_preserves_properties_length_dep;
         try solve [apply nth_default_preserves_properties; split; zero_bounds; rewrite limb_widths_uniform; auto || omega].
      intros; apply nth_default_preserves_properties_length_dep; try solve [intros; omega].
       let x := fresh "x" in intro x; intros;
         replace x with width; try symmetry; auto.
   Qed.

  Lemma uniform_limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w.
  Proof using Type*.
    intros.
    replace w with width by (symmetry; auto).
    assumption.
  Qed.

  Lemma nth_default_uniform_base_full : forall i,
      nth_default 0 limb_widths i = if lt_dec i (length limb_widths)
                                    then width else 0.
  Admitted.

  Lemma nth_default_uniform_base : forall i, (i < length limb_widths)%nat ->
      nth_default 0 limb_widths i = width.
  Proof using Type*.
    intros; rewrite nth_default_uniform_base_full.
    edestruct lt_dec; omega.
  Qed.

  Lemma sum_firstn_uniform_base : forall i, (i <= length limb_widths)%nat ->
                                            sum_firstn limb_widths i = Z.of_nat i * width.
  Proof using limb_widths_uniform.
    clear limb_width_nonneg. (* clear this before induction so we don't depend on this *)
    induction limb_widths as [|x xs IHxs]; (intros [|i] ?);
      simpl @length in *;
      autorewrite with simpl_sum_firstn push_Zof_nat zsimplify;
      try reflexivity;
      try omega.
    assert (x = width) by auto with datatypes; subst.
    rewrite IHxs by auto with datatypes omega; omega.
  Qed.

  Lemma sum_firstn_uniform_base_strong : forall i, (length limb_widths <= i)%nat ->
                                            sum_firstn limb_widths i = Z.of_nat (length limb_widths) * width.
  Proof using limb_widths_uniform.
    intros; rewrite sum_firstn_all, sum_firstn_uniform_base by omega; reflexivity.
  Qed.

  Lemma upper_bound_uniform : upper_bound limb_widths = 2^(Z.of_nat (length limb_widths) * width).
  Proof using limb_widths_uniform.
    unfold upper_bound; rewrite sum_firstn_uniform_base_strong by omega; reflexivity.
  Qed.

  (* TODO : move *)
  Lemma decode_truncate_base : forall us bs, BaseSystem.decode bs us = BaseSystem.decode (firstn (length us) bs) us.
  Proof using Type.
    clear.
    induction us; intros.
    + rewrite !decode_nil; reflexivity.
    + distr_length.
      destruct bs.
      - rewrite firstn_nil, !decode_base_nil; reflexivity.
      - rewrite firstn_cons, !peel_decode.
        f_equal.
        apply IHus.
  Qed.

  (* TODO : move *)
  Lemma tl_repeat : forall {A} xs n (x : A), (forall y, In y xs -> y = x) ->
                                             (n < length xs)%nat ->
                                             firstn n xs = firstn n (tl xs).
  Proof using Type.
    intros.
    erewrite (repeat_spec_eq xs) by first [ eassumption | reflexivity ].
    rewrite ListUtil.tl_repeat.
    autorewrite with push_firstn.
    apply f_equal; omega *.
  Qed.

  Lemma decode_tl_base : forall us, (length us < length limb_widths)%nat ->
      BaseSystem.decode base us = BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us.
  Proof using limb_widths_uniform.
    intros.
    match goal with |- BaseSystem.decode ?b1 _ = BaseSystem.decode ?b2 _ =>
      rewrite (decode_truncate_base _ b1), (decode_truncate_base _ b2) end.
    rewrite !firstn_base_from_limb_widths.
    do 2 f_equal.
    eauto using tl_repeat.
  Qed.

  Lemma decode_shift_uniform_tl : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << width).
  Proof using Type*.
    intros.
    rewrite <- (nth_default_uniform_base 0) by distr_length.
    rewrite decode_shift by auto using uniform_limb_widths_nonneg.
    reflexivity.
  Qed.

  Lemma decode_shift_uniform_app : forall us0 us1, (length (us0 ++ us1) <= length limb_widths)%nat ->
    BaseSystem.decode base (us0 ++ us1) = (BaseSystem.decode (base_from_limb_widths (firstn (length us0) limb_widths)) us0) + ((BaseSystem.decode (base_from_limb_widths (skipn (length us0) limb_widths)) us1) << (Z.of_nat (length us0) * width)).
  Proof using Type*.
    intros.
    rewrite <- sum_firstn_uniform_base by (distr_length; omega).
    rewrite decode_shift_app by auto using uniform_limb_widths_nonneg.
    reflexivity.
  Qed.

  Lemma decode_shift_uniform : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode base us) << width).
  Proof using Type*.
    intros.
    rewrite decode_tl_base with (us := us) by distr_length.
    apply decode_shift_uniform_tl; assumption.
  Qed.

End UniformBase.

Hint Rewrite @upper_bound_uniform using solve [ auto with datatypes ] : push_upper_bound.

Section SplitIndex.
  (* This section defines [split_index], which for a list of bounded digits
       splits a bit index in the decoded value into a digit index and a bit
       index within the digit. Examples:
       limb_widths [4;4] : split_index 6 = (1,2)
       limb_widths [26,25,26] : split_index 30 = (1,4)
       limb_widths [26,25,26] : split_index 51 = (2,0)
  *)
  Local Notation "u # i" := (nth_default 0 u i).

  Function split_index' i index lw :=
    match lw with
    | nil      => (index, i)
    | w :: lw' => if Z_lt_dec i w then (index, i)
                  else split_index' (i - w) (S index) lw'
    end.

  Lemma split_index'_ge_index : forall i index lw, (index <= fst (split_index' i index lw))%nat.
  Proof.
    intros; functional induction (split_index' i index lw);
      repeat match goal with
             | |- _ => omega
             | |- _ => progress (simpl fst; simpl snd)
             end.
  Qed.

  Lemma split_index'_done_case : forall i index lw, 0 <= i ->
                                                    (forall x, In x lw -> 0 <= x) ->
    if Z_lt_dec i (sum_firstn lw (length lw))
    then (fst (split_index' i index lw) - index < length lw)%nat
    else (fst (split_index' i index lw) - index = length lw)%nat.
  Proof.
    intros; functional induction (split_index' i index lw);
      repeat match goal with
             | |- _ => break_if
             | |- _ => rewrite sum_firstn_nil in *
             | |- _ => rewrite sum_firstn_succ_cons in *
             | |- _ => progress distr_length
             | |- _ => progress (simpl fst; simpl snd)
             | H : appcontext [split_index' ?a ?b ?c] |- _ =>
               unique pose proof (split_index'_ge_index a b c)
             | H : appcontext [sum_firstn ?l ?i] |- _ =>
               let H0 := fresh "H" in
               assert (forall x, In x l -> 0 <= x) by auto using in_cons;
               unique pose proof (sum_firstn_limb_widths_nonneg H0 i)
             | |- _ => progress specialize_by assumption
             | |- _ => progress specialize_by omega
             | |- _ => omega
             end.
  Qed.

  Lemma snd_split_index'_nonneg : forall index lw i, (0 <= i) ->
                                                     (0 <= snd (split_index' i index lw)).
  Proof.
    intros; functional induction (split_index' i index lw);
      repeat match goal with
             | |- _ => omega
             | H : ?P -> ?G |- ?G => apply H
             | |- _ => progress (simpl fst; simpl snd)
             end.
  Qed.

  Lemma snd_split_index'_small : forall i index lw, 0 <= i < sum_firstn lw (length lw) ->
      (snd (split_index' i index lw) < lw # (fst (split_index' i index lw) - index)).
  Proof.
    intros; functional induction (split_index' i index lw);
      try match goal with |- appcontext [split_index' ?a ?b ?c] =>
                    pose proof (split_index'_ge_index a b c) end;
      repeat match goal with
             | |- _ => progress autorewrite with push_nth_default distr_length in *
             | |- _ => rewrite Nat.sub_diag
             | |- _ => rewrite sum_firstn_nil in *
             | |- _ => rewrite sum_firstn_succ_cons in *
             | |- _ => progress (simpl fst; simpl snd)
             | H : _ -> ?x < _ |- ?x < _ => eapply Z.lt_le_trans; [ apply H; omega | ]
             | |- ?xs # (?a - S ?b) <= (_ :: ?xs) # (?a - ?b) =>
               replace (a - b)%nat with (S (a - S b))%nat
             | |- _ => omega
             end.
  Qed.

  Lemma split_index'_correct : forall i index lw,
    sum_firstn lw (fst (split_index' i index lw) - index) + (snd (split_index' i index lw)) = i.
  Proof.
    intros; functional induction (split_index' i index lw);
      repeat match goal with
             | |- _ => omega
             | |- _ => rewrite Nat.sub_diag
             | |- _ => progress rewrite ?sum_firstn_nil, ?sum_firstn_0, ?sum_firstn_succ_cons
             | |- _ => progress (simpl fst; simpl snd)
             | |- appcontext[(fst (split_index' ?i (S ?idx) ?lw) - ?idx)%nat] =>
               pose proof (split_index'_ge_index i (S idx) lw);
                 replace (fst (split_index' i (S idx) lw) - idx)%nat with
                   (S (fst (split_index' i (S idx) lw) - S idx))%nat
             end.
  Qed.

  Context limb_widths
          (limb_widths_pos : forall w, In w limb_widths -> 0 <= w).
  Local Hint Resolve limb_widths_pos.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation bitsIn lw := (sum_firstn lw (length lw)).

  Definition split_index i := split_index' i 0 limb_widths.
  Definition digit_index i := fst (split_index i).
  Definition bit_index i := snd (split_index i).

  Lemma testbit_decode : forall us n,
    0 <= n < bitsIn limb_widths ->
    length us = length limb_widths ->
    bounded limb_widths us ->
    Z.testbit (BaseSystem.decode base us) n = Z.testbit (us # digit_index n) (bit_index n).
  Proof using Type*.
    cbv [digit_index bit_index split_index]; intros.
    pose proof (split_index'_correct n 0 limb_widths).
    pose proof (snd_split_index'_nonneg 0 limb_widths n).
    specialize_by assumption.
    repeat match goal with
           | |- _ => progress autorewrite with Ztestbit natsimplify in *
           | |- _ => erewrite digit_select by eauto
           | |- _ => break_if
           | |- _ => rewrite Z.testbit_pow2_mod by auto using nth_default_limb_widths_nonneg
           | |- _ => omega
           | |- _ => f_equal; omega
           end.
    destruct (Z_lt_dec n (bitsIn limb_widths)). {
      pose proof (snd_split_index'_small n 0 limb_widths).
      specialize_by omega.
      rewrite Nat.sub_0_r in *.
      omega.
    } {
      apply testbit_decode_high; auto.
      replace (length us) with (length limb_widths) in *.
      omega.
    }
  Qed.

  Lemma testbit_decode_full : forall us n,
    length us = length limb_widths ->
    bounded limb_widths us ->
    Z.testbit (BaseSystem.decode base us) n =
    if Z_le_dec 0 n
    then (if Z_lt_dec n (bitsIn limb_widths)
          then Z.testbit (us # digit_index n) (bit_index n)
          else false)
    else false.
  Proof using Type*.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => break_if
           | |- _ => apply Z.testbit_neg_r; lia
           | |- _ => apply testbit_decode_high; auto;
                       try match goal with H : length _ = length limb_widths |- _ => rewrite H end; lia
           | |- _ => auto using testbit_decode
           end.
  Qed.

  Lemma bit_index_nonneg : forall i, 0 <= i -> 0 <= bit_index i.
  Proof using Type.
    apply snd_split_index'_nonneg.
  Qed.

  Lemma digit_index_lt_length : forall i, 0 <= i < bitsIn limb_widths ->
                                         (digit_index i < length limb_widths)%nat.
  Proof using Type*.
    cbv [bit_index digit_index split_index]; intros.
    pose proof (split_index'_done_case i 0 limb_widths).
    specialize_by lia. specialize_by eauto.
    break_if; lia.
  Qed.

  Lemma bit_index_not_done : forall i, 0 <= i < bitsIn limb_widths ->
                                         (bit_index i < limb_widths # digit_index i).
  Proof using Type.

    cbv [bit_index digit_index split_index]; intros.
    eapply Z.lt_le_trans; try apply (snd_split_index'_small i 0 limb_widths); try assumption.
    rewrite Nat.sub_0_r; lia.
  Qed.

  Lemma split_index_eqn : forall i, 0 <= i < bitsIn limb_widths ->
    sum_firstn limb_widths (digit_index i) + bit_index i = i.
  Proof using Type.
    cbv [bit_index digit_index split_index]; intros.
    etransitivity;[ | apply (split_index'_correct i 0 limb_widths) ].
    repeat f_equal; omega.
  Qed.

  Lemma rem_bits_in_digit_pos : forall i, 0 <= i < bitsIn limb_widths ->
                                          0 < (limb_widths # digit_index i) - bit_index i.
  Proof using Type.
    repeat match goal with
           | |- _ => progress intros
           | |- 0 < ?a - ?b => destruct (Z_lt_dec b a); [ lia | exfalso ]
           | H : ~ (bit_index ?i < limb_widths # digit_index ?i) |- _ =>
             pose proof (bit_index_not_done i); specialize_by omega; omega
           end.
  Qed.


  Lemma rem_bits_in_digit_le_rem_bits : forall i, 0 <= i < bitsIn limb_widths ->
                                                    i + ((limb_widths # digit_index i) - bit_index i) <= bitsIn limb_widths.
  Proof using Type*.
    intros.
    rewrite <-(split_index_eqn i) at 1 by lia.
    match goal with
    | |- ?a + ?b + (?c - ?b) <= _ => replace (a + b + (c - b)) with (c + a) by ring
    end.
    rewrite <-sum_firstn_succ_default.
    apply sum_firstn_prefix_le; auto.
    pose proof (digit_index_lt_length i H); lia.
  Qed.


  Lemma same_digit : forall i j, 0 <= i <= j ->
                                 j < bitsIn limb_widths ->
                                 j < i + ((limb_widths # (digit_index i)) - bit_index i) ->
                                 (digit_index i = digit_index j)%nat.
  Proof using Type*.
    intros.
    pose proof (split_index_eqn i).
    pose proof (split_index_eqn j).
    specialize_by lia.
    apply le_antisym. {
      eapply sum_firstn_pos_lt_succ; eauto; try (apply digit_index_lt_length; auto; lia).
      rewrite sum_firstn_succ_default.
      eapply Z.le_lt_trans; [ | apply Z.add_lt_mono_r; apply bit_index_not_done; lia ].
      pose proof (bit_index_nonneg i).
      specialize_by lia.
      lia.
    } {
      eapply sum_firstn_pos_lt_succ; eauto; try (apply digit_index_lt_length; auto; lia).
      rewrite <-H2 in H1 at 1.
      match goal with
      | H : _ < ?a + ?b + (?c - ?b) |- _ => replace (a + b + (c - b)) with (c + a) in H by ring;
                                              rewrite <-sum_firstn_succ_default in H
      end.
      rewrite <-H3 in H1.
      pose proof (bit_index_nonneg j). specialize_by lia.
      lia.
    }
  Qed.

  Lemma same_digit_bit_index_sub : forall i j, 0 <= i <= j -> j < bitsIn limb_widths ->
                                               digit_index i = digit_index j ->
                                               bit_index j - bit_index i = j - i.
  Proof using Type.
    intros.
    pose proof (split_index_eqn i).
    pose proof (split_index_eqn j).
    specialize_by lia.
    rewrite H1 in *.
    lia.
  Qed.

End SplitIndex.

Section carrying_helper.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).

  Lemma update_nth_sum : forall n f us, (n < length us \/ n >= length limb_widths)%nat ->
    BaseSystem.decode base (update_nth n f us) =
    (let v := nth_default 0 us n in f v - v) * nth_default 0 base n + BaseSystem.decode base us.
  Proof using Type.
    intros.
    unfold BaseSystem.decode.
    destruct H as [H|H].
    { nth_inbounds; auto. (* TODO(andreser): nth_inbounds should do this auto*)
      erewrite nth_error_value_eq_nth_default by eassumption.
      unfold splice_nth.
      rewrite <- (firstn_skipn n us) at 3.
      do 2 rewrite decode'_splice.
      remember (length (firstn n us)) as n0.
      ring_simplify.
      remember (BaseSystem.decode' (firstn n0 base) (firstn n us)).
      rewrite (skipn_nth_default n us 0) by omega.
      erewrite (nth_error_value_eq_nth_default _ _ us) by eassumption.
      rewrite firstn_length in Heqn0.
      rewrite Min.min_l in Heqn0 by omega; subst n0.
      destruct (le_lt_dec (length limb_widths) n). {
        rewrite (@nth_default_out_of_bounds _ _ base) by (distr_length; auto).
        rewrite skipn_all by (rewrite base_from_limb_widths_length; omega).
        do 2 rewrite decode_base_nil.
        ring_simplify; auto.
      } {
        rewrite (skipn_nth_default n base 0) by (distr_length; omega).
        do 2 rewrite decode'_cons.
        ring_simplify; ring.
      } }
    { rewrite (nth_default_out_of_bounds _ base) by (distr_length; omega); ring_simplify.
      etransitivity; rewrite BaseSystem.decode'_truncate; [ reflexivity | ].
      apply f_equal.
      autorewrite with push_firstn simpl_update_nth.
      rewrite update_nth_out_of_bounds by (distr_length; omega * ).
      reflexivity. }
  Qed.

  Lemma unfold_add_to_nth n x
    : forall xs,
      add_to_nth n x xs
      = match n with
        | O => match xs with
	       | nil => nil
	       | x'::xs' => x + x'::xs'
	       end
        | S n' =>  match xs with
		   | nil => nil
		   | x'::xs' => x'::add_to_nth n' x xs'
		   end
        end.
  Proof using Type.
    induction n; destruct xs; reflexivity.
  Qed.

  Lemma simpl_add_to_nth_0 x
    : forall xs,
      add_to_nth 0 x xs
      = match xs with
        | nil => nil
        | x'::xs' => x + x'::xs'
        end.
  Proof using Type. intro; rewrite unfold_add_to_nth; reflexivity. Qed.

  Lemma simpl_add_to_nth_S x n
    : forall xs,
      add_to_nth (S n) x xs
      = match xs with
        | nil => nil
        | x'::xs' => x'::add_to_nth n x xs'
        end.
  Proof using Type. intro; rewrite unfold_add_to_nth; reflexivity. Qed.

  Hint Rewrite @simpl_set_nth_S @simpl_set_nth_0 : simpl_add_to_nth.

  Lemma add_to_nth_cons : forall x u0 us, add_to_nth 0 x (u0 :: us) = x + u0 :: us.
  Proof using Type. reflexivity. Qed.

  Hint Rewrite @add_to_nth_cons : simpl_add_to_nth.

  Lemma cons_add_to_nth : forall n f y us,
      y :: add_to_nth n f us = add_to_nth (S n) f (y :: us).
  Proof using Type.
    induction n; boring.
  Qed.

  Hint Rewrite <- @cons_add_to_nth : simpl_add_to_nth.

  Lemma add_to_nth_nil : forall n f, add_to_nth n f nil = nil.
  Proof using Type.
    induction n; boring.
  Qed.

  Hint Rewrite @add_to_nth_nil : simpl_add_to_nth.

  Lemma add_to_nth_set_nth n x xs
    : add_to_nth n x xs
      = set_nth n (x + nth_default 0 xs n) xs.
  Proof using Type.
    revert xs; induction n; destruct xs;
      autorewrite with simpl_set_nth simpl_add_to_nth;
      try rewrite IHn;
      reflexivity.
  Qed.
  Lemma add_to_nth_update_nth n x xs
    : add_to_nth n x xs
      = update_nth n (fun y => x + y) xs.
  Proof using Type.
    revert xs; induction n; destruct xs;
      autorewrite with simpl_update_nth simpl_add_to_nth;
      try rewrite IHn;
      reflexivity.
  Qed.

  Lemma length_add_to_nth i x xs : length (add_to_nth i x xs) = length xs.
  Proof using Type. unfold add_to_nth; distr_length; reflexivity. Qed.

  Hint Rewrite @length_add_to_nth : distr_length.

  Lemma set_nth_sum : forall n x us, (n < length us \/ n >= length limb_widths)%nat ->
    BaseSystem.decode base (set_nth n x us) =
    (x - nth_default 0 us n) * nth_default 0 base n + BaseSystem.decode base us.
  Proof using Type. intros; unfold set_nth; rewrite update_nth_sum by assumption; reflexivity. Qed.

  Lemma add_to_nth_sum : forall n x us, (n < length us \/ n >= length limb_widths)%nat ->
    BaseSystem.decode base (add_to_nth n x us) =
    x * nth_default 0 base n + BaseSystem.decode base us.
  Proof using Type. intros; rewrite add_to_nth_set_nth, set_nth_sum; try ring_simplify; auto. Qed.

  Lemma add_to_nth_nth_default_full : forall n x l i d,
    nth_default d (add_to_nth n x l) i =
    if lt_dec i (length l) then
      if (eq_nat_dec i n) then x + nth_default d l i
      else nth_default d l i
    else d.
  Proof using Type. intros; rewrite add_to_nth_update_nth; apply update_nth_nth_default_full; assumption. Qed.
  Hint Rewrite @add_to_nth_nth_default_full : push_nth_default.

  Lemma add_to_nth_nth_default : forall n x l i, (0 <= i < length l)%nat ->
    nth_default 0 (add_to_nth n x l) i =
    if (eq_nat_dec i n) then x + nth_default 0 l i else nth_default 0 l i.
  Proof using Type. intros; rewrite add_to_nth_update_nth; apply update_nth_nth_default; assumption. Qed.
  Hint Rewrite @add_to_nth_nth_default using omega : push_nth_default.

  Lemma log_cap_nonneg : forall i, 0 <= log_cap i.
  Proof using Type*.
    unfold nth_default; intros.
    case_eq (nth_error limb_widths i); intros; try omega.
    apply limb_widths_nonneg.
    eapply nth_error_value_In; eauto.
  Qed. Local Hint Resolve log_cap_nonneg.
End carrying_helper.

Hint Rewrite @simpl_set_nth_S @simpl_set_nth_0 : simpl_add_to_nth.
Hint Rewrite @add_to_nth_cons : simpl_add_to_nth.
Hint Rewrite <- @cons_add_to_nth : simpl_add_to_nth.
Hint Rewrite @add_to_nth_nil : simpl_add_to_nth.
Hint Rewrite @length_add_to_nth : distr_length.
Hint Rewrite @add_to_nth_nth_default_full : push_nth_default.
Hint Rewrite @add_to_nth_nth_default using (omega || distr_length; omega) : push_nth_default.

Section carrying.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).
  Local Hint Resolve limb_widths_nonneg sum_firstn_limb_widths_nonneg.

  Lemma length_carry_gen : forall fc fi i us, length (carry_gen limb_widths fc fi i us) = length us.
  Proof using Type. intros; unfold carry_gen, carry_single; distr_length; reflexivity. Qed.

  Hint Rewrite @length_carry_gen : distr_length.

  Lemma length_carry_simple : forall i us, length (carry_simple limb_widths i us) = length us.
  Proof using Type. intros; unfold carry_simple; distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_simple : distr_length.

  Lemma nth_default_base_succ : forall i, (S i < length limb_widths)%nat ->
    nth_default 0 base (S i) = 2 ^ log_cap i * nth_default 0 base i.
  Proof using Type*.
    intros.
    rewrite !nth_default_base, <- Z.pow_add_r by (omega || eauto using log_cap_nonneg).
    autorewrite with simpl_sum_firstn; reflexivity.
  Qed.

  Lemma carry_gen_decode_eq : forall fc fi i' us
                                     (i := fi i')
                                     (Si := fi (S i)),
    (length us = length limb_widths) ->
    BaseSystem.decode base (carry_gen limb_widths fc fi i' us)
    =  (fc (nth_default 0 us i / 2 ^ log_cap i) *
        (if eq_nat_dec Si (S i)
         then if lt_dec (S i) (length limb_widths)
              then 2 ^ log_cap i * nth_default 0 base i
              else 0
         else nth_default 0 base Si)
        - 2 ^ log_cap i * (nth_default 0 us i / 2 ^ log_cap i) * nth_default 0 base i)
      + BaseSystem.decode base us.
  Proof using Type*.
    intros fc fi i' us i Si H; intros.
    destruct (eq_nat_dec 0 (length limb_widths));
      [ destruct limb_widths, us, i; simpl in *; try congruence;
        break_match;
        unfold carry_gen, carry_single, add_to_nth;
        autorewrite with zsimplify simpl_nth_default simpl_set_nth simpl_update_nth distr_length;
        reflexivity
      | ].
    (*assert (0 <= i < length limb_widths)%nat by (subst i; auto with arith).*)
    assert (0 <= log_cap i) by auto using log_cap_nonneg.
    assert (2 ^ log_cap i <> 0) by (apply Z.pow_nonzero; lia).
    unfold carry_gen, carry_single.
     change (i' mod length limb_widths)%nat with i.
    rewrite add_to_nth_sum by (rewrite length_set_nth; omega).
    rewrite set_nth_sum by omega.
    unfold Z.pow2_mod.
    rewrite Z.land_ones by auto using log_cap_nonneg.
    rewrite Z.shiftr_div_pow2 by auto using log_cap_nonneg.
    change (fi i') with i.
    subst Si.
    repeat first [ ring
                 | match goal with H : _ = _ |- _ => rewrite !H in * end
                 | rewrite nth_default_base_succ by omega
                 | rewrite !(nth_default_out_of_bounds _ base) by (distr_length; omega)
                 | rewrite !(nth_default_out_of_bounds _ us) by omega
                 | rewrite Z.mod_eq by assumption
                 | progress distr_length
                 | progress autorewrite with natsimplify zsimplify in *
                 | progress break_match ].
  Qed.

  Lemma carry_simple_decode_eq : forall i us,
    (length us = length limb_widths) ->
    (i < (pred (length limb_widths)))%nat ->
    BaseSystem.decode base (carry_simple limb_widths i us) = BaseSystem.decode base us.
  Proof using Type*.
    unfold carry_simple; intros; rewrite carry_gen_decode_eq by assumption.
    autorewrite with natsimplify.
    break_match; try lia; autorewrite with zsimplify; lia.
  Qed.


  Lemma length_carry_simple_sequence : forall is us, length (carry_simple_sequence limb_widths is us) = length us.
  Proof using Type.
    unfold carry_simple_sequence.
    induction is; [ reflexivity | simpl; intros ].
    distr_length.
    congruence.
  Qed.
  Hint Rewrite @length_carry_simple_sequence : distr_length.

  Lemma length_make_chain : forall i, length (make_chain i) = i.
  Proof using Type. induction i; simpl; congruence. Qed.
  Hint Rewrite @length_make_chain : distr_length.

  Lemma length_full_carry_chain : length (full_carry_chain limb_widths) = length limb_widths.
  Proof using Type. unfold full_carry_chain; distr_length; reflexivity. Qed.
  Hint Rewrite @length_full_carry_chain : distr_length.

  Lemma length_carry_simple_full us : length (carry_simple_full limb_widths us) = length us.
  Proof using Type. unfold carry_simple_full; distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_simple_full : distr_length.

  (* TODO : move? *)
  Lemma make_chain_lt : forall x i : nat, In i (make_chain x) -> (i < x)%nat.
  Proof using Type.
    induction x; simpl; intuition auto with arith lia.
  Qed.

  Lemma nth_default_carry_gen_full fc fi d i n us
    : nth_default d (carry_gen limb_widths fc fi i us) n
      = if lt_dec n (length us)
        then (if eq_nat_dec n (fi i)
              then Z.pow2_mod (nth_default 0 us n) (log_cap n)
              else nth_default 0 us n) +
             if eq_nat_dec n (fi (S (fi i)))
             then fc (nth_default 0 us (fi i) >> log_cap (fi i))
             else 0
        else d.
  Proof using Type.
    unfold carry_gen, carry_single.
    intros; autorewrite with push_nth_default natsimplify distr_length.
    edestruct (lt_dec n (length us)) as [H|H]; [ | reflexivity ].
    rewrite !(@nth_default_in_bounds Z 0 d) by assumption.
    repeat break_match; subst; try omega; try rewrite_hyp *; omega.
  Qed.

  Hint Rewrite @nth_default_carry_gen_full : push_nth_default.

  Lemma nth_default_carry_simple_full : forall d i n us,
      nth_default d (carry_simple limb_widths i us) n
      = if lt_dec n (length us)
        then if eq_nat_dec n i
             then Z.pow2_mod (nth_default 0 us n) (log_cap n)
             else nth_default 0 us n +
                  if eq_nat_dec n (S i) then nth_default 0 us i >> log_cap i else 0
        else d.
  Proof using Type.
    intros; unfold carry_simple; autorewrite with push_nth_default.
    repeat break_match; try omega; try reflexivity.
  Qed.

  Hint Rewrite @nth_default_carry_simple_full : push_nth_default.

  Lemma nth_default_carry_gen
    : forall fc fi i us,
      (0 <= i < length us)%nat
      -> nth_default 0 (carry_gen limb_widths fc fi i us) i
         = (if eq_nat_dec i (fi i)
            then Z.pow2_mod (nth_default 0 us i) (log_cap i)
            else nth_default 0 us i) +
           if eq_nat_dec i (fi (S (fi i)))
           then fc (nth_default 0 us (fi i) >> log_cap (fi i))
           else 0.
  Proof using Type.
    intros; autorewrite with push_nth_default natsimplify; break_match; omega.
  Qed.
  Hint Rewrite @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.

  Lemma nth_default_carry_simple
    : forall i us,
      (0 <= i < length us)%nat
      -> nth_default 0 (carry_simple limb_widths i us) i
         = Z.pow2_mod (nth_default 0 us i) (log_cap i).
  Proof using Type.
    intros; autorewrite with push_nth_default natsimplify; break_match; omega.
  Qed.
  Hint Rewrite @nth_default_carry_simple using (omega || distr_length; omega) : push_nth_default.
End carrying.

Hint Rewrite @length_carry_gen : distr_length.
Hint Rewrite @length_carry_simple @length_carry_simple_sequence @length_make_chain @length_full_carry_chain @length_carry_simple_full : distr_length.
Hint Rewrite @nth_default_carry_simple_full @nth_default_carry_gen_full : push_nth_default.
Hint Rewrite @nth_default_carry_simple @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.
