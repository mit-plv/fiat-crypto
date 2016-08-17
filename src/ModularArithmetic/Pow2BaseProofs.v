Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Coq.funind.Recdef.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Tactics.
Require Import Crypto.ModularArithmetic.Pow2Base Crypto.BaseSystemProofs.
Require Export Crypto.Util.FixCoqMistakes.
Require Crypto.BaseSystem.
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
  Proof.
    clear limb_widths limb_widths_nonneg.
    induction ls; [ reflexivity | simpl in * ].
    autorewrite with distr_length; auto.
  Qed.
  Hint Rewrite base_from_limb_widths_length : distr_length.

  Lemma base_from_limb_widths_cons : forall l0 l,
    base_from_limb_widths (l0 :: l) = 1 :: map (Z.mul (two_p l0)) (base_from_limb_widths l).
  Proof. reflexivity. Qed.
  Hint Rewrite base_from_limb_widths_cons : push_base_from_limb_widths.
  Hint Rewrite <- base_from_limb_widths_cons : pull_base_from_limb_widths.

  Lemma base_from_limb_widths_nil : base_from_limb_widths nil = nil.
  Proof. reflexivity. Qed.
  Hint Rewrite base_from_limb_widths_nil : push_base_from_limb_widths.

  Lemma firstn_base_from_limb_widths : forall n, firstn n (base_from_limb_widths limb_widths) = base_from_limb_widths (firstn n limb_widths).
  Proof.
    clear limb_widths_nonneg. (* don't use this in the inductive hypothesis *)
    induction limb_widths as [|l ls IHls]; intros [|n]; try reflexivity.
    autorewrite with push_base_from_limb_widths push_firstn; boring.
  Qed.
  Hint Rewrite <- @firstn_base_from_limb_widths : push_base_from_limb_widths pull_firstn.
  Hint Rewrite @firstn_base_from_limb_widths : pull_base_from_limb_widths push_firstn.

  Lemma sum_firstn_limb_widths_nonneg : forall n, 0 <= sum_firstn limb_widths n.
  Proof.
    unfold sum_firstn; intros.
    apply fold_right_invariant; try omega.
    eauto using Z.add_nonneg_nonneg, limb_widths_nonneg, In_firstn.
  Qed. Hint Resolve sum_firstn_limb_widths_nonneg.

  Lemma two_sum_firstn_limb_widths_pos n : 0 < 2^sum_firstn limb_widths n.
  Proof. auto with zarith. Qed.

  Lemma two_sum_firstn_limb_widths_nonzero n : 2^sum_firstn limb_widths n <> 0.
  Proof. pose proof (two_sum_firstn_limb_widths_pos n); omega. Qed.

  Lemma base_from_limb_widths_step : forall i b w, (S i < length limb_widths)%nat ->
    nth_error base i = Some b ->
    nth_error limb_widths i = Some w ->
    nth_error base (S i) = Some (two_p w * b).
  Proof.
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
      destruct nth_err_w as [x [A B]].
      subst.
      replace (two_p w * (two_p a * x)) with (two_p a * (two_p w * x)) by ring.
      apply map_nth_error.
      apply IHl; auto. omega.
  Qed.


  Lemma nth_error_base : forall i, (i < length limb_widths)%nat ->
    nth_error base i = Some (two_p (sum_firstn limb_widths i)).
  Proof.
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
  Proof.
    intros ? ? i_lt_length.
    apply nth_error_value_eq_nth_default.
    rewrite nth_error_base, two_p_correct by assumption.
    reflexivity.
  Qed.

  Lemma base_succ : forall i, ((S i) < length limb_widths)%nat ->
    nth_default 0 base (S i) mod nth_default 0 base i = 0.
  Proof.
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
   Proof.
     intros i b nth_err_b.
     pose proof (nth_error_value_length _ _ _ _ nth_err_b).
     rewrite base_from_limb_widths_length in *.
     rewrite nth_error_base in nth_err_b by assumption.
     rewrite two_p_correct in nth_err_b.
     congruence.
   Qed.

   Lemma base_positive : forall b : Z, In b base -> b > 0.
   Proof.
     intros b In_b_base.
     apply In_nth_error_value in In_b_base.
     destruct In_b_base as [i nth_err_b].
     apply nth_error_subst in nth_err_b.
     rewrite nth_err_b.
     apply Z.gt_lt_iff.
     apply Z.pow_pos_nonneg; omega || auto using sum_firstn_limb_widths_nonneg.
   Qed.

   Lemma b0_1 : forall x : Z, limb_widths <> nil -> nth_default x base 0 = 1.
   Proof.
     case_eq limb_widths; intros; [congruence | reflexivity].
   Qed.

  Lemma base_from_limb_widths_app : forall l0 l
                                           (l0_nonneg : forall x, In x l0 -> 0 <= x)
                                           (l_nonneg : forall x, In x l -> 0 <= x),
      base_from_limb_widths (l0 ++ l)
      = base_from_limb_widths l0 ++ map (Z.mul (two_p (sum_firstn l0 (length l0)))) (base_from_limb_widths l).
  Proof.
    induction l0 as [|?? IHl0].
    { simpl; intros; rewrite <- map_id at 1; apply map_ext; intros; omega. }
    { simpl; intros; rewrite !IHl0, !map_app, map_map, sum_firstn_succ_cons, two_p_is_exp by auto with znonzero.
      do 2 f_equal; apply map_ext; intros; lia. }
  Qed.

  Lemma skipn_base_from_limb_widths : forall n, skipn n (base_from_limb_widths limb_widths) = map (Z.mul (two_p (sum_firstn limb_widths n))) (base_from_limb_widths (skipn n limb_widths)).
  Proof.
    intro n; pose proof (base_from_limb_widths_app (firstn n limb_widths) (skipn n limb_widths)) as H.
    specialize_by eauto using In_firstn, In_skipn.
    autorewrite with simpl_firstn simpl_skipn in *.
    rewrite H, skipn_app, skipn_all by auto with arith distr_length; clear H.
    simpl; distr_length.
    apply Min.min_case_strong; intro;
      unfold sum_firstn; autorewrite with natsimplify simpl_skipn simpl_firstn;
        reflexivity.
  Qed.
  Hint Rewrite <- @skipn_base_from_limb_widths : push_base_from_limb_widths pull_skipn.
  Hint Rewrite @skipn_base_from_limb_widths : pull_base_from_limb_widths push_skipn.

  Lemma pow2_mod_bounded :forall lw us i, (forall w, In w lw -> 0 <= w) -> bounded lw us ->
                                          Z.pow2_mod (nth_default 0 us i) (nth_default 0 lw i) = nth_default 0 us i.
  Proof.
    clear limb_widths limb_widths_nonneg.
  Admitted.

  Lemma pow2_mod_bounded_iff :forall lw us, (forall w, In w lw -> 0 <= w) -> bounded lw us <->
    forall i, Z.pow2_mod (nth_default 0 us i) (nth_default 0 lw i) = nth_default 0 us i.
  Proof.
    clear limb_widths limb_widths_nonneg.
  Admitted.

  Lemma bounded_nil_iff : forall us, bounded nil us <-> (forall u, In u us -> u = 0).
  Proof.
    clear limb_widths limb_widths_nonneg.
  Admitted.

  Lemma bounded_iff : forall lw us, bounded lw us <-> forall i, 0 <= nth_default 0 us i < 2 ^ nth_default 0 lw i.
  Proof.
    clear limb_widths limb_widths_nonneg.
  Admitted.

  Lemma digit_select : forall us i, bounded limb_widths us ->
                                    nth_default 0 us i = Z.pow2_mod (BaseSystem.decode base us >> sum_firstn limb_widths i) (nth_default 0 limb_widths i).
  Proof.
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
            autorewrite with Ztestbit.
            rewrite Z.testbit_neg_r with (n := n - w) by omega.
            autorewrite with Ztestbit. f_equal; ring.
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
  Proof.
    intros; apply nth_default_preserves_properties; auto; omega.
  Qed. Hint Resolve nth_default_limb_widths_nonneg.

  Lemma decode_firstn_pow2_mod : forall us i,
    (i <= length us)%nat ->
    length us = length limb_widths ->
    bounded limb_widths us ->
    BaseSystem.decode' base (firstn i us) = Z.pow2_mod (BaseSystem.decode' base us) (sum_firstn limb_widths i).
  Proof.
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
  Proof.
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
  Proof.
    intros.
    erewrite <-(firstn_all _ us) by reflexivity.
    auto using testbit_decode_firstn_high.
  Qed.

  (* TODO : move to ZUtil *)
  Lemma testbit_false_bound : forall a x, 0 <= x ->
    (forall n, ~ (n < x) -> Z.testbit a n = false) ->
    a < 2 ^ x.
  Proof.
    intros.
    assert (a = Z.pow2_mod a x). {
     apply Z.bits_inj'; intros.
     rewrite Z.testbit_pow2_mod by omega; break_if; auto.
    }
    rewrite H1.
    rewrite Z.pow2_mod_spec; try apply Z.mod_pos_bound; zero_bounds.
  Qed.

  (** TODO: Figure out how to automate and clean up this proof *)
  Lemma decode_nonneg : forall us,
    length us = length limb_widths ->
    bounded limb_widths us ->
    0 <= BaseSystem.decode base us.
  Proof.
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
  Proof.
    cbv [upper_bound]; intros.
    split.
    { apply decode_nonneg; auto. }
    { apply testbit_false_bound; auto; intros.
      rewrite testbit_decode_high; auto;
        replace (length us) with (length limb_widths); try omega. }
  Qed.

  Lemma decode_firstn_succ : forall us i,
      (S i <= length us)%nat ->
      bounded limb_widths us ->
      length us = length limb_widths ->
      BaseSystem.decode base (firstn (S i) us) =
      Z.lor (BaseSystem.decode base (firstn i us)) (nth_default 0 us i << sum_firstn limb_widths i).
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
    unfold BaseSystem.decode; intros us0 us1 ?.
    assert (0 <= sum_firstn limb_widths (length us0)) by auto using sum_firstn_nonnegative.
    rewrite decode'_splice; autorewrite with push_firstn.
    apply Z.add_cancel_l.
    autorewrite with pull_base_from_limb_widths Zshift_to_pow zsimplify.
    rewrite decode'_map_mul, two_p_correct; nia.
  Qed.

  Lemma decode_shift : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << (nth_default 0 limb_widths 0)).
  Proof.
    intros; etransitivity; [ apply (decode_shift_app (u0::nil)); assumption | ].
    transitivity (u0 * 1 + 0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << (nth_default 0 limb_widths 0 + 0))); [ | autorewrite with zsimplify; reflexivity ].
    destruct limb_widths; distr_length; reflexivity.
  Qed.

  Lemma upper_bound_nil : upper_bound nil = 1.
  Proof. reflexivity. Qed.

  Lemma upper_bound_cons x xs : 0 <= x -> 0 <= sum_firstn xs (length xs) -> upper_bound (x::xs) = 2^x * upper_bound xs.
  Proof.
    intros Hx Hxs.
    unfold upper_bound; simpl.
    autorewrite with simpl_sum_firstn pull_Zpow.
    reflexivity.
  Qed.

  Lemma upper_bound_app xs ys : 0 <= sum_firstn xs (length xs) -> 0 <= sum_firstn ys (length ys) -> upper_bound (xs ++ ys) = upper_bound xs * upper_bound ys.
  Proof.
    intros Hxs Hys.
    unfold upper_bound; simpl.
    autorewrite with distr_length simpl_sum_firstn pull_Zpow.
    reflexivity.
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
    Proof.
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
    Proof.
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

Hint Rewrite <- @firstn_base_from_limb_widths : push_base_from_limb_widths pull_firstn.
Hint Rewrite @firstn_base_from_limb_widths : pull_base_from_limb_widths push_firstn.
Hint Rewrite <- @skipn_base_from_limb_widths : push_base_from_limb_widths pull_skipn.
Hint Rewrite @skipn_base_from_limb_widths : pull_base_from_limb_widths push_skipn.

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
  Local Notation "w[ i ]" := (nth_default 0 limb_widths i).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation upper_bound := (upper_bound limb_widths).

  Lemma encode'_spec : forall x i, (i <= length limb_widths)%nat ->
    encode' limb_widths x i = BaseSystem.encode' base x upper_bound i.
  Proof.
    induction i; intros.
    + rewrite encode'_zero. reflexivity.
    + rewrite encode'_succ, <-IHi by omega.
      simpl; do 2 f_equal.
      rewrite Z.land_ones, Z.shiftr_div_pow2 by auto using sum_firstn_limb_widths_nonneg.
      match goal with H : (S _ <= length limb_widths)%nat |- _ =>
        apply le_lt_or_eq in H; destruct H end.
      - repeat f_equal; rewrite nth_default_base by (omega || auto); reflexivity.
      - repeat f_equal; try solve [rewrite nth_default_base by (omega || auto); reflexivity].
        rewrite nth_default_out_of_bounds by (distr_length; omega).
        unfold Pow2Base.upper_bound.
        congruence.
  Qed.

  Lemma base_upper_bound_compatible : @base_max_succ_divide base upper_bound.
  Proof.
    unfold base_max_succ_divide; intros i lt_Si_length.
    rewrite base_from_limb_widths_length in lt_Si_length.
    rewrite Nat.lt_eq_cases in lt_Si_length; destruct lt_Si_length;
      rewrite !nth_default_base by (omega || auto).
    + erewrite sum_firstn_succ by (eapply nth_error_Some_nth_default with (x := 0); omega).
      rewrite Z.pow_add_r; eauto using sum_firstn_limb_widths_nonneg, nth_default_limb_widths_nonneg.
      apply Z.divide_factor_r.
    + rewrite nth_default_out_of_bounds by (distr_length; omega).
      unfold Pow2Base.upper_bound.
      replace (length limb_widths) with (S (pred (length limb_widths))) by omega.
      replace i with (pred (length limb_widths)) by omega.
      erewrite sum_firstn_succ by (eapply nth_error_Some_nth_default with (x := 0); omega).
      rewrite Z.pow_add_r; eauto using sum_firstn_limb_widths_nonneg, nth_default_limb_widths_nonneg.
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
      zero_bounds; intros; eauto using sum_firstn_limb_widths_nonneg, base_positive, b0_1. {
      rewrite nth_default_out_of_bounds by omega.
      reflexivity.
    } {
      econstructor; try apply base_good;
        eauto using base_positive, b0_1.
    }
  Qed.

  Lemma encodeZ_length : forall x, length (encodeZ limb_widths x) = length limb_widths.
  Proof.
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
  Proof.
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
      end.
  Qed.

  Lemma decode_bitwise'_invariant_holds : forall i us acc,
    length us = length limb_widths ->
    bounded limb_widths us ->
    decode_bitwise'_invariant us i acc ->
    decode_bitwise'_invariant us 0 (decode_bitwise' limb_widths us i acc).
  Proof.
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
  Proof.
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
   Proof.
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
  Proof.
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
  Proof.
    intros; rewrite nth_default_uniform_base_full.
    edestruct lt_dec; omega.
  Qed.

  Lemma sum_firstn_uniform_base : forall i, (i <= length limb_widths)%nat ->
                                            sum_firstn limb_widths i = Z.of_nat i * width.
  Proof.
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
  Proof.
    intros; rewrite sum_firstn_all, sum_firstn_uniform_base by omega; reflexivity.
  Qed.

  Lemma upper_bound_uniform : upper_bound limb_widths = 2^(Z.of_nat (length limb_widths) * width).
  Proof.
    unfold upper_bound; rewrite sum_firstn_uniform_base_strong by omega; reflexivity.
  Qed.

  (* TODO : move *)
  Lemma decode_truncate_base : forall bs us, BaseSystem.decode bs us = BaseSystem.decode (firstn (length us) bs) us.
  Admitted.

  (* TODO : move *)
  Lemma tl_repeat : forall {A} xs n (x : A), (forall y, In y xs -> y = x) ->
                                             (n < length xs)%nat ->
                                             firstn n xs = firstn n (tl xs).
  Proof.
    intros.
    erewrite (repeat_spec_eq xs) by first [ eassumption | reflexivity ].
    rewrite ListUtil.tl_repeat.
    autorewrite with push_firstn.
    apply f_equal; omega *.
  Qed.

  Lemma decode_tl_base : forall us, (length us < length limb_widths)%nat ->
      BaseSystem.decode base us = BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us.
  Proof.
    intros.
    match goal with |- BaseSystem.decode ?b1 _ = BaseSystem.decode ?b2 _ =>
      rewrite (decode_truncate_base b1), (decode_truncate_base b2) end.
    rewrite !firstn_base_from_limb_widths.
    do 2 f_equal.
    eauto using tl_repeat.
  Qed.

  Lemma decode_shift_uniform_tl : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << width).
  Proof.
    intros.
    rewrite <- (nth_default_uniform_base 0) by distr_length.
    rewrite decode_shift by auto using uniform_limb_widths_nonneg.
    reflexivity.
  Qed.

  Lemma decode_shift_uniform_app : forall us0 us1, (length (us0 ++ us1) <= length limb_widths)%nat ->
    BaseSystem.decode base (us0 ++ us1) = (BaseSystem.decode (base_from_limb_widths (firstn (length us0) limb_widths)) us0) + ((BaseSystem.decode (base_from_limb_widths (skipn (length us0) limb_widths)) us1) << (Z.of_nat (length us0) * width)).
  Proof.
    intros.
    rewrite <- sum_firstn_uniform_base by (distr_length; omega).
    rewrite decode_shift_app by auto using uniform_limb_widths_nonneg.
    reflexivity.
  Qed.

  Lemma decode_shift_uniform : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode base us) << width).
  Proof.
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
  Local Notation "u # i" := (nth_default 0 u i) (at level 30).

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

  Context limb_widths (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Hint Resolve limb_widths_nonneg.
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation bitsIn lw := (sum_firstn lw (length lw)).

  Definition split_index i := split_index' i 0 limb_widths.
  Definition digit_index i := fst (split_index i).
  Definition bit_index i := snd (split_index i).

  Lemma testbit_decode : forall us n,
    0 <= n ->
    length us = length limb_widths ->
    bounded limb_widths us ->
    Z.testbit (BaseSystem.decode base us) n = Z.testbit (us # digit_index n) (bit_index n).
  Proof.
    cbv [digit_index bit_index split_index]; intros.
    pose proof (split_index'_correct n 0 limb_widths).
    pose proof (snd_split_index'_nonneg 0 limb_widths n).
    specialize_by assumption.
    repeat match goal with
           | |- _ => progress autorewrite with Ztestbit natsimplify in *
           | |- _ => erewrite digit_select by eassumption
           | |- _ => break_if
           | |- _ => rewrite Z.testbit_pow2_mod by auto using nth_default_limb_widths_nonneg
           | |- _ => omega
           | |- _ => f_equal; omega
           end.
    destruct (Z_lt_dec n (sum_firstn limb_widths (length limb_widths))). {
      assert (0 <= n < sum_firstn limb_widths (length limb_widths)) as Hn by omega.
      pose proof (snd_split_index'_small n 0 limb_widths Hn).
      rewrite Nat.sub_0_r in *.
      omega.
    } {
      apply testbit_decode_high; auto.
      replace (length us) with (length limb_widths) in *.
      omega.
    }
  Qed.

  Lemma digit_index_not_done : forall i, 0 <= i < bitsIn limb_widths ->
                                         (digit_index i < length limb_widths)%nat.
  Proof.
  Admitted.

  Lemma bit_index_not_done : forall i, 0 <= i < bitsIn limb_widths ->
                                         (bit_index i < limb_widths # digit_index i).
  Admitted.

  Lemma bit_index_nonneg : forall i, 0 <= i -> 0 <= bit_index i.
  Admitted.

  Lemma rem_bits_in_digit_pos : forall i, 0 <= i < bitsIn limb_widths ->
                                          0 < limb_widths # digit_index i - bit_index i.
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- 0 < ?a - ?b => destruct (Z_lt_dec b a); [ lia | exfalso ]
           | H : ~ (bit_index ?i < limb_widths # digit_index ?i) |- _ =>
             pose proof (bit_index_not_done i); specialize_by omega; omega
           end.
  Qed.

    Lemma rem_bits_in_digit_le_rem_bits : forall i, 0 <= i < bitsIn limb_widths ->
                                                    i + (limb_widths # digit_index i - bit_index i) <= bitsIn limb_widths.
  Admitted.

  Lemma split_index_done_case : forall i, 0 <= i ->
    if Z_lt_dec i (sum_firstn limb_widths (length limb_widths))
    then (digit_index i < length limb_widths)%nat /\ 0 < limb_widths # (digit_index i) - bit_index i
    else (digit_index i = length limb_widths) /\ limb_widths # (digit_index i) - bit_index i <= 0.
  Proof.
  Admitted.

  Lemma bit_index_pos_iff : forall i, 0 <= i ->
                                  0 < limb_widths # (digit_index i) - bit_index i <->
                                  i < sum_firstn limb_widths (length limb_widths).

  Admitted.

  Lemma digit_index_not_lt_length : forall i, 0 <= i ->
                                              ~ (digit_index i < length limb_widths)%nat ->
                                              sum_firstn limb_widths (length limb_widths) <= i.
  Admitted.


  Lemma le_remaining_bits : forall i, 0 <= i < sum_firstn limb_widths (length limb_widths) ->
                                      0 <= sum_firstn limb_widths (length limb_widths)
                                           - (i + (limb_widths # (digit_index i) - bit_index i)).
  Admitted.

  Lemma same_digit : forall i j, 0 <= i <= j -> j < i + (limb_widths # (digit_index i) - bit_index i) ->
                                 digit_index i = digit_index j.
  Admitted.

  Lemma same_digit_bit_index_sub : forall i j, 0 <= i <= j ->
                                               digit_index i = digit_index j ->
                                               bit_index j - bit_index i = j - i.
  Admitted.

End SplitIndex.

Section ConversionHelper.
  Local Hint Resolve in_eq in_cons.

  (* concatenates first n bits of a with all bits of b *)
  Definition concat_bits n a b := Z.lor (Z.pow2_mod a n) (b << n).

  Lemma concat_bits_spec : forall a b n i, 0 <= n ->
                                           Z.testbit (concat_bits n a b) i =
                                           if Z_lt_dec i n then Z.testbit a i else Z.testbit b (i - n).
  Proof.
    repeat match goal with
           | |- _ => progress cbv [concat_bits]; intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => rewrite Z.testbit_pow2_mod by omega
           | |- _ => rewrite Z.testbit_neg_r by omega
           | |- _ => break_if
           | |- appcontext [Z.testbit (?a << ?b) ?i] => destruct (Z_le_dec 0 i)
           | |- (?a || ?b)%bool = ?a => replace b with false
           | |- _ => reflexivity
           end.
  Qed.

  Definition update_by_concat_bits num_low_bits bits x := concat_bits num_low_bits x bits.

End ConversionHelper.

Section Conversion.
  Context {limb_widthsA} (limb_widthsA_nonneg : forall w, In w limb_widthsA -> 0 <= w)
          {limb_widthsB} (limb_widthsB_nonneg : forall w, In w limb_widthsB -> 0 <= w).
  Local Notation bitsIn lw := (sum_firstn lw (length lw)).
  Context (bits_fit : bitsIn limb_widthsA <=  bitsIn limb_widthsB).
  Local Notation decodeA := (BaseSystem.decode (base_from_limb_widths limb_widthsA)).
  Local Notation decodeB := (BaseSystem.decode (base_from_limb_widths limb_widthsB)).
  Local Notation "u # i" := (nth_default 0 u i) (at level 30).
  Local Hint Resolve in_eq in_cons nth_default_limb_widths_nonneg sum_firstn_limb_widths_nonneg Nat2Z.is_nonneg.
  Local Opaque bounded.

  Function convert' inp i out
           {measure (fun x => Z.to_nat ((bitsIn limb_widthsA) - Z.of_nat x)) i}:=
    if Z_le_dec (bitsIn limb_widthsA) (Z.of_nat i)
    then out
    else
      let digitA := digit_index limb_widthsA (Z.of_nat i) in
      let digitB := digit_index limb_widthsB (Z.of_nat i) in
      let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
      let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
      let dist := Z.min (limb_widthsA # digitA - indexA) (limb_widthsB # digitB - indexB) in
      let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
      convert' inp (i + Z.to_nat dist)%nat (update_nth digitB (update_by_concat_bits indexB bitsA) out).
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | H : forall x : Z, In x ?lw -> x = ?y, H0 : 0 < ?y |- _ =>
            unique pose proof (uniform_limb_widths_nonneg H0 lw H)
           | H : forall x : Z, In x ?lw -> 0 <= x |- appcontext [bit_index ?lw ?i] =>
             unique pose proof (bit_index_not_done lw H i)
           | H : forall x : Z, In x ?lw -> 0 <= x |- appcontext [bit_index ?lw ?i] =>
             unique pose proof (rem_bits_in_digit_le_rem_bits lw H i)
           | |- _ => rewrite Z2Nat.id
           | |- _ => rewrite Nat2Z.inj_add
           | |- (Z.to_nat _ < Z.to_nat _)%nat => apply Z2Nat.inj_lt
           | |- (?a - _ < ?a - _) => apply Z.sub_lt_mono_l
           | |- appcontext [Z.min ?a ?b] => unique assert (0 < Z.min a b) by (specialize_by lia; lia)
           | |- _ => lia
    end.
  Defined.

  Definition convert'_invariant inp i out :=
    length out = length limb_widthsB
    /\ bounded limb_widthsB out
    /\ Z.of_nat i <= bitsIn limb_widthsA
    /\ forall n, Z.testbit (decodeB out) n = if Z_lt_dec n (Z.of_nat i) then Z.testbit (decodeA inp) n else false.

  Ltac subst_lia := repeat match goal with | x := _ |- _ => subst x end; subst; lia.

  Lemma convert'_bounded_step : forall inp i out,
    bounded limb_widthsB out ->
    let digitA := digit_index limb_widthsA (Z.of_nat i) in
    let digitB := digit_index limb_widthsB (Z.of_nat i) in
    let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
    let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
    let dist := Z.min (limb_widthsA # digitA - indexA)
                      (limb_widthsB # digitB - indexB) in
    let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
    0 < dist ->
    bounded limb_widthsB (update_nth digitB (update_by_concat_bits indexB bitsA) out).
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => rewrite update_nth_nth_default_full
           | |- _ => rewrite Z.testbit_pow2_mod
           | |- _ => break_if
           | |- _ =>  progress cbv [update_by_concat_bits];
                        rewrite concat_bits_spec by (apply bit_index_nonneg; auto using Nat2Z.is_nonneg)
           | |- bounded _ _ => apply pow2_mod_bounded_iff
           | |- Z.pow2_mod _ _ = _ => apply Z.bits_inj'
           | |- false = Z.testbit _ _ => symmetry
           | x := _ |- Z.testbit ?x _ = _ => subst x
           | |- Z.testbit _ _ = false => eapply testbit_bounded_high; eauto; lia
           | |- _ => solve [auto]
           | |- _ => subst_lia
    end.
  Qed.

  Lemma convert'_index_step : forall inp i out,
    bounded limb_widthsB out ->
    let digitA := digit_index limb_widthsA (Z.of_nat i) in
    let digitB := digit_index limb_widthsB (Z.of_nat i) in
    let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
    let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
    let dist := Z.min (limb_widthsA # digitA - indexA)
                      (limb_widthsB # digitB - indexB) in
    let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
    0 < dist ->
    Z.of_nat i + dist <= bitsIn limb_widthsA.
  Proof.
    pose proof (le_remaining_bits limb_widthsA).
    pose proof (le_remaining_bits limb_widthsB).
    repeat match goal with
           | |- _ => progress intros
           | H : forall x : Z, In x ?lw -> x = ?y, H0 : 0 < ?y |- _ =>
              unique pose proof (uniform_limb_widths_nonneg H0 lw H)
           | |- _ => progress specialize_by assumption
           | H : _ /\ _ |- _ => destruct H
           | |- _ => break_if
           | |- _ => split
           | a := digit_index _ ?i, H : forall x, 0 <= x < bitsIn _ -> _ |- _ => specialize (H i); forward H
           | |- _ => subst_lia
           | |- _ => apply bit_index_pos_iff; auto
           | |- _ => apply Nat2Z.is_nonneg
    end.
  Qed.

  Lemma convert'_invariant_step : forall inp i out,
    length inp = length limb_widthsA ->
    bounded limb_widthsA inp ->
    convert'_invariant inp i out ->
    let digitA := digit_index limb_widthsA (Z.of_nat i) in
    let digitB := digit_index limb_widthsB (Z.of_nat i) in
    let indexA :=   bit_index limb_widthsA (Z.of_nat i) in
    let indexB :=   bit_index limb_widthsB (Z.of_nat i) in
    let dist := Z.min (limb_widthsA # digitA - indexA)
                      (limb_widthsB # digitB - indexB) in
    let bitsA := Z.pow2_mod ((inp # digitA) >> indexA) dist in
    0 < dist ->
    convert'_invariant inp (i + Z.to_nat dist)%nat
                       (update_nth digitB (update_by_concat_bits indexB bitsA) out).
  Proof.
    repeat match goal with
           | |- _ => progress intros; cbv [convert'_invariant] in *
           | |- _ => progress autorewrite with Ztestbit
           | H : length _ = length limb_widthsB |- _ => rewrite H
           | |- _ => rewrite Z.testbit_neg_r by omega
           | |- _ => rewrite Nat2Z.inj_add
           | |- _ => rewrite Z2Nat.id in *
           | |- _ => rewrite update_nth_nth_default_full
           | |- _ => rewrite nth_default_out_of_bounds by omega
           | |- false = Z.testbit _ _ =>
             rewrite testbit_decode_high; auto;
               match goal with H : length _ = length limb_widthsA |- _ => rewrite H end;
                 etransitivity; [ apply bits_fit | ]; apply digit_index_not_lt_length; auto
           | |- _ =>  progress cbv [update_by_concat_bits];
                        rewrite concat_bits_spec by (apply bit_index_nonneg; auto using Nat2Z.is_nonneg)
           | H : _ /\ _ |- _ => destruct H
           | |- _ => break_if
           | |- _ => split
           | H : forall n, Z.testbit (decodeB _) n = _ |- Z.testbit (decodeB _) ?n = _ =>
             specialize (H n)
           | H : _ = Z.testbit (decodeA _) ?n |- Z.testbit (decodeB _) ?n = Z.testbit (decodeA _) ?n =>
             rewrite <-H
           | H : 0 <= ?n |- appcontext[Z.testbit (BaseSystem.decode _ _) ?n] =>
             rewrite testbit_decode by
                 (distr_length; eauto using convert'_bounded_step)
           | |- Z.testbit (decodeB _) ?n = _ =>
              destruct (Z_le_dec 0 n)
           | |- _ => solve [distr_length]
           | |- _ => eapply convert'_bounded_step; solve [eauto]
           | |- _ => eapply convert'_index_step; solve [eauto]
           | |- _ => lia
           | x := ?y |- Z.testbit ?x _ =  _ => subst x
           | d1 := digit_index ?lw _ |-digit_index ?lw _ = ?d1 =>
                   symmetry; apply same_digit; eauto; subst_lia
           | d1 := digit_index ?lw _ |- Z.testbit (?a # ?d1) _ = Z.testbit (?a # ?d2) _ =>
                   assert (d2 = d1); [ | repeat f_equal]
           | H : ~ (?n < ?i), H0 : ?n < ?i + ?d,
               d1 := digit_index ?lw ?i, H1 : digit_index ?lw ?n <> ?d1 |- _ => exfalso; apply H1
           | d := digit_index ?lw ?j,
                   b := bit_index ?lw ?j,
                   H : digit_index ?lw ?i = ?d |- _ =>
                   let A := fresh "H" in
                   let B := fresh "H" in
                   (   (assert (0 <= i <= j) as A by omega)
                       || (assert (0 <= j <= i) as A by omega; symmetry in H));
                   assert (forall w, In w lw -> 0 <= w) as B by auto;
                   pose proof (same_digit_bit_index_sub lw B _ _ A H); subst b
           | |- _ => rewrite <- testbit_decode by
                 (distr_length; eauto using convert'_bounded_step); assumption
    end.
  Qed.

  Lemma convert'_termination_condition : forall i, 0 <= i ->
    let digitA := digit_index limb_widthsA i in
    let digitB := digit_index limb_widthsB i in
    let indexA :=   bit_index limb_widthsA i in
    let indexB :=   bit_index limb_widthsB i in
    let dist := Z.min (limb_widthsA # digitA - indexA)
                      (limb_widthsB # digitB - indexB) in
    dist <= 0  -> bitsIn limb_widthsA <= i.
  Proof.
    pose proof (split_index_done_case limb_widthsA).
    pose proof (split_index_done_case limb_widthsB).
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress specialize_by assumption
           | H : _ /\ _ |- _ => destruct H
           | |- _ => break_if
           | H : 0 <= ?i, H0 : forall x, 0 <= x -> if _ then _ else _ |- _ => specialize (H0 i H)
           | |- _ => repeat match goal with x := _ |- _ => subst x end; subst; lia
           end.
  Qed.

  Lemma convert'_invariant_holds : forall inp i out,
    length inp = length limb_widthsA ->
    bounded limb_widthsA inp ->
    convert'_invariant inp i out ->
    convert'_invariant inp (Z.to_nat (bitsIn limb_widthsA)) (convert' inp i out).
  Proof.
    intros until 2; functional induction (convert' inp i out);
      repeat match goal with
           | |- _ => progress intros
           | H : forall x : Z, In x ?lw -> 0 <= x |- appcontext [bit_index ?lw ?i] =>
              unique pose proof (bit_index_not_done lw H i)
           | H : convert'_invariant _ _ _ |- convert'_invariant _ _ (convert' _ _ _) =>
             eapply convert'_invariant_step in H; solve [auto; specialize_by lia; lia]
           | H : convert'_invariant _ _ ?out |- convert'_invariant _ _ ?out => progress cbv [convert'_invariant] in *
           | H : _ /\ _ |- _ => destruct H
           | |- _ => rewrite Z2Nat.id
           | |- _ => split
           | |- _ => assumption
           | |- _ => lia
           | |- _ => solve [eauto]
           | |- _ => replace (bitsIn limb_widthsA) with (Z.of_nat i) by (apply Z.le_antisymm; assumption)
             end.
  Qed.

  Definition convert us := convert' us 0 (BaseSystem.zeros (length limb_widthsB)).

  Lemma convert_correct : forall us, length us = length limb_widthsA ->
                                     bounded limb_widthsA us ->
                                     decodeA us = decodeB (convert us).
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress cbv [convert convert'_invariant] in *
           | |- _ => progress change (Z.of_nat 0) with 0 in *
           | |- _ => progress rewrite ?length_zeros, ?zeros_rep, ?Z.testbit_0_l
           | H : length _ = length limb_widthsA |- _ => rewrite H
           | |- _ => rewrite Z.testbit_neg_r by omega
           | |- _ => rewrite nth_default_zeros
           | |- _ => break_if
           | |- _ => split
           | H : _ /\ _ |- _ => destruct H
           | H : forall n, Z.testbit ?x n = _ |- _ = ?x => apply Z.bits_inj'; intros; rewrite H
           | |- _ = decodeB (convert' ?a ?b ?c) => edestruct (convert'_invariant_holds a b c)
           | |- _ => apply testbit_decode_high
           | |- _ => assumption
           | |- _ => reflexivity
           | |- _ => lia
           | |- _ => solve [auto using sum_firstn_limb_widths_nonneg]
           | |- _ => solve [apply nth_default_preserves_properties; auto; lia]
           | |- _ => rewrite Z2Nat.id in *
           | |- bounded _ _ => apply bounded_iff
           | |- 0 < 2 ^ _ => zero_bounds
           end.
  Qed.

  (* This is part of convert'_invariant, but proving it separately strips preconditions *)
  Lemma length_convert' : forall inp i out,
    length (convert' inp i out) = length out.
  Proof.
    intros; functional induction (convert' inp i out); distr_length.
  Qed.

  Lemma length_convert : forall us, length (convert us) = length limb_widthsB.
  Proof.
    cbv [convert]; intros.
    rewrite length_convert', length_zeros.
    reflexivity.
  Qed.
End Conversion.

Section carrying_helper.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).
  Local Notation log_cap i := (nth_default 0 limb_widths i).

  Lemma update_nth_sum : forall n f us, (n < length us \/ n >= length limb_widths)%nat ->
    BaseSystem.decode base (update_nth n f us) =
    (let v := nth_default 0 us n in f v - v) * nth_default 0 base n + BaseSystem.decode base us.
  Proof.
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
  Proof.
    induction n; destruct xs; reflexivity.
  Qed.

  Lemma simpl_add_to_nth_0 x
    : forall xs,
      add_to_nth 0 x xs
      = match xs with
        | nil => nil
        | x'::xs' => x + x'::xs'
        end.
  Proof. intro; rewrite unfold_add_to_nth; reflexivity. Qed.

  Lemma simpl_add_to_nth_S x n
    : forall xs,
      add_to_nth (S n) x xs
      = match xs with
        | nil => nil
        | x'::xs' => x'::add_to_nth n x xs'
        end.
  Proof. intro; rewrite unfold_add_to_nth; reflexivity. Qed.

  Hint Rewrite @simpl_set_nth_S @simpl_set_nth_0 : simpl_add_to_nth.

  Lemma add_to_nth_cons : forall x u0 us, add_to_nth 0 x (u0 :: us) = x + u0 :: us.
  Proof. reflexivity. Qed.

  Hint Rewrite @add_to_nth_cons : simpl_add_to_nth.

  Lemma cons_add_to_nth : forall n f y us,
      y :: add_to_nth n f us = add_to_nth (S n) f (y :: us).
  Proof.
    induction n; boring.
  Qed.

  Hint Rewrite <- @cons_add_to_nth : simpl_add_to_nth.

  Lemma add_to_nth_nil : forall n f, add_to_nth n f nil = nil.
  Proof.
    induction n; boring.
  Qed.

  Hint Rewrite @add_to_nth_nil : simpl_add_to_nth.

  Lemma add_to_nth_set_nth n x xs
    : add_to_nth n x xs
      = set_nth n (x + nth_default 0 xs n) xs.
  Proof.
    revert xs; induction n; destruct xs;
      autorewrite with simpl_set_nth simpl_add_to_nth;
      try rewrite IHn;
      reflexivity.
  Qed.
  Lemma add_to_nth_update_nth n x xs
    : add_to_nth n x xs
      = update_nth n (fun y => x + y) xs.
  Proof.
    revert xs; induction n; destruct xs;
      autorewrite with simpl_update_nth simpl_add_to_nth;
      try rewrite IHn;
      reflexivity.
  Qed.

  Lemma length_add_to_nth i x xs : length (add_to_nth i x xs) = length xs.
  Proof. unfold add_to_nth; distr_length; reflexivity. Qed.

  Hint Rewrite @length_add_to_nth : distr_length.

  Lemma set_nth_sum : forall n x us, (n < length us \/ n >= length limb_widths)%nat ->
    BaseSystem.decode base (set_nth n x us) =
    (x - nth_default 0 us n) * nth_default 0 base n + BaseSystem.decode base us.
  Proof. intros; unfold set_nth; rewrite update_nth_sum by assumption; reflexivity. Qed.

  Lemma add_to_nth_sum : forall n x us, (n < length us \/ n >= length limb_widths)%nat ->
    BaseSystem.decode base (add_to_nth n x us) =
    x * nth_default 0 base n + BaseSystem.decode base us.
  Proof. intros; rewrite add_to_nth_set_nth, set_nth_sum; try ring_simplify; auto. Qed.

  Lemma add_to_nth_nth_default_full : forall n x l i d,
    nth_default d (add_to_nth n x l) i =
    if lt_dec i (length l) then
      if (eq_nat_dec i n) then x + nth_default d l i
      else nth_default d l i
    else d.
  Proof. intros; rewrite add_to_nth_update_nth; apply update_nth_nth_default_full; assumption. Qed.
  Hint Rewrite @add_to_nth_nth_default_full : push_nth_default.

  Lemma add_to_nth_nth_default : forall n x l i, (0 <= i < length l)%nat ->
    nth_default 0 (add_to_nth n x l) i =
    if (eq_nat_dec i n) then x + nth_default 0 l i else nth_default 0 l i.
  Proof. intros; rewrite add_to_nth_update_nth; apply update_nth_nth_default; assumption. Qed.
  Hint Rewrite @add_to_nth_nth_default using omega : push_nth_default.

  Lemma log_cap_nonneg : forall i, 0 <= log_cap i.
  Proof.
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
  Proof. intros; unfold carry_gen, carry_single; distr_length; reflexivity. Qed.

  Hint Rewrite @length_carry_gen : distr_length.

  Lemma length_carry_simple : forall i us, length (carry_simple limb_widths i us) = length us.
  Proof. intros; unfold carry_simple; distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_simple : distr_length.

  Lemma nth_default_base_succ : forall i, (S i < length limb_widths)%nat ->
    nth_default 0 base (S i) = 2 ^ log_cap i * nth_default 0 base i.
  Proof.
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
  Proof.
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
  Proof.
    unfold carry_simple; intros; rewrite carry_gen_decode_eq by assumption.
    autorewrite with natsimplify.
    break_match; try lia; autorewrite with zsimplify; lia.
  Qed.


  Lemma length_carry_simple_sequence : forall is us, length (carry_simple_sequence limb_widths is us) = length us.
  Proof.
    unfold carry_simple_sequence.
    induction is; [ reflexivity | simpl; intros ].
    distr_length.
    congruence.
  Qed.
  Hint Rewrite @length_carry_simple_sequence : distr_length.

  Lemma length_make_chain : forall i, length (make_chain i) = i.
  Proof. induction i; simpl; congruence. Qed.
  Hint Rewrite @length_make_chain : distr_length.

  Lemma length_full_carry_chain : length (full_carry_chain limb_widths) = length limb_widths.
  Proof. unfold full_carry_chain; distr_length; reflexivity. Qed.
  Hint Rewrite @length_full_carry_chain : distr_length.

  Lemma length_carry_simple_full us : length (carry_simple_full limb_widths us) = length us.
  Proof. unfold carry_simple_full; distr_length; reflexivity. Qed.
  Hint Rewrite @length_carry_simple_full : distr_length.

  (* TODO : move? *)
  Lemma make_chain_lt : forall x i : nat, In i (make_chain x) -> (i < x)%nat.
  Proof.
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
  Proof.
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
  Proof.
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
  Proof.
    intros; autorewrite with push_nth_default natsimplify; break_match; omega.
  Qed.
  Hint Rewrite @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.

  Lemma nth_default_carry_simple
    : forall i us,
      (0 <= i < length us)%nat
      -> nth_default 0 (carry_simple limb_widths i us) i
         = Z.pow2_mod (nth_default 0 us i) (log_cap i).
  Proof.
    intros; autorewrite with push_nth_default natsimplify; break_match; omega.
  Qed.
  Hint Rewrite @nth_default_carry_simple using (omega || distr_length; omega) : push_nth_default.
End carrying.

Hint Rewrite @length_carry_gen : distr_length.
Hint Rewrite @length_carry_simple @length_carry_simple_sequence @length_make_chain @length_full_carry_chain @length_carry_simple_full : distr_length.
Hint Rewrite @nth_default_carry_simple_full @nth_default_carry_gen_full : push_nth_default.
Hint Rewrite @nth_default_carry_simple @nth_default_carry_gen using (omega || distr_length; omega) : push_nth_default.
