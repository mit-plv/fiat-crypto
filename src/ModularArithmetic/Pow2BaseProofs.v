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

Hint Extern 1 => progress autorewrite with push_upper_bound in * : push_upper_bound.
Hint Extern 1 => progress autorewrite with pull_upper_bound in * : pull_upper_bound.

(* TODO : move to ZUtil *)
  Lemma ones_spec : forall n m, 0 <= n -> 0 <= m -> Z.testbit (Z.ones n) m = if Z_lt_dec m n then true else false.
  Proof.
    intros.
    break_if.
    + apply Z.ones_spec_low. omega.
    + apply Z.ones_spec_high. omega.
  Qed.

(* TODO : move to ZUtil *)
  Create HintDb Ztestbit discriminated.
Hint Rewrite Z.testbit_0_l : Ztestbit.
Hint Rewrite Z.land_spec Z.lor_spec Z.shiftl_spec Z.shiftr_spec ones_spec using omega : Ztestbit.
Hint Rewrite Z.testbit_neg_r using omega : Ztestbit.
Hint Rewrite Bool.andb_true_r Bool.andb_false_r Bool.orb_true_r Bool.orb_false_r
            Bool.andb_true_l Bool.andb_false_l Bool.orb_true_l Bool.orb_false_l : Ztestbit.

(* TODO : move *)
Lemma testbit_pow2_mod : forall a n i, 0 <= i ->  0 <= n ->
Z.testbit (Z.pow2_mod a n) i = if Z_lt_dec i n then Z.testbit a i else false.
Proof.
cbv [Z.pow2_mod]; intros.
repeat match goal with
        | |- _ => break_if
        | |- _ => omega
        | |- _ => reflexivity
        | |- _ => progress autorewrite with Ztestbit
        end.
Qed.
Hint Rewrite testbit_pow2_mod using omega : Ztestbit.

Section Pow2BaseProofs.
  Context {limb_widths} (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma base_from_limb_widths_length : length base = length limb_widths.
  Proof.
    clear limb_widths_nonneg.
    induction limb_widths; [ reflexivity | simpl in * ].
    autorewrite with distr_length; auto.
  Qed.
  Hint Rewrite base_from_limb_widths_length : distr_length.

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

  Lemma base_from_limb_widths_cons : forall l0 l,
    base_from_limb_widths (l0 :: l) = 1 :: map (Z.mul (two_p l0)) (base_from_limb_widths l).
  Proof.
    reflexivity.
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

  (* TODO : move *)
  Lemma pow2_mod_split : forall a n m, 0 <= n -> 0 <= m ->
                                       Z.pow2_mod a (n + m) = Z.lor (Z.pow2_mod a n) ((Z.pow2_mod (a >> n) m) << n).
  Proof.
    intros; cbv [Z.pow2_mod].
    apply Z.bits_inj'; intros.
    repeat progress (try break_if; autorewrite with Ztestbit zsimplify; try reflexivity).
    try match goal with H : ?a < ?b |- appcontext[Z.testbit _ (?a - ?b)] =>
      rewrite !Z.testbit_neg_r with (n := a - b) by omega end.
    autorewrite with Ztestbit; reflexivity.
  Qed.


  (* TODO : move *)
  Lemma pow2_mod_pow2_mod : forall a n m, 0 <= n -> 0 <= m ->
                                          Z.pow2_mod (Z.pow2_mod a n) m = Z.pow2_mod a (Z.min n m).
  Proof.
    intros; cbv [Z.pow2_mod].
    apply Z.bits_inj'; intros.
    apply Z.min_case_strong; intros; repeat progress (try break_if; autorewrite with Ztestbit zsimplify; try reflexivity).
  Qed.

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


  (* TODO : move *)
  Lemma pow2_mod_add_shiftl_low : forall a b n m, m <= n -> Z.pow2_mod (a + b << n) m = Z.pow2_mod a m.
  Proof.
    clear limb_widths limb_widths_nonneg.
  Admitted.

  (* TODO : move *)
  Lemma pow2_mod_subst : forall a n m, n <= m -> Z.pow2_mod a n = a -> Z.pow2_mod a m = Z.pow2_mod a n.
  Proof.
    clear limb_widths limb_widths_nonneg.
  Admitted.

  (* TODO : move *)
  Lemma pow2_mod_0_r : forall a, Z.pow2_mod a 0 = 0.
  Proof.
    clear limb_widths limb_widths_nonneg. intros.
    rewrite Z.pow2_mod_spec, Z.mod_1_r; reflexivity.
  Qed.

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
          rewrite pow2_mod_add_shiftl_low by omega.
          rewrite bounded_iff in *.
          specialize (H 0%nat); rewrite !nth_default_cons in H.
          rewrite Z.pow2_mod_spec, Z.mod_small; try omega; auto using in_eq.
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
           | |- _ => rewrite firstn_0, sum_firstn_0, decode_nil, pow2_mod_0_r; reflexivity
           | |- _ => progress distr_length
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
           | |- _ => rewrite testbit_pow2_mod by (omega || trivial)
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
           | |- _ => rewrite testbit_pow2_mod
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
     rewrite testbit_pow2_mod by omega; break_if; auto.
    }
    rewrite H1.
    rewrite Z.pow2_mod_spec; try apply Z.mod_pos_bound; zero_bounds.
  Qed.

  Lemma decode_upper_bound : forall us,
    length us = length limb_widths ->
    bounded limb_widths us ->
    BaseSystem.decode base us < upper_bound limb_widths.
  Proof.
    cbv [upper_bound]; intros.
    apply testbit_false_bound; auto; intros.
    rewrite testbit_decode_high; auto;
      replace (length us) with (length limb_widths); try omega.
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
           | |- _ => rewrite testbit_pow2_mod
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
           | |- _ => erewrite <-pow2_mod_bounded by eauto; rewrite testbit_pow2_mod
           end.
  Qed.

  Lemma decode_shift : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << nth_default 0 limb_widths 0).
  Proof.
    induction limb_widths; intros;
      repeat match goal with
             | |- _ => rewrite base_from_limb_widths_cons, peel_decode
             | |- _ => rewrite two_p_correct, Z.shiftl_mul_pow2
             | |- _ => apply Z.add_cancel_l
             | |- appcontext[tl (_ :: _)] => cbv [tl]
             | |- appcontext[map (Z.mul ?a) _] => fold (BaseSystem.mul_each a);
                                                    rewrite <-!mul_each_base, !mul_each_rep
             | |- _ => progress distr_length
             | |- _ => progress autorewrite with push_nth_default zsimplify
             | |- _ => solve [auto using in_eq, Z.mul_comm]
            end.
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
Hint Rewrite @base_from_limb_widths_length : distr_length.
Hint Rewrite @upper_bound_nil @upper_bound_cons @upper_bound_app using solve [ eauto with znonzero ] : push_upper_bound.
Hint Rewrite <- @upper_bound_cons @upper_bound_app using solve [ eauto with znonzero ] : pull_upper_bound.

Section BitwiseDecodeEncode.
  Context {limb_widths} (bv : BaseSystem.BaseVector (base_from_limb_widths limb_widths))
          (limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w).
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
    rewrite BaseSystemProofs.encode'_spec; unfold Pow2Base.upper_bound; try zero_bounds;
      auto using sum_firstn_limb_widths_nonneg.
    rewrite nth_default_out_of_bounds by omega.
    reflexivity.
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

  Lemma sum_firstn_uniform_base : forall i, (i <= length limb_widths)%nat ->
                                            sum_firstn limb_widths i = Z.of_nat i * width.
  Admitted.

  Lemma sum_firstn_uniform_base_strong : forall i, (length limb_widths <= i)%nat ->
                                            sum_firstn limb_widths i = Z.of_nat (length limb_widths) * width.
  Admitted.

  (* TODO : move *)
  Lemma decode_truncate_base : forall bs us, BaseSystem.decode bs us = BaseSystem.decode (firstn (length us) bs) us.
  Admitted.

  (* TODO : move *)
  Lemma firstn_map : forall {A B} n (f : A -> B) ls, firstn n (map f ls) = map f (firstn n ls).
  Proof.
    induction n; destruct ls; boring.
  Qed.

  (* TODO : move *)
  Lemma firstn_base_from_limb_widths : forall n lw,
      firstn n (base_from_limb_widths lw) = base_from_limb_widths (firstn n lw).
  Proof.
    induction n; destruct lw; boring.
    f_equal.
    rewrite <-IHn, firstn_map.
    reflexivity.
  Qed.

  (* TODO : move *)
  Lemma tl_repeat : forall {A} xs n (x : A), (forall y, In y xs -> y = x) ->
                                             (n < length xs)%nat ->
                                             firstn n xs = firstn n (tl xs).
  Proof.
    induction xs; destruct n; try solve [boring]; intros.
    rewrite firstn_cons_S.
    erewrite IHxs by (eauto using in_cons; distr_length).
    destruct xs; distr_length.
    cbv [tl].
    rewrite firstn_cons_S.
    f_equal.
    transitivity x; [|symmetry]; eauto using in_eq, in_cons.
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

  Lemma decode_shift_uniform : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode base us) << width).
  Proof.
    intros.
    rewrite decode_tl_base with (us := us) by distr_length.
    rewrite decode_shift; auto using uniform_limb_widths_nonneg.
    destruct limb_widths; try congruence;
      repeat match goal with
             | |- _ => rewrite base_from_limb_widths_cons
             | |- _ => rewrite two_p_correct, Z.shiftl_mul_pow2
             | |- _ => apply Z.add_cancel_l
             | |- appcontext[tl (_ :: _)] => cbv [tl]
             | |- appcontext[map (Z.mul ?a) _] => fold (BaseSystem.mul_each a);
                                                    rewrite <-!mul_each_base, !mul_each_rep
             | |- _ => progress distr_length
             | |- _ => progress autorewrite with push_nth_default zsimplify
             | |- _ => solve [auto using in_eq, Z.mul_comm]
            end.
    f_equal; eauto using in_eq.
  Qed.

End UniformBase.

Section TestbitDecode.
  Local Notation "u # i" := (nth_default 0 u i) (at level 30).

  (* splits a bit index into a digit index and an index within the digit*)
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

  Lemma snd_split_index'_nonneg : forall i index lw, (0 <= i) ->
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
    pose proof (snd_split_index'_nonneg n 0 limb_widths).
    specialize_by assumption.
    repeat match goal with
           | |- _ => progress autorewrite with Ztestbit natsimplify in *
           | |- _ => erewrite digit_select by eassumption
           | |- _ => break_if
           | |- _ => rewrite testbit_pow2_mod by auto using nth_default_limb_widths_nonneg
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

End TestbitDecode.

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
    break_match; lia.
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
