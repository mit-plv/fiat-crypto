Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Coq.funind.Recdef.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.LegacyArithmetic.VerdiTactics.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.LegacyArithmetic.Pow2Base.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.Bool.
Require Export Crypto.Util.FixCoqMistakes.
Local Open Scope Z_scope.

Require Crypto.LegacyArithmetic.BaseSystemProofs.

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

  Lemma base_from_limb_widths_step : forall i b w, (S i < length limb_widths)%nat ->
    nth_error base i = Some b ->
    nth_error limb_widths i = Some w ->
    nth_error base (S i) = Some (two_p w * b).
  Proof using Type.
    clear limb_widths_nonneg. (* don't use this in the inductive hypothesis *)
    induction limb_widths; intros i b w ? nth_err_w nth_err_b;
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
    induction i as [|i IHi]; intros H.
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
    cbv [bounded]; intros lw us i H H0.
    repeat match goal with
           | |- _ => progress (cbv [bounded]; intros)
           | |- _ => break_if
           | |- _ => apply Z.bits_inj'
           | |- _ => rewrite Z.testbit_pow2_mod by (apply nth_default_preserves_properties; auto; omega)
           | |- _ => reflexivity
           end.
    specialize (H0 i).
    symmetry.
    let n := match goal with n : Z |- _ => n end in
    rewrite <- (Z.mod_pow2_bits_high (nth_default 0 us i) (nth_default 0 lw i) n);
      [ rewrite Z.mod_small by omega; reflexivity | ].
    split; try omega.
    apply nth_default_preserves_properties; auto; omega.
  Qed.

  Lemma bounded_nil_iff : forall us, bounded nil us <-> (forall u, In u us -> u = 0).
  Proof using Type.
    clear.
    intros us; split; cbv [bounded]; [ intros H u H0 | intros H i ].
    + edestruct (In_nth_error_value us u) as [x]; try assumption.
      specialize (H x).
      replace u with (nth_default 0 us x) by (auto using nth_error_value_eq_nth_default).
      rewrite nth_default_nil, Z.pow_0_r in H.
      omega.
    + rewrite nth_default_nil, Z.pow_0_r.
      apply nth_default_preserves_properties; try omega.
      intros x H0.
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
    intro us; revert limb_widths limb_widths_nonneg; induction us as [|a us IHus];
      intros limb_widths limb_widths_nonneg i H.
    + rewrite nth_default_nil, BaseSystemProofs.decode_nil, Z.shiftr_0_l, Z.pow2_mod_spec, Z.mod_0_l by
          (try (apply Z.pow_nonzero; try omega); apply nth_default_preserves_properties; auto; omega).
      reflexivity.
    + destruct i.
      - rewrite nth_default_cons, sum_firstn_0, Z.shiftr_0_r.
        destruct limb_widths as [|w lw].
        * cbv [base_from_limb_widths].
          rewrite <-pow2_mod_bounded with (lw := nil); rewrite bounded_nil_iff in *; auto using in_cons;
            try solve [intros; exfalso; eauto using in_nil].
          rewrite !nth_default_nil, BaseSystemProofs.decode_base_nil; auto.
          cbv. auto using in_eq.
        * rewrite nth_default_cons, base_from_limb_widths_cons, BaseSystemProofs.peel_decode.
          fold (BaseSystem.mul_each (two_p w)).
          rewrite <-BaseSystemProofs.mul_each_base, BaseSystemProofs.mul_each_rep.
          rewrite two_p_correct, (Z.mul_comm (2 ^ w)).
          rewrite <-Z.shiftl_mul_pow2 by auto using in_eq.
          rewrite bounded_iff in *.
          specialize (H 0%nat); rewrite !nth_default_cons in H.
          rewrite <-Z.lor_shiftl by (auto using in_eq; omega).
          apply Z.bits_inj'; intros n H0.
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
          rewrite sum_firstn_nil, !nth_default_nil, BaseSystemProofs.decode_base_nil, Z.shiftr_0_r.
          apply nth_default_preserves_properties; intros; auto using in_cons.
          f_equal; auto using in_cons.
        * rewrite sum_firstn_succ_cons, nth_default_cons_S, base_from_limb_widths_cons, BaseSystemProofs.peel_decode.
          fold (BaseSystem.mul_each (two_p w)).
          rewrite <-BaseSystemProofs.mul_each_base, BaseSystemProofs.mul_each_rep.
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

  Lemma decode_firstn_pow2_mod : forall us i,
    (i <= length us)%nat ->
    length us = length limb_widths ->
    bounded limb_widths us ->
    BaseSystem.decode' base (firstn i us) = Z.pow2_mod (BaseSystem.decode' base us) (sum_firstn limb_widths i).
  Proof using Type*.
    intros us i H H0 H1; induction i;
    repeat match goal with
           | |- _ => rewrite sum_firstn_0, BaseSystemProofs.decode_nil, Z.pow2_mod_0_r; reflexivity
           | |- _ => progress distr_length
           | |- _ => progress autorewrite with simpl_firstn
           | |- _ => rewrite firstn_succ with (d := 0)
           | |- _ => rewrite BaseSystemProofs.set_higher
           | |- _ => rewrite nth_default_base
           | |- _ => rewrite IHi
           | |- _ => rewrite <-Z.lor_shiftl by (rewrite ?Z.pow2_mod_spec; try apply Z.mod_pos_bound; zero_bounds)
           | |- context[min ?x ?y] => (rewrite Nat.min_l by omega || rewrite Nat.min_r by omega)
           | |- context[2 ^ ?a * _] => rewrite (Z.mul_comm (2 ^ a)); rewrite <-Z.shiftl_mul_pow2
           | |- _ => solve [auto]
           | |- _ => lia
           end.
    rewrite digit_select by assumption; apply Z.bits_inj'.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress autorewrite with Ztestbit
           | |- _ => rewrite Z.testbit_pow2_mod by (omega || trivial)
           | |- _ => break_if; try omega
           | H : ?a < ?b |- context[Z.testbit _ (?a - ?b)] =>
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
    intros us n H H0 H1.
    erewrite <-(firstn_all _ us) by reflexivity.
    auto using testbit_decode_firstn_high.
  Qed.

  (** TODO: Figure out how to automate and clean up this proof *)
  Lemma decode_nonneg : forall us,
    length us = length limb_widths ->
    bounded limb_widths us ->
    0 <= BaseSystem.decode base us.
  Proof using Type*.
    intros us H H0.
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
    cbv [upper_bound]; intros us H H0.
    split.
    { apply decode_nonneg; auto. }
    { apply Z.testbit_false_bound; auto; intros.
      rewrite testbit_decode_high; auto;
        replace (length us) with (length limb_widths); try omega. }
  Qed.

  Lemma decode_shift_app : forall us0 us1, (length (us0 ++ us1) <= length limb_widths)%nat ->
    BaseSystem.decode base (us0 ++ us1) = (BaseSystem.decode (base_from_limb_widths (firstn (length us0) limb_widths)) us0) + ((BaseSystem.decode (base_from_limb_widths (skipn (length us0) limb_widths)) us1) << sum_firstn limb_widths (length us0)).
  Proof using Type*.
    unfold BaseSystem.decode; intros us0 us1 ?.
    assert (0 <= sum_firstn limb_widths (length us0)) by auto using sum_firstn_nonnegative.
    rewrite BaseSystemProofs.decode'_splice; autorewrite with push_firstn.
    apply Z.add_cancel_l.
    autorewrite with pull_base_from_limb_widths Zshift_to_pow zsimplify.
    rewrite BaseSystemProofs.decode'_map_mul, two_p_correct; nia.
  Qed.

  Lemma decode_shift : forall us u0, (length (u0 :: us) <= length limb_widths)%nat ->
    BaseSystem.decode base (u0 :: us) = u0 + ((BaseSystem.decode (base_from_limb_widths (tl limb_widths)) us) << (nth_default 0 limb_widths 0)).
  Proof using Type*.
    intros us u0 H; etransitivity; [ apply (decode_shift_app (u0::nil)); assumption | ].
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

Section UniformBase.
  Context {width : Z} (limb_width_nonneg : 0 <= width).
  Context (limb_widths : list Z)
    (limb_widths_uniform : forall w, In w limb_widths -> w = width).
  Local Notation base := (base_from_limb_widths limb_widths).

   Lemma bounded_uniform : forall us, (length us <= length limb_widths)%nat ->
     (bounded limb_widths us <-> (forall u, In u us -> 0 <= u < 2 ^ width)).
   Proof using Type*.
     cbv [bounded]; intros us H; split; intro A; [ intros u H0 | intros i ].
     + let G := fresh "G" in
       match goal with H : In _ us |- _ =>
         eapply In_nth in H; destruct H as [x G]; destruct G as [? G];
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
    intros w H.
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
    induction us as [|a us IHus]; intros bs.
    + rewrite !BaseSystemProofs.decode_nil; reflexivity.
    + distr_length.
      destruct bs.
      - rewrite firstn_nil, !BaseSystemProofs.decode_base_nil; reflexivity.
      - rewrite firstn_cons, !BaseSystemProofs.peel_decode.
        f_equal.
        apply IHus.
  Qed.

  (* TODO : move *)
  Lemma tl_repeat : forall {A} xs n (x : A), (forall y, In y xs -> y = x) ->
                                             (n < length xs)%nat ->
                                             firstn n xs = firstn n (tl xs).
  Proof using Type.
    intros A xs n x H H0.
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
End UniformBase.
