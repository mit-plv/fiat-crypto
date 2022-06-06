Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import Crypto.Arithmetic.UniformWeight.
Require Crypto.PushButtonSynthesis.SaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Crypto.Stringification.C.
Require Crypto.Stringification.Go.
Require Crypto.Stringification.Java.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.ZUtil.ModInv.

Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Coq.ZArith.Znat.

Require Import Crypto.Util.Notations.
Local Open Scope string_scope.
Local Open Scope list_scope.
Import ListNotations. Local Open Scope Z_scope.

Import
  AbstractInterpretation.Compilers
  Language.Compilers
  Language.API.Compilers.

Import Language.API.Compilers.API.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Local Existing Instance default_low_level_rewriter_method.
Local Existing Instance AbstractInterpretation.default_Options.
Local Instance : unfold_value_barrier_opt := true.
Local Instance : assembly_hints_lines_opt := None.
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.

Local Existing Instance default_output_options.

Module solinas_reduction.

  Import Crypto.Arithmetic.Saturated.

  Section __.

    Print weight_properties.

    Context (machine_wordsize := 64)
            (weight := uweight machine_wordsize)
            {wprops : @weight_properties weight}.

    Definition sat_reduce base s c n (p : list (Z * Z)) :=
      let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
      let lo_hi := Associational.split s' p in
      let coef := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let hi := Saturated.Associational.sat_mul_const base coef (snd lo_hi) in
      let r := (fst lo_hi) ++ hi in
      r.

    Hint Rewrite eval_app : push_eval.
    Hint Rewrite Saturated.Associational.eval_sat_mul : push_eval.
    Hint Rewrite Saturated.Associational.eval_sat_mul_const using (lia || assumption) : push_eval.
    Hint Rewrite eval_split using solve [auto] : push_eval.

    Lemma value_sat_reduce base s c n (p : list (Z * Z)) (basenz:base<>0):
      let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
      let coef := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let lo_hi := Associational.split s' p in
      Associational.eval (sat_reduce base s c n p) =
        Associational.eval coef * Associational.eval (snd lo_hi) + Associational.eval (fst lo_hi).
    Proof.
      intros; cbv [sat_reduce] in *; cbv [s' lo_hi coef].
      autorewrite with push_eval; lia.
    Qed.

    Lemma adjust_s_invariant fuel s (s_nz:s<>0) :
      fst (Saturated.Rows.adjust_s weight fuel s) mod s = 0
      /\ fst (Saturated.Rows.adjust_s weight fuel s) <> 0.
    Proof using wprops.
      cbv [Saturated.Rows.adjust_s]; rewrite fold_right_map; generalize (List.rev (seq 0 fuel)); intro ls; induction ls as [|l ls IHls];
        cbn.
      { rewrite Z.mod_same by assumption; auto. }
      { break_match; cbn in *; auto with zarith. }
    Qed.

    Lemma eval_sat_reduce base s c n p :
      base <> 0
      -> s - Associational.eval c <> 0
      -> s <> 0
      -> Associational.eval (sat_reduce base s c n p) mod (s - Associational.eval c)
        = Associational.eval p mod (s - Associational.eval c).
    Proof using wprops.
      intros; cbv [sat_reduce].
      lazymatch goal with
      | |- context[Saturated.Rows.adjust_s ?weight ?fuel ?s] =>
          destruct (adjust_s_invariant fuel s ltac:(assumption)) as [Hmod ?]
      end.
      eta_expand; autorewrite with push_eval zsimplify_const; cbn [fst snd].
      rewrite <- (Z.mul_comm (Associational.eval c)), <- !Z.mul_assoc, <-Associational.reduction_rule by auto.
      autorewrite with zsimplify_const; rewrite !Z.mul_assoc, Z.mul_div_eq_full, Hmod by auto.
      autorewrite with zsimplify_const push_eval; trivial.
    Qed.
    Hint Rewrite eval_sat_reduce using auto : push_eval.

    (* n is input width *)
    Definition reduce1 base s c n m (p : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let r_a := sat_reduce base s c n p_a in
      let r_rows := Saturated.Rows.from_associational weight n r_a in
      let r_flat := Saturated.Rows.flatten weight m r_rows in
      fst r_flat.

    Definition reduce base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) (S n) p in
      let r2 := reduce1 base s c (S n) (S n) (r1) in
      let r3 := reduce1 base s c (S n) (n) (r2) in
      r3.

    Definition mul_no_reduce base n (p q : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      fst pq.

    Definition mulmod base s c n (p q : list Z) :=
      let prod := mul_no_reduce base n p q in
      let red := reduce base s c n prod in
      red.

    Definition canonical_repr n (p : list Z) : Prop :=
      length p = n /\
        p = Partition.partition weight n (Positional.eval weight n p).

    Hint Rewrite Saturated.Rows.eval_from_associational using auto : push_eval.

    Hint Resolve length_partition : push_length.
    Hint Resolve Rows.length_from_associational : push_length.

    Ltac weight_comp :=
      unfold weight, uweight, ModOps.weight;
      rewrite !Z.div_1_r;
      rewrite !Z.opp_involutive;
      try rewrite Nat2Z.inj_succ;
      try rewrite OrdersEx.Z_as_OT.mul_succ_r;
      try rewrite OrdersEx.Z_as_OT.pow_add_r;
      autorewrite with zsimplify_const;
      ring_simplify.

    Lemma canonical_pos n : forall (p : list Z),
        canonical_repr n p ->
        0 <= eval weight n p.
    Proof.
      intros.
      unfold canonical_repr in *.
      intuition.
      pose proof Partition.eval_partition.
      specialize (H weight wprops n (eval weight n p)).
      rewrite <-H1 in H.
      rewrite H.
      apply Z.mod_pos_bound.
      eauto.
    Qed.

    Lemma canonical_bounded n : forall (p : list Z),
        canonical_repr n p ->
        forall x, In x p -> 0 <= x < 2 ^ machine_wordsize.
    Proof.
      intros.
      pose proof (canonical_pos n p H).
      unfold canonical_repr, Partition.partition in H.
      destruct H.
      rewrite H2 in H0.
      rewrite in_map_iff in H0.
      destruct H0.
      intuition.
      { rewrite <-H3.
        apply Z.div_nonneg.
        apply Z_mod_nonneg_nonneg.
        assumption.
        eauto using Z.lt_le_incl.
        eauto using Z.lt_le_incl. }
      { rewrite <-H3.
        apply OrdersEx.Z_as_OT.div_lt_upper_bound; eauto.
        assert (weight (S x0) = weight x0 * 2 ^ machine_wordsize).
        { unfold weight, uweight, ModOps.weight.
          rewrite !Z.div_1_r.
          rewrite !Z.opp_involutive.
          rewrite Nat2Z.inj_succ.
          rewrite OrdersEx.Z_as_OT.mul_succ_r.
          rewrite OrdersEx.Z_as_OT.pow_add_r.
          reflexivity.
          lia.
          lia. }
        rewrite <-H0.
        apply OrdersEx.Z_as_OT.mod_pos_bound.
        eauto. }
    Qed.

    Lemma canonical_iff p n :
      canonical_repr n p <->
        length p = n /\
          forall x, In x p -> 0 <= x < 2 ^ machine_wordsize.
    Proof.
      split.
      { intros.
        intuition.
        unfold canonical_repr in *.
        intuition.
        eapply canonical_bounded; eauto.
        eapply canonical_bounded; eauto. }
      { intros.
        unfold canonical_repr.
        intuition.

        apply uweight_partition_unique.
        lia.
        assumption.
        intros.
        rewrite Le.Z.le_sub_1_iff.
        eauto. }
    Qed.

    Lemma canonical_cons n a p:
      canonical_repr (S n) (a :: p) ->
      canonical_repr n p.
    Proof.
      intros.
      rewrite canonical_iff in *.
      intuition; apply H1; simpl; eauto.
    Qed.

    Lemma canonical_app_l n n1 n2 l l1 l2 :
      canonical_repr n l ->
      length l1 = n1 ->
      length l2 = n2 ->
      n = (n1 + n2)%nat ->
      l = l1 ++ l2 ->
      canonical_repr n1 l1.
    Proof.
      intros.
      intuition;
        rewrite canonical_iff in *;
        intuition; apply H5; rewrite H3; apply in_or_app; eauto.
    Qed.

    Lemma canonical_app_r n n1 n2 l l1 l2 :
      canonical_repr n l ->
      length l1 = n1 ->
      length l2 = n2 ->
      n = (n1 + n2)%nat ->
      l = l1 ++ l2 ->
      canonical_repr n2 l2.
    Proof.
      intros.
      intuition;
        rewrite canonical_iff in *;
        intuition; apply H5; rewrite H3; apply in_or_app; eauto.
    Qed.

    (* helps with proving lemmas about the length of the reduction *)
    Ltac length_q q :=
      try match goal with
          | [ H : canonical_repr _ q |- _ ] =>
              unfold canonical_repr in H; intuition
          end;
      try match goal with
          | [ H : length q = _ |- _] =>
              rewrite !app_length in H;
              try rewrite !app_length;
              cbn [length] in H; cbn [length]; lia
          end;
      match goal with
      | [ H : q = _ |- _ ] =>
          apply f_equal with (f:=fun l => length l) in H;
          rewrite !app_length in H;
          try rewrite !app_length;
          cbn [length] in H; cbn [length]; lia
      end.

    Definition eval_weight_P p :=
      eval (fun i : nat => weight (S i)) (Datatypes.length p) p =
        (eval weight (Datatypes.length p) p) * weight 1.

    Lemma eval_weight_S' : forall p,
      eval_weight_P p.
    Proof.
      apply (ListAux.list_length_induction Z).
      intros.
      pose proof (@break_list_last Z l1).
      intuition; unfold eval_weight_P in *.
      { subst.
        reflexivity. }
      { destruct H1.
        destruct H0.
        subst.
        rewrite app_length.
        simpl.
        replace (length x + 1)%nat with (S (length x)) by lia.
        rewrite !eval_snoc_S.
        rewrite H.
        rewrite OrdersEx.Z_as_OT.mul_add_distr_r.
        rewrite OrdersEx.Z_as_DT.add_cancel_l.
        unfold weight, uweight, ModOps.weight, machine_wordsize.
        rewrite !Z.div_1_r.
        rewrite !Z.opp_involutive.
        rewrite Nat2Z.inj_succ.
        rewrite OrdersEx.Z_as_OT.mul_succ_r.
        rewrite OrdersEx.Z_as_OT.pow_add_r.
        lia.
        lia.
        lia.
        rewrite app_length.
        simpl.
        lia.
        lia.
        lia. }
    Qed.

    Lemma eval_weight_S p n:
      n = Datatypes.length p ->
      eval (fun i : nat => weight (S i)) n p =
        (eval weight n p) * weight 1.
    Proof.
      pose proof eval_weight_S'.
      unfold eval_weight_P in *.
      intros.
      subst.
      eauto.
    Qed.

    Lemma canonical_eval_bounded n : forall (p : list Z),
        canonical_repr n p ->
        eval weight n p < weight n.
    Proof.
      intros.
      pose proof (canonical_bounded _ _ H).
      assert (Hcanon: canonical_repr n p) by assumption.
      unfold canonical_repr in H; intuition.
      generalize dependent n.
      induction p; intros.
      { simpl in H1; subst.
        vm_compute.
        eauto. }
      { simpl in H1; subst.
        rewrite eval_cons.
        autorewrite with zsimplify_const.
        rewrite eval_weight_S.
        assert (a + eval weight (Datatypes.length p) p * weight 1 < 2^machine_wordsize + eval weight (Datatypes.length p) p * weight 1).
        rewrite <-OrdersEx.Z_as_OT.add_lt_mono_r.
        apply H0.
        simpl.
        left.
        reflexivity.
        rewrite <-Le.Z.le_sub_1_iff.
        rewrite <-Le.Z.le_sub_1_iff in H.
        etransitivity.
        apply H.
        assert (2 ^ machine_wordsize + eval weight (Datatypes.length p) p * weight 1 <= 2 ^ machine_wordsize + (weight (Datatypes.length p) - 1) * weight 1).
        rewrite <-OrdersEx.Z_as_OT.add_le_mono_l.
        rewrite <-OrdersEx.Z_as_OT.mul_le_mono_pos_r.
        rewrite Le.Z.le_sub_1_iff.
        apply IHp.
        intros.
        apply H0.
        simpl.
        eauto.
        eapply canonical_cons; eauto.
        reflexivity.
        apply canonical_cons in Hcanon.
        unfold canonical_repr in Hcanon.
        intuition.
        apply wprops.
        rewrite OrdersEx.Z_as_OT.sub_le_mono_r with (p:=1) in H1.
        etransitivity.
        apply H1.
        weight_comp.
        rewrite <-OrdersEx.Z_as_OT.sub_le_mono_r.
        rewrite Nat2Z.inj_succ.
        rewrite OrdersEx.Z_as_OT.mul_succ_r.
        rewrite OrdersEx.Z_as_OT.pow_add_r.
        ring_simplify.
        reflexivity.
        lia.
        lia.
        lia.
        lia.
        reflexivity.
        reflexivity. }
    Qed.

    Lemma reduce_canonical_repr base s c n m : forall (p : list Z),
        canonical_repr m (reduce1 base s c n m p).
    Proof using wprops.
      intros.
      unfold reduce1 in *.
      unfold canonical_repr.
      rewrite Saturated.Rows.flatten_correct; auto.
      { intuition.
        { cbn [fst].
          auto with push_length. }
        { simpl.
          rewrite Partition.eval_partition; auto.
          f_equal.
          admit. }
      }
      { admit. }
    Admitted.

    Lemma split_lt w l1 l2:
      (forall x, In x l1 -> 0 < x < w) ->
      length l1 = length l2 ->
      split w (combine l1 l2) = (combine l1 l2, []).
    Proof.
      intros.
      generalize dependent l2.
      induction l1; intros.
      { reflexivity. }
      { simpl.
        destruct l2 eqn:E.
        simpl in H0.
        discriminate.
        match goal with
        | [ |- context[ ?x :: ?y ] ] => replace (x :: y) with ([x] ++ y) by eauto
        end.
        rewrite split_app.
        rewrite IHl1.
        cbn [fst snd].
        simpl.
        assert (In a (a :: l1)) by apply in_eq.
        apply H in H1.
        assert (a mod w = a).
        { apply Z.mod_small.
          lia. }
        rewrite H2.
        destruct (a =? 0) eqn:E1.
        rewrite Z.eqb_eq in E1.
        lia.
        reflexivity.
        intros.
        apply H.
        apply in_cons.
        assumption.
        simpl in H0.
        lia. }
    Qed.

    Lemma weight_mono' x :
      weight x < weight (S x).
    Proof.
      intros.
      unfold weight, uweight, ModOps.weight, machine_wordsize.
      rewrite !Z.div_1_r.
      rewrite !Z.opp_involutive.
      rewrite Nat2Z.inj_succ.
      rewrite OrdersEx.Z_as_OT.mul_succ_r.
      rewrite OrdersEx.Z_as_OT.pow_add_r.
      lia.
      lia.
      lia.
    Qed.

    Lemma weight_mono'' x1 x2 :
      (x2 > 0)%nat
      -> weight x1 < weight (x2 + x1).
    Proof.
      intros.
      induction H.
      { apply weight_mono'. }
      { etransitivity.
        apply IHle.
        apply weight_mono'. }
    Qed.

    Lemma weight_mono x1 x2 :
      (x1 < x2)%nat ->
      weight x1 < weight x2.
    Proof.
      intros.
      replace x2%nat with ((x2 - x1) + x1)%nat.
      apply weight_mono''.
      lia.
      lia.
    Qed.

    Context (base : Z)
            (s : Z)
            (c : list (Z * Z))
            (n : nat).

    Context (s_nz : s <> 0)
            (n_gt_1 : n > 1)
            (s_pos : s > 0)
            (c_pos : Associational.eval c > 0)
            (base_nz : base <> 0)
            (solinas_property : Rows.adjust_s weight (S (S (S n))) s = (weight n, true))
            (coef_small : weight n / s * Associational.eval c <= 2^(machine_wordsize/2)).

    Lemma value_reduce_second (* base s c n (s_nz:s<>0) *) : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        (canonical_repr (S n) p /\ hi <= 39) ->
        let q := reduce1 base s c (S n) (S n) p in
        let s' := fst (Saturated.Rows.adjust_s weight (S (S (S n))) s) in
        let coef := Associational.sat_mul_const base [(1, s'/s)] c in
        canonical_repr (S n) q ->
        eval weight (S n) q = Associational.eval coef * hi + eval weight n lo.
    Proof.
      intros.
      intuition.
      assert (Hcanon : canonical_repr (S n) p) by assumption.
      apply OrdersEx.Z_as_OT.le_trans with (p:=2^machine_wordsize) in coef_small.
      2: unfold machine_wordsize; simpl; lia.
      cbv [reduce1 canonical_repr] in H1, H2, q; intuition.
      cbv [q coef s'].
      rewrite !H.
      rewrite Rows.flatten_mod.
      rewrite Rows.eval_from_associational.
      rewrite value_sat_reduce.
      lazymatch goal with
        | |- context[Saturated.Rows.adjust_s ?weight ?fuel ?s] =>
            destruct (adjust_s_invariant fuel s ltac:(assumption)) as [Hmod ?]
      end.

      unfold to_associational.
      rewrite seq_snoc.
      rewrite map_app.
      rewrite Nat.add_0_l; cbn [map].
      rewrite combine_snoc.
      rewrite fst_split_app, snd_split_app.
      autorewrite with push_eval.
      pose proof solinas_property.
      rewrite H6 in *; cbn [fst] in *.
      assert (split (weight n) [(weight n, hi)] = ([], [(1, hi)])).
      { unfold split.
        simpl.
        assert (weight n mod weight n = 0) by (apply Z_mod_same_full).
        rewrite H7.
        simpl.
        assert (weight n / weight n = 1) by
          eauto using Z_div_same, Z.lt_gt, weight_positive.
        rewrite H8.
        reflexivity. }
      rewrite H7; cbn [fst snd].
      autorewrite with push_eval zsimplify_const; cbn [fst snd].
      assert (split (weight n) (combine (map weight (seq 0 n)) lo) =
                ((combine (map weight (seq 0 n)) lo), [])).
      { apply split_lt.
        intros.
        rewrite in_map_iff in H8.
        destruct H8.
        intuition.
        rewrite <-H9.
        apply wprops.
        rewrite <-H9.
        rewrite in_seq in H10.
        intuition.
        simpl in H11.
        apply weight_mono.
        lia.
        rewrite map_length.
        rewrite seq_length.
        length_q p. }
      rewrite H8; cbn [fst snd].
      autorewrite with push_eval zsimplify_const; cbn [fst snd].
      unfold eval, to_associational.
      apply Z.mod_small.
      pose proof BYInv.eval_bound.
      assert (0 < machine_wordsize) by lia.
      apply H9 with (n:=n) (f:=lo) in H10.
      unfold eval, to_associational in H10.
      unfold weight.
      intuition.

      etransitivity.
      assert (0 <= uweight machine_wordsize n / s * Associational.eval c * hi).
      { apply OrdersEx.Z_as_OT.mul_nonneg_nonneg.
        apply OrdersEx.Z_as_OT.mul_nonneg_nonneg.
        apply OrdersEx.Z_as_DT.div_pos.
        replace (uweight machine_wordsize n) with (weight n) by reflexivity.
        apply OrdersEx.Z_as_OT.lt_le_incl.
        apply wprops.
        lia.
        lia.
        rewrite canonical_iff in Hcanon.
        intuition.
        apply H13.
        rewrite H.
        apply in_or_app.
        right.
        simpl.
        eauto. }
      eassumption.
      replace (uweight machine_wordsize n / s * Associational.eval c * hi) with (uweight machine_wordsize n / s * Associational.eval c * hi + 0) at 1 by lia.
      rewrite <-OrdersEx.Z_as_OT.add_le_mono_l.
      pose proof (canonical_pos _ _ Hcanon).
      unfold eval, to_associational in H10.
      assumption.
      apply Zplus_lt_compat_l with
        (p:=uweight machine_wordsize n / s * Associational.eval c * hi) in H12.
      etransitivity.
      eauto.

      rewrite <-Le.Z.le_sub_1_iff.
      etransitivity.
      unfold weight in coef_small.
      apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_r with (p:=hi) in coef_small.
      rewrite OrdersEx.Z_as_OT.add_le_mono_r with (p:=2 ^ (machine_wordsize * Z.of_nat n)) in coef_small.
      apply coef_small.
      apply canonical_bounded with (x:=hi) in Hcanon.
      apply Hcanon.
      rewrite H.
      apply in_or_app.
      right.
      simpl.
      eauto.

      etransitivity.
      assert (2^machine_wordsize <= 2^(machine_wordsize * n)).
      apply OrdersEx.Z_as_OT.pow_le_mono_r.
      lia.
      lia.
      apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_r with (p:=hi) in H10.
      rewrite OrdersEx.Z_as_OT.add_le_mono_r with (p:=2 ^ (machine_wordsize * Z.of_nat n)) in H10.
      apply H10.
      apply canonical_bounded with (x:=hi) in Hcanon.
      apply Hcanon.
      rewrite H.
      apply in_or_app; right; simpl; eauto.

      etransitivity.
      apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l with (p:=(2 ^ (machine_wordsize * Z.of_nat n))) in H3.
      rewrite OrdersEx.Z_as_OT.add_le_mono_r with (p:=2 ^ (machine_wordsize * Z.of_nat n)) in H3.
      apply H3.
      lia.
      weight_comp.
      rewrite Z.mul_comm.
      rewrite Le.Z.le_sub_1_iff.
      cbv [machine_wordsize].
      lia.
      lia.
      lia.

      (* proving statements generated by apply lemmas *)
      intros.
      apply canonical_bounded with (p:=p) (n:=S n).
      unfold canonical_repr; intuition.
      rewrite H.
      apply in_or_app; intuition.
      apply f_equal with (f:=fun l => length l) in H.
      rewrite app_length in H.
      simpl in H.
      rewrite H1 in H.
      lia.
      rewrite map_length.
      rewrite seq_length.
      apply f_equal with (f:=fun l => length l) in H.
      rewrite app_length in H.
      simpl in H.
      rewrite H1 in H.
      lia.
      eauto.
      eauto.
      left; lia.
      eauto.
      intros.
      eapply Rows.length_from_associational; eauto.
    Qed.

    Theorem reduce_second' : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        (canonical_repr (S n) p /\ hi <= 39) ->
        forall q_lo q_hi1 q_hi2,
          let q := reduce1 base s c (S n) (S n) p in
          q = q_lo ++ [q_hi1] ++ [q_hi2] ->
          canonical_repr (S n) q ->
          ((q_hi2 = 1 /\ q_hi1 = 0) \/
             (q_hi2 = 0)).
    Proof using base base_nz c c_pos coef_small machine_wordsize n n_gt_1 s s_nz s_pos solinas_property weight wprops.
      intros.

      pose proof
           (value_reduce_second p lo hi H H0 H2).
      assert (coef_small2: weight n / s * Associational.eval c <= 2^machine_wordsize).
      { eapply OrdersEx.Z_as_OT.le_trans.
        eauto.
        unfold machine_wordsize; simpl; lia. }

      assert (0 <= q_hi2 < 2).
      { split.
        { pose proof (canonical_bounded _ _ H2).
          assert (In q_hi2 q).
          { rewrite H1.
            simpl.
            apply in_or_app.
            right.
            simpl.
            intuition. }
          apply H4 in H5.
          lia. }
        { pose proof fun pf => nth_default_partition weight 0 (S n) (eval weight (S n) q) (1 + length q_lo) pf.
          unfold canonical_repr in H2.
          intuition.
          rewrite <-H7 in H4.
          rewrite H1 in H4 at 1.
          rewrite nth_default_app in H4.
          destruct (lt_dec) in H4; try lia.
          replace (1 + Datatypes.length q_lo - Datatypes.length q_lo)%nat with 1%nat in H4 by lia.
          unfold nth_default in H4.
          simpl in H4.
          cbv [q] in H4.
          rewrite H3 in H4.
          rewrite H4.
          apply Z.div_lt_upper_bound.
          eauto.
          apply Le.Z.le_sub_1_iff.
          etransitivity.
          apply Z.mod_le.
          autorewrite with push_eval zsimplify_const.
          rewrite solinas_property.
          cbn [fst snd].

          apply OrdersEx.Z_as_OT.add_nonneg_nonneg.
          apply OrdersEx.Z_as_OT.mul_nonneg_nonneg.
          apply OrdersEx.Z_as_OT.mul_nonneg_nonneg.
          apply Z.div_nonneg.
          apply OrdersEx.Z_as_OT.lt_le_incl.
          apply wprops.
          lia.
          lia.
          eapply canonical_bounded.
          apply H5.
          rewrite H.
          apply in_or_app; right; simpl; eauto.
          apply canonical_pos.
          eapply canonical_app_l.
          eauto.
          length_q p.
          3: eauto.
          eauto.
          length_q p.
          apply wprops.
          rewrite OrdersEx.Z_as_OT.le_add_le_sub_r.

          assert (weight (S (Datatypes.length q_lo)) <= weight (S (Datatypes.length q_lo)) * 2 - 1 - eval weight n lo).
          { rewrite <-OrdersEx.Z_as_OT.le_add_le_sub_l.
            rewrite <-OrdersEx.Z_as_OT.le_add_le_sub_l.
            rewrite Z.add_assoc.
            rewrite OrdersEx.Z_as_OT.le_add_le_sub_r.
            ring_simplify.
            eapply canonical_app_l with (l1:=lo) (n1:=n) in H5.
            apply canonical_eval_bounded in H5.
            rewrite Le.Z.le_add_1_iff.
            replace (S (length q_lo)) with n by (length_q q).
            assumption.
            length_q p.
            3: eauto.
            reflexivity.
            simpl.
            lia. }
          etransitivity.
          2: eassumption.
          autorewrite with push_eval zsimplify_const.
          rewrite solinas_property.
          cbn [fst snd].
          etransitivity.
          apply Zmult_le_compat_r with (p:=hi) in coef_small2.
          apply coef_small2.
          eapply canonical_bounded; eauto.
          rewrite H.
          apply in_or_app; right; simpl; eauto.
          weight_comp.
          etransitivity.
          apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l.
          lia.
          eauto.
          apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l.
          lia.
          etransitivity.
          assert (39 <= 2^machine_wordsize).
          unfold machine_wordsize.
          lia.
          eauto.
          apply OrdersEx.Z_as_OT.pow_le_mono_r.
          lia.
          rewrite <-OrdersEx.Z_as_OT.le_mul_diag_r.
          replace (length q_lo) with (n-1)%nat.
          lia.
          length_q q.
          lia.
          lia.
          lia.
          length_q q. }
      }
      assert (q_hi2 = 1 \/ q_hi2 = 0) by lia.
      intuition.
      left.
      intuition.
      pose proof f_equal (eval weight (S n)) H1.
      erewrite app_assoc, !eval_snoc in H5; eauto.
      cbv [q] in H5.
      rewrite H3 in H5.
      subst.
      autorewrite with zsimplify_const in H5.
      apply LinearSubstitute.Z.move_L_pX in H5.

      remember (Associational.eval (Associational.sat_mul_const base [(1, fst (Rows.adjust_s weight (S (S (S n))) s) / s)] c)) as coef.
      pose proof
           fun pf => nth_default_partition weight 0 n (coef * hi + eval weight n lo - weight (S (Datatypes.length q_lo))) (length q_lo) pf.
      assert (Partition.partition weight n (coef * hi + eval weight n lo - weight (S (Datatypes.length q_lo))) = q_lo ++ [q_hi1]).
      { assert (canonical_repr n (q_lo ++ [q_hi1])).
        { eapply canonical_app_l.
          apply H2.
          length_q q.
          3: rewrite <-app_assoc; eauto.
          simpl.
          eauto.
          lia. }
        unfold canonical_repr in H4; intuition.
        rewrite H10.
        f_equal.
        rewrite H5.
        assert (n = S (length q_lo)) by length_q q.
        rewrite H4.
        rewrite eval_snoc_S.
        reflexivity.
        reflexivity. }

      rewrite H4 in H.
      rewrite nth_default_app in H.
      destruct lt_dec in H.
      lia.
      replace (Datatypes.length q_lo - Datatypes.length q_lo)%nat with 0%nat in H by lia.
      replace (nth_default 0 [q_hi1] 0) with (q_hi1) in H.

      rewrite H.
      apply Z.div_small.
      assert (0 <= (coef * hi + eval weight n lo - weight (S (Datatypes.length q_lo)))).
      { rewrite H5.
        etransitivity.
        assert (canonical_repr (length q_lo) q_lo).
        { eapply canonical_app_l.
          apply H2.
          length_q q.
          eauto.
          2: eauto.
          length_q q. }
        apply canonical_pos in H9.
        apply H9.
        replace (eval weight (Datatypes.length q_lo) q_lo) with
          (eval weight (Datatypes.length q_lo) q_lo + 0) at 1.
        apply Zplus_le_compat_l.
        apply OrdersEx.Z_as_DT.mul_nonneg_nonneg.
        apply OrdersEx.Z_as_OT.lt_le_incl.
        apply wprops.
        pose proof (canonical_bounded _ _ H2).
        apply H9.
        rewrite H1.
        apply in_or_app.
        right.
        apply in_or_app.
        simpl.
        intuition.
        lia. }
      split.
      apply Z_mod_nonneg_nonneg.
      eauto.
      apply OrdersEx.Z_as_OT.lt_le_incl.
      apply wprops.

      rewrite <- Le.Z.le_sub_1_iff.
      etransitivity.
      apply OrdersEx.Z_as_OT.mod_le.
      eauto.
      apply wprops.
      rewrite Le.Z.le_sub_1_iff.
      rewrite OrdersEx.Z_as_OT.lt_sub_lt_add_r.
      etransitivity.
      assert (canonical_repr n lo).
      { eapply canonical_app_l.
        apply H6.
        length_q (lo ++ [hi]).
        eauto.
        2: eauto.
        length_q (lo ++ [hi]). }
      pose proof (canonical_eval_bounded _ _ H10).
      apply Zplus_lt_compat_l with (p:=coef*hi).
      eauto.
      replace (S (length q_lo)) with n by (length_q q).
      apply Zplus_lt_compat_r.
      rewrite Heqcoef.
      autorewrite with push_eval.
      rewrite solinas_property.
      cbn [fst snd].
      ring_simplify.
      rewrite <- Le.Z.le_sub_1_iff.
      etransitivity.
      apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_r with (p:=hi) in coef_small.
      apply coef_small.
      eapply canonical_bounded.
      apply H6.
      apply in_or_app; right; simpl; eauto.
      etransitivity.
      apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_l with (p:=2^(machine_wordsize/2)) in H7.
      eauto.
      lia.
      rewrite Le.Z.le_sub_1_iff.
      replace (length q_lo) with (n-1)%nat by (length_q q).
      weight_comp.
      unfold machine_wordsize.
      rewrite <- Le.Z.le_sub_1_iff.
      eapply OrdersEx.Z_as_OT.le_trans with (m:=2 ^ (64 * Z.of_nat (2 - 1))-1).
      simpl.
      lia.
      apply OrdersEx.Z_as_OT.sub_le_mono_r.
      apply OrdersEx.Z_as_OT.pow_le_mono_r.
      lia.
      lia.
      length_q q.
      reflexivity.
      length_q q.
      length_q q.
    Qed.

    Theorem reduce_second base s c n (s_nz:s<>0) : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        (canonical_repr (S n) p /\ hi <= 39) ->
        forall q_lo q_hi1 q_hi2,
          let q := reduce1 base s c (S n) (S n) p in
          q = q_lo ++ [q_hi1] ++ [q_hi2] ->
          canonical_repr (S n) q ->
          ((q_hi2 = 1 /\ q_hi1 = 0) \/
             (q_hi2 = 0)).
    Proof using wprops.
      intros.

      intuition.

      assert (Hevalq : eval weight (S n) q = 38 * hi + eval weight n lo).
      { cbv [reduce1 canonical_repr] in *.
        intuition.
        cbv [q].
        rewrite !H.
        rewrite Rows.flatten_mod.
        rewrite Rows.eval_from_associational.
        rewrite value_sat_reduce.

        lazymatch goal with
        | |- context[Saturated.Rows.adjust_s ?weight ?fuel ?s] =>
            destruct (adjust_s_invariant fuel s ltac:(assumption)) as [Hmod ?]
        end.

        assert (Rows.adjust_s weight (S (S (S n))) s = (weight 4, true)) by admit.
        rewrite H7 in *.

        Search Rows.adjust_s.
        cbn [fst] in *.
        cbv [to_associational].
        rewrite seq_snoc.
        rewrite map_app.
        replace (map weight [(0 + n)%nat]) with [weight n] by auto.
        rewrite combine_snoc.

        rewrite fst_split_app.
        rewrite snd_split_app.
        autorewrite with push_eval.

        assert (n = 4%nat) by admit.
        rewrite H8.
        assert (split (weight 4) [(weight 4, hi)] = ([], [(1, hi)])) by eauto.
        rewrite H9; cbn [fst snd].
        autorewrite with push_eval; cbn [fst snd]; autorewrite with zsimplify_const.
        assert (split (weight 4) (combine (map weight (seq 0 4)) lo) =
                  ((combine (map weight (seq 0 4)) lo), [])).
        { admit. }
        rewrite H10; cbn [fst snd].
        autorewrite with push_eval; cbn [fst snd]; autorewrite with zsimplify_const.
        assert (s = 2^255) by admit.
        assert (c = [(1, 19)]) by admit.
        assert (base = 2^256) by admit.
        rewrite H11, H12, H13.
        replace (weight 4 / 2 ^ 255) with 2 by eauto.
        replace (Associational.eval (Associational.sat_mul_const (2 ^ 256) [(1, 2)] [(1, 19)])) with (38) by reflexivity.

        autorewrite with push_eval; cbn [fst snd]; autorewrite with zsimplify_const.
        unfold eval, to_associational.
        apply Zmod_small.
        split.
        admit.
        Locate "<=".
        Search Positional.eval .
        pose proof BYInv.eval_bound.
        assert (0 < 64) by lia.
        apply H14 with (n:=4%nat) (f:=lo) in H15.
        unfold eval, to_associational in H15.
        assert (2 ^ (64 * Z.of_nat 4) <= weight 5 - 38 * 39).
        {
          vm_compute.
          intuition.
          discriminate x. }
        unfold weight in *.

        all: admit.

        (* rewrite H in H2. *)
        (* rewrite app_length in H2. *)
        (* simpl in H2. *)
        (* rewrite plus_comm in H2. *)
        (* rewrite map_length. *)
        (* rewrite seq_length. *)
        (* lia. *)

        (* admit. (* base <> 0 *) *)
        (* eauto. *)
        (* lia. *)
        (* eauto. *)
        (* intros. *)
        (* eapply Rows.length_from_associational; eauto. *)
      }

      assert (q_hi2 < 2).
      { pose proof fun pf => nth_default_partition weight 0 (S n) (eval weight (S n) q) (1 + length q_lo) pf.
        unfold canonical_repr in H2.
        destruct H2.
        rewrite <-H5 in H0.
        rewrite H1 in H0 at 1.
        Search nth_default app.
        rewrite nth_default_app in H0.
        destruct (lt_dec) in H0.
        lia.
        replace (1 + Datatypes.length q_lo - Datatypes.length q_lo)%nat with 1%nat in H0 by lia.
        unfold nth_default in H0.
        simpl in H0.
        rewrite Hevalq in H0.
        rewrite H0.
        Search (_ / _ < _).
        apply Z.div_lt_upper_bound.
        eauto.

        Search Z.lt Z.le 1 iff.
        apply Le.Z.le_sub_1_iff.

        etransitivity.
        apply Z.mod_le.
        admit.
        eauto.



        admit.
        admit. }

      assert (q_hi2 >= 0) by admit.
      assert (q_hi2 = 1 \/ q_hi2 = 0) by lia.
      intuition.
      left.
      intuition.
      pose proof f_equal (eval weight (S n)) H1.
      rewrite app_assoc in H6.
      Search eval app.
      erewrite eval_snoc in H6.
      2: eauto.
      erewrite eval_snoc in H6.
      2: eauto.
      Search (_ = _ + _ -> _ - _ = _).
      rewrite Hevalq in H6.
      subst.
      autorewrite with zsimplify_const in H6.
      apply LinearSubstitute.Z.move_L_pX with (y:=weight (Datatypes.length (q_lo ++ [q_hi1]))) in H6.
      Search nth_default Partition.partition.
      pose proof fun pf => nth_default_partition weight 0 (n) (38 * hi + eval weight n lo - weight (Datatypes.length (q_lo ++ [q_hi1]))) (length q_lo) pf.
      assert (Partition.partition weight n (38 * hi + eval weight n lo - weight (Datatypes.length (q_lo ++ [q_hi1]))) = q_lo ++ [q_hi1]) by admit.
      rewrite H7 in H.
      rewrite nth_default_app in H.
      destruct lt_dec in H.
      lia.
      replace (Datatypes.length q_lo - Datatypes.length q_lo)%nat with 0%nat in H by lia.
      replace (nth_default 0 [q_hi1] 0) with (q_hi1) in H.
      2: { unfold nth_default.
           reflexivity. }
      rewrite H.
      Search (_ / _ = 0).
      apply Z.div_small.
      split.
      admit.
      apply Le.Z.le_sub_1_iff.
      etransitivity.
      apply Z.mod_le.
      admit.
      apply wprops.
      { admit. }
      unfold canonical_repr in H2.
      intuition.
      apply f_equal with (f:=fun l => length l) in H1.
      rewrite !app_length in H1.
      cbn [Datatypes.length] in H1.
      assert (Datatypes.length q_lo = (n - 1)%nat) by lia.
      lia.
      rewrite app_length.
      cbn [Datatypes.length].
      lia.

      unfold canonical_repr in H2.
      intuition.
      apply f_equal with (f:=fun l => length l) in H1.
      rewrite !app_length in *.
      cbn [Datatypes.length] in *.
      apply f_equal.
      rewrite H8 in H1.
      lia.
    Admitted.

  End __.

  Section compile.

    Let s := 2^255.
    Let c := [(1, 19)].
    Let machine_wordsize := 64.
    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m : nat := 2 * n.
    Let w : nat -> Z := weight machine_wordsize 1.
    Let base : Z := 2 ^ machine_wordsize.

    Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.
    Let boundsn : list (ZRange.type.option.interp base.type.Z)
        := repeat bound (n).

    Import Stringification.C.Compilers.
    Import Stringification.C.Compilers.ToString.

    Local Existing Instances ToString.C.OutputCAPI Pipeline.show_ErrorMessage.
    Local Instance : only_signed_opt := false.
    Local Instance : no_select_opt := false.
    Local Instance : static_opt := true.
    Local Instance : internal_static_opt := true.
    Local Instance : inline_opt := true.
    Local Instance : inline_internal_opt := true.
    Local Instance : use_mul_for_cmovznz_opt := false.
    Local Instance : emit_primitives_opt := true.
    Local Instance : should_split_mul_opt := false.
    Local Instance : should_split_multiret_opt := false.
    Local Instance : widen_carry_opt := false.
    Local Instance : widen_bytes_opt := true. (* true, because we don't allow byte-sized things anyway, so we should not expect carries to be widened to byte-size when emitting C code *)

    Let possible_values := prefix_with_carry [machine_wordsize].
    Local Instance : machine_wordsize_opt := machine_wordsize. (* for show *)
    Local Instance : no_select_size_opt := no_select_size_of_no_select machine_wordsize.
    Local Instance : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.
    Local Instance : split_multiret_to_opt := split_multiret_to_of_should_split_multiret machine_wordsize possible_values.


    Compute reduce

    Time Compute
         Show.show
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false
            false
            None
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) in
                  let r := Reify (reduce w base s c n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (2*n)), tt)
                   (Some (repeat bound (n)))
                   (None, tt)
                   (None)
           : Pipeline.ErrorT _).

  End compile.

End solinas_reduction.
