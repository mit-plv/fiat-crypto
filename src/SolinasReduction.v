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
Require Import Crypto.Util.ListUtil.FoldBool.
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

    Context (machine_wordsize := 64)
            (weight := uweight machine_wordsize)
            (up_bound := 2 ^ (machine_wordsize / 4))
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

    Lemma adjust_s_finished' fuel s w (s_nz:s<>0) :
      Rows.adjust_s weight fuel s = (w, true) ->
      Rows.adjust_s weight (S fuel) s = (w, true).
    Proof.
      cbv [Rows.adjust_s].
      rewrite !fold_right_map.
      replace (rev (seq 0 (S fuel))) with (fuel :: rev (seq 0 fuel)).
      generalize (rev (seq 0 fuel)).
      cbn in *.
      intros.
      induction l;
        break_match; auto; discriminate.
      rewrite seq_snoc.
      rewrite rev_app_distr.
      reflexivity.
    Qed.

    Lemma adjust_s_finished fuel fuel' s w (s_nz:s<>0) :
      (fuel' > fuel)%nat ->
      Saturated.Rows.adjust_s weight fuel s = (w, true) ->
      Saturated.Rows.adjust_s weight fuel' s = (w, true).
    Proof.
      induction 1; intros; apply adjust_s_finished'; auto.
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
      let r_rows := Saturated.Rows.from_associational weight m r_a in
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

    Ltac solve_length q :=
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

    Ltac solve_ineq :=
      repeat
        match goal with
        | [ |- 0 <= _ + _ ] => apply OrdersEx.Z_as_OT.add_nonneg_nonneg
        | _ => apply OrdersEx.Z_as_OT.mul_nonneg_nonneg
        | _ => apply OrdersEx.Z_as_DT.div_pos

        | |- _ + ?x < _ + ?x => apply OrdersEx.Z_as_OT.add_lt_mono_r
        | [ |- _ + _ < _ ] => apply OrdersEx.Z_as_OT.add_lt_mono
        | [ |- _ + _ <= _ ] => apply OrdersEx.Z_as_OT.add_le_mono

        | [ |- 0 <= weight _ ] => apply OrdersEx.Z_as_OT.lt_le_incl;
                               apply wprops
        | _ => lia
        end.

    Ltac solve_in :=
      repeat
        match goal with
        | [ |- In ?hi ?p ] =>
            match goal with
            | [ H : p = _ ++ _ |- _ ] =>
                rewrite H; apply in_or_app; simpl; auto
            | [ H : p = _ ++ _ ++ _ |- _ ] =>
                rewrite app_assoc in H
            end
        end.

    Ltac apply_iff p :=
      match goal with
      | [ H : canonical_repr _ p |- _ ] =>
          rewrite canonical_iff in H;
          destruct H as [ _ Htmp ];
          apply Htmp;
          solve_in
      end.
    Ltac solve_hi :=
      match goal with
      | [ |- 0 <= ?hi ] =>
          match goal with
          | [ H : ?p = _ ++ [hi] |- _ ] => apply_iff p
          | [ H : ?p = _ ++ [hi] ++ _ |- _ ] => apply_iff p
          | [ H : ?p = _ ++ _ ++ [hi] |- _ ] => apply_iff p
          end
      end.

    Ltac adjust_ineq_lt H :=
      match type of H with
      | context[ ?x < ?y ] =>
          match goal with
          | [ |- context[ x * ?z ] ] =>
              apply Zmult_lt_compat_r with (p:=z) in H; eauto
          end
      end.
    Ltac adjust_ineq_le H :=
      match type of H with
      | context[ ?x <= ?y ] =>
          match goal with
          | [ |- context[ x * ?z ] ] =>
              apply Zmult_le_compat_r with (p:=z) in H; eauto
          end
      end.
    Ltac adjust_ineq H := adjust_ineq_le H || adjust_ineq_lt H.

    Ltac canonical_app p :=
      let H' := fresh "TEMP" in
      pose proof (eq_refl p) as H';
      match goal with
      | [ H : p = ?lo ++ ?hi |- _ ] =>
          let H1 := fresh "Hcanon_l" in
          let H2 := fresh "Hcanon_r" in
          match goal with
          | [ H' : canonical_repr _ p |- _ ] =>
              eapply canonical_app_l with (l1:=lo) (n1:=length lo) (l2:=hi) (n2:=length hi) in H' as H1;
              eapply canonical_app_r with (l1:=lo) (n1:=length lo) (l2:=hi) (n2:=length hi) in H' as H2;
              try (solve_length p)
          end
      end;
      clear H'.

    Ltac subst_canon q :=
      match goal with
      | [ H : canonical_repr ?n1 ?p |- canonical_repr ?n2 ?p ] =>
          replace n2 with n1 by (solve_length q);
          auto
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

    Lemma split_gt w l1 l2:
      (forall x, In x l1 -> x mod w = 0) ->
      length l1 = length l2 ->
      split w (combine l1 l2) = ([], combine (map (fun t => t / w) l1) l2).
    Proof.
      intros.
      generalize dependent l2.
      induction l1; intros.
      reflexivity.
      simpl.
      break_match.
      auto.
      match goal with
      | [ |- context[ ?x :: ?y ] ] => replace (x :: y) with ([x] ++ y) by eauto
      end.
      rewrite split_app.
      rewrite IHl1.
      cbn [fst snd].
      simpl.
      break_match; cbn.
      reflexivity.
      rewrite Z.eqb_neq in Heqb.
      rewrite H in Heqb.
      lia.
      simpl.
      auto.
      intros.
      apply H.
      simpl.
      auto.
      simpl in H0.
      lia.
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

    Context (n_gt_1 : n > 1)
            (s_pos : s > 0)
            (c_pos : Associational.eval c > 0)
            (mod_nz : s - Associational.eval c <> 0)
            (base_nz : base <> 0)
            (solinas_property : Rows.adjust_s weight (S (S n)) s = (weight n, true))
            (coef_small : weight n / s * Associational.eval c < up_bound).

    Lemma split_p : forall p lo hi,
        p = lo ++ [hi] ->
        canonical_repr (S n) p ->
        (split (weight n) [(weight n, hi)] = ([], [(1, hi)])) /\
          (split (weight n) (combine (map weight (seq 0 n)) lo) =
             ((combine (map weight (seq 0 n)) lo), [])).
    Proof.
      intros.
      intuition.
      { intros.
        unfold split.
        simpl.
        assert (weight n mod weight n = 0) by (apply Z_mod_same_full).
        rewrite H1.
        simpl.
        assert (weight n / weight n = 1) by
          auto using Z_div_same, Z.lt_gt, weight_positive.
        rewrite H2.
        reflexivity. }
      { apply split_lt.
        intros.
        rewrite in_map_iff in H1.
        destruct H1.
        intuition.
        rewrite <-H2.
        auto.
        rewrite <-H2.
        rewrite in_seq in H3.
        intuition.
        simpl in H4.
        apply weight_mono.
        lia.
        rewrite map_length.
        rewrite seq_length.
        solve_length p. }
    Qed.

    Lemma reduce_in_range : forall m x,
        x < weight 1 - weight 0 ->
        x + weight m < weight (S m).
    Proof.
      intros.
      rewrite OrdersEx.Z_as_DT.lt_add_lt_sub_r.
      induction m.
      auto.
      etransitivity.
      apply IHm.
      unfold weight.
      rewrite uweight_S.
      rewrite uweight_S.
      rewrite <-uweight_S at 1.
      rewrite <-OrdersEx.Z_as_OT.mul_sub_distr_l.
      rewrite Z.mul_comm.
      rewrite <-OrdersEx.Z_as_OT.lt_mul_diag_r.
      simpl; lia.
      rewrite OrdersEx.Z_as_OT.lt_0_sub.
      fold weight.
      apply weight_mono'.
      lia.
      lia.
      lia.
    Qed.

    Lemma map_weight_seq : forall m p,
        map weight (seq 0 p) = map (fun t => t / (weight m)) (map weight (seq m p)).
    Proof.
      induction m; intros.
      { generalize dependent (map weight (seq 0 p)).
        intros.
        erewrite map_ext.
        symmetry.
        eapply map_id.
        intros.
        rewrite weight_0.
        rewrite Z.div_1_r.
        lia.
        auto. }
      { rewrite IHm.
        rewrite <-map_S_seq.
        rewrite !map_map.
        apply map_ext_Forall.
        rewrite Forall_forall.
        intros.
        rewrite in_seq in H.
        weight_comp.
        rewrite <-OrdersEx.Z_as_OT.pow_add_r.
        rewrite <- !OrdersEx.Z_as_OT.pow_sub_r.
        f_equal.
        lia.
        lia.
        lia.
        lia.
        lia.
        lia.
        lia.
        lia.
        lia. }
    Qed.

    Lemma split_p' : forall (p lo hi : list Z),
        p = lo ++ hi ->
        canonical_repr (2 * n) p ->
        length lo = n ->
        split (weight n) (combine (map weight (seq 0 n)) lo) = (combine (map weight (seq 0 n)) lo, []) /\
          split (weight n) (combine (map weight (seq n n)) hi) = ([], combine (map weight (seq 0 n)) hi).
    Proof.
      intros.
      intuition.
      { apply split_lt.
        intros.
        rewrite in_map_iff in H2.
        destruct H2.
        intuition; rewrite <-H3.
        auto.
        rewrite in_seq in H4.
        apply weight_mono.
        lia.
        rewrite map_length.
        rewrite seq_length.
        auto. }
      { rewrite map_weight_seq with (m:=n).
        apply split_gt.
        intros.
        rewrite in_map_iff in H2.
        destruct H2.
        intuition; rewrite <-H3.
        apply Weight.weight_multiples_full.
        auto.
        auto.
        rewrite in_seq in H4.
        lia.
        rewrite map_length, seq_length.
        solve_length p. }
    Qed.

    Lemma value_reduce_first : forall (p lo hi : list Z),
        p = lo ++ hi ->
        canonical_repr (2 * n) p ->
        length lo = n ->
        let q := reduce1 base s c (2 * n) (S n) p in
        let s' := fst (Saturated.Rows.adjust_s weight (S (S (S n))) s) in
        let coef := Associational.sat_mul_const base [(1, s'/s)] c in
        eval weight (S n) q = Associational.eval coef * eval weight n hi + eval weight n lo.
    Proof.
      intros.
      pose proof (split_p' _ _ _ H H0 H1) as Hsplit.
      destruct Hsplit as [ Hlo Hhi ].
      canonical_app p.
      replace (length hi) with n in * by (solve_length p).
      replace (length lo) with n in *.
      unfold q, reduce1.
      rewrite H.
      rewrite Rows.flatten_mod, Rows.eval_from_associational, value_sat_reduce.
      unfold to_associational.
      cbn [fst snd].
      erewrite adjust_s_finished; try apply solinas_property.
      replace (2 * n)%nat with (n + n)%nat by lia.
      rewrite seq_add.
      rewrite Nat.add_0_l.
      rewrite map_app.
      rewrite combine_app_samelength.
      rewrite fst_split_app, snd_split_app.
      cbn [fst snd].
      rewrite Hlo, Hhi.
      autorewrite with push_eval zsimplify_const.
      cbn [snd].
      unfold coef, s'.
      autorewrite with push_eval zsimplify_const.
      erewrite adjust_s_finished; try apply solinas_property.
      cbn [fst snd].

      rewrite Z.mod_small.
      reflexivity.
      split.
      solve_ineq; apply canonical_pos; auto.
      etransitivity.
      solve_ineq.
      apply Z.mul_lt_mono_nonneg.
      solve_ineq.
      eauto.
      apply canonical_pos; auto.
      apply canonical_eval_bounded; auto.
      apply canonical_eval_bounded; auto.
      weight_comp.
      rewrite Z.mul_comm.
      rewrite Zred_factor3.
      apply Zmult_lt_compat_l.
      lia.
      simpl.
      lia.
      lia.
      lia.
      lia.
      lia.
      rewrite map_length, seq_length.
      solve_length lo.
      lia.
      lia.
      lia.
      auto.
      lia.
      auto.
      intros.
      eapply Rows.length_from_associational; eauto.
    Qed.

    Lemma reduce_second_canonical : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        hi < up_bound ->
        canonical_repr (S n) p ->
        canonical_repr (S n) (reduce1 base s c (S n) (S n) p).
    Proof.
      intros.
      unfold reduce1 in *.
      unfold canonical_repr.
      intuition.
      { rewrite Rows.flatten_correct.
        cbn [fst].
        auto with push_length.
        eauto.
        intros.
        eapply Rows.length_from_associational.
        eauto. }
      { pose proof (split_p _ _ _ H H1).
        intuition.

        rewrite Rows.flatten_correct.
        cbn [fst].
        rewrite Partition.eval_partition.
        f_equal.
        apply Z.mod_small_sym.

        rewrite Rows.eval_from_associational.
        rewrite H.
        rewrite value_sat_reduce.
        apply adjust_s_finished' in solinas_property.
        rewrite solinas_property.
        autorewrite with push_eval zsimplify_const.
        cbn [fst snd].
        unfold to_associational.
        rewrite seq_snoc.
        rewrite map_app.
        rewrite Nat.add_0_l; cbn [map].
        rewrite combine_snoc.
        rewrite fst_split_app, snd_split_app.
        autorewrite with push_eval.
        rewrite H3, H4.
        cbn [fst snd].
        autorewrite with push_eval zsimplify_const.
        cbn [snd].

        split.
        apply OrdersEx.Z_as_OT.add_nonneg_nonneg.
        apply OrdersEx.Z_as_OT.mul_nonneg_nonneg.
        apply OrdersEx.Z_as_OT.mul_nonneg_nonneg.
        apply Z.div_nonneg.
        auto with zarith.
        lia.
        lia.
        eapply canonical_bounded; eauto.
        rewrite H; apply in_or_app; right; simpl; eauto.
        rewrite H in H1.
        assert (canonical_repr n lo).
        { eapply canonical_app_l.
          apply H1.
          solve_length (lo++[hi]).
          3: eauto.
          eauto.
          solve_length (lo++[hi]). }
        pose proof (canonical_pos _ _ H2).
        unfold eval, to_associational in H5.
        auto.

        assert (weight n / s * Associational.eval c * hi < up_bound * up_bound).
        { apply OrdersEx.Z_as_OT.mul_lt_mono_nonneg.
          apply OrdersEx.Z_as_OT.mul_nonneg_nonneg.
          apply Z.div_nonneg.
          auto with zarith.
          lia.
          lia.
          auto.
          eapply canonical_bounded; eauto.
          rewrite H; apply in_or_app; right; simpl; eauto.
          auto. }

        assert (canonical_repr n lo).
        { eapply canonical_app_l.
          apply H1.
          solve_length p.
          3: eauto.
          eauto.
          solve_length p. }
        pose proof (canonical_eval_bounded _ _ H5).

        etransitivity.
        apply OrdersEx.Z_as_OT.add_lt_mono.
        eauto.
        eauto.
        apply reduce_in_range.
        vm_compute; auto.

        (* generated lemmas *)
        rewrite map_length.
        rewrite seq_length.
        solve_length p.
        lia.
        lia.
        auto.
        auto.
        auto.
        auto.
        intros.
        eapply Rows.length_from_associational; eauto. }
    Qed.

    Lemma value_reduce_second : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        canonical_repr (S n) p ->
        hi < up_bound ->
        let q := reduce1 base s c (S n) (S n) p in
        let s' := fst (Saturated.Rows.adjust_s weight (S (S (S n))) s) in
        let coef := Associational.sat_mul_const base [(1, s'/s)] c in
        eval weight (S n) q = Associational.eval coef * hi + eval weight n lo.
    Proof.
      intros.
      unfold reduce1 in *.
      unfold q, coef, s'.
      rewrite H.
      rewrite Rows.flatten_mod, Rows.eval_from_associational, value_sat_reduce.

      unfold to_associational.
      rewrite seq_snoc.
      rewrite map_app.
      rewrite Nat.add_0_l; cbn [map].
      rewrite combine_snoc.
      rewrite fst_split_app, snd_split_app.
      autorewrite with push_eval.

      pose proof solinas_property as Hsol.
      apply adjust_s_finished' in Hsol.
      rewrite Hsol.
      cbn [fst snd]; autorewrite with zsimplify_const.
      pose proof (split_p _ _ _ H H0) as Hsplit.
      destruct Hsplit as [ Hhi Hlo ].
      rewrite Hhi, Hlo.
      cbn [fst snd]; autorewrite with push_eval zsimplify_const; cbn [snd].

      unfold eval, to_associational.
      apply Z.mod_small.
      assert (Hmach : 0 < machine_wordsize) by lia.
      apply BYInv.eval_bound with (n:=n) (f:=lo) in Hmach.
      unfold eval, to_associational in Hmach.
      intuition.

      solve_ineq.
      solve_hi.
      auto.

      rewrite <-Le.Z.le_sub_1_iff.
      etransitivity.
      solve_ineq.
      apply OrdersEx.Z_as_OT.lt_le_incl in coef_small as coef_small'.
      adjust_ineq coef_small'.
      solve_hi.
      rewrite Le.Z.le_sub_1_iff.
      eauto.
      rewrite OrdersEx.Z_as_OT.add_sub_assoc.
      rewrite <-OrdersEx.Z_as_OT.sub_le_mono_r.

      etransitivity.
      solve_ineq.
      apply OrdersEx.Z_as_OT.lt_le_incl in H1 as H1'.
      apply Zmult_le_compat_l.
      eauto.
      lia.
      reflexivity.

      etransitivity.
      unfold up_bound.

      match goal with
      | [ |- context[ ?x + ?y ] ] =>
          assert (x <= y)
      end.
      ring_simplify.
      rewrite <-OrdersEx.Z_as_OT.pow_mul_r.
      apply OrdersEx.Z_as_OT.pow_le_mono_r.
      lia.
      unfold machine_wordsize.
      simpl.
      break_match; lia.
      (* proving 0 <= 64 / 4... is there an easier way? *)
      unfold machine_wordsize.
      replace (64 / 4) with 16 by eauto.
      lia.
      (* *)
      lia.
      solve_ineq.
      eauto.
      reflexivity.
      weight_comp.
      simpl.
      break_match; lia.
      lia.
      lia.

      canonical_app p.
      eapply canonical_bounded.
      apply Hcanon_l.
      solve_length p.
      lia.
      rewrite map_length.
      rewrite seq_length.
      solve_length p.
      lia.
      auto.
      auto.
      auto.
      intros.
      eapply Rows.length_from_associational; eauto.
    Qed.

    Lemma reduce_second : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        canonical_repr (S n) p ->
        hi < up_bound ->
        forall q_lo q_hi1 q_hi2,
          let q := reduce1 base s c (S n) (S n) p in
          q = q_lo ++ [q_hi1] ++ [q_hi2] ->
          ((q_hi2 = 1 /\ q_hi1 = 0) \/
             (q_hi2 = 0)).
    Proof.
      intros.
      pose proof (value_reduce_second _ _ _ H H0 H1).
      pose proof (reduce_second_canonical _ _ _ H H1 H0) as Hqcanon.
      fold q in Hqcanon.

      assert (0 <= q_hi2 < 2).
      { intuition.
        eapply canonical_bounded.
        apply Hqcanon.
        solve_in.

        pose proof fun pf => nth_default_partition weight 0 (S n) (eval weight (S n) q) (1 + length q_lo) pf as Hnth.
        assert (Hqcanon' := Hqcanon).
        unfold canonical_repr in Hqcanon'.
        destruct Hqcanon' as [ _ Hqpart ].
        rewrite <-Hqpart in Hnth.
        rewrite H2 in Hnth at 1.
        rewrite nth_default_app in Hnth.
        destruct lt_dec in Hnth.
        lia.
        rewrite Nat.add_sub in Hnth.
        unfold nth_default in Hnth.
        simpl in Hnth.
        rewrite Hnth.
        unfold q.
        apply Z.div_lt_upper_bound.
        auto.

        rewrite H3.
        autorewrite with push_eval.
        apply adjust_s_finished' in solinas_property.
        rewrite solinas_property.
        cbn [fst snd].
        autorewrite with zsimplify_const.
        apply Le.Z.le_sub_1_iff.
        etransitivity.
        apply Z.mod_le.
        solve_ineq.
        solve_hi.
        apply canonical_pos.
        canonical_app p.
        replace n with (length lo).
        auto.
        solve_length p.
        auto.
        apply Le.Z.le_sub_1_iff.

        etransitivity.
        solve_ineq.
        apply Z.mul_lt_mono_nonneg.
        solve_ineq.
        eauto.
        solve_hi.
        eauto.
        apply canonical_eval_bounded.
        canonical_app p.
        replace n with (length lo).
        auto.
        solve_length p.

        rewrite <-Zplus_diag_eq_mult_2.
        replace (S (length q_lo)) with n by (solve_length q).
        solve_ineq.

        unfold up_bound.
        weight_comp.
        rewrite <-OrdersEx.Z_as_OT.pow_mul_r.
        apply OrdersEx.Z_as_OT.pow_lt_mono_r.
        lia.
        unfold machine_wordsize.
        simpl.
        break_match; lia.
        unfold machine_wordsize.
        simpl.
        break_match; lia.
        (* proving 0 <= 64 / 4... is there an easier way? *)
        unfold machine_wordsize.
        replace (64 / 4) with 16 by eauto.
        lia.
        lia.
        lia.
        solve_length q. }

      assert (q_hi2 = 0 \/ q_hi2 = 1) by lia.
      intuition.
      left.
      intuition.
      pose proof f_equal (eval weight (S n)) H2 as Hqeval.
      erewrite app_assoc, !eval_snoc in Hqeval; eauto; try (solve_length q).
      unfold q in Hqeval.
      rewrite H3 in Hqeval.
      subst q_hi2.
      autorewrite with push_eval zsimplify_const in Hqeval.
      apply adjust_s_finished' in solinas_property.
      rewrite solinas_property in Hqeval.
      cbn [fst snd] in Hqeval.
      apply LinearSubstitute.Z.move_L_pX in Hqeval.

      remember (weight n / s * Associational.eval c) as coef.
      pose proof
           fun pf => nth_default_partition weight 0 n (coef * hi + eval weight n lo - weight (S (Datatypes.length q_lo))) (length q_lo) pf as Heval.

      rewrite app_assoc in H2.
      canonical_app q.
      rewrite app_length in Hcanon_l.
      cbn [length] in Hcanon_l.
      unfold canonical_repr in Hcanon_l.
      destruct Hcanon_l as [ _ Hcanon_l ].

      assert (Partition.partition weight n (coef * hi + eval weight n lo - weight (S (Datatypes.length q_lo))) = q_lo ++ [q_hi1]) as Hqpart.
      rewrite Hcanon_l.
      f_equal.
      solve_length q.
      erewrite eval_snoc; try (solve_length q).
      apply Hqeval.

      rewrite Hqpart in Heval.
      rewrite nth_default_app in Heval.
      destruct lt_dec in Heval; try lia.
      rewrite OrdersEx.Nat_as_OT.sub_diag in Heval.
      cbn in Heval.
      rewrite Heval; try (solve_length q).
      apply Z.div_small.

      match goal with
      | |- 0 <= ?x mod _ < _ => assert (0 <= x) as Hpos
      end.
      rewrite Hqeval.
      solve_ineq.
      apply canonical_pos.
      canonical_app q.
      canonical_app (q_lo ++ [q_hi1]).
      rewrite <-app_assoc in H2.
      solve_hi.
      match goal with
      | |- 0 <= ?x mod _ < ?y => assert (x < y) as Hbound
      end.

      rewrite OrdersEx.Z_as_OT.lt_sub_lt_add_r.
      replace (S (length q_lo)) with n by (solve_length q).
      solve_ineq.
      etransitivity.
      rewrite Heqcoef.
      apply OrdersEx.Z_as_OT.mul_lt_mono_nonneg.
      solve_ineq.
      rewrite Heqcoef in coef_small.
      eauto.
      solve_hi.
      eauto.
      unfold up_bound.
      weight_comp.
      rewrite <-OrdersEx.Z_as_OT.pow_mul_r.
      apply OrdersEx.Z_as_OT.pow_lt_mono_r.
      lia.
      lia.
      replace (length q_lo) with (n-1)%nat by (solve_length q).
      simpl.
      break_match; lia.
      unfold machine_wordsize.
      replace (64 / 4) with 16 by reflexivity.
      lia.
      lia.
      apply canonical_eval_bounded.
      canonical_app p.
      replace n with (length lo) by (solve_length p).
      auto.

      split;
        rewrite Z.mod_small;
        auto;
        split;
        auto;
        etransitivity;
        eauto;
        apply weight_mono'.
      lia.
    Qed.

    Lemma reduce_second_correct : forall p lo hi,
        p = lo ++ [hi] ->
        canonical_repr (S n) p ->
        hi < up_bound ->
        let q := reduce1 base s c (S n) (S n) p in
        (Positional.eval weight (S n) p) mod (s - Associational.eval c)
        = (Positional.eval weight (S n) q) mod (s - Associational.eval c).
    Proof.
      intros.
      pose proof (value_reduce_second _ _ _ H H0 H1) as Hval.
      unfold q in *.
      rewrite Hval.
      rewrite H.
      rewrite eval_snoc_S.
      autorewrite with push_eval zsimplify_const.
      cbn [fst snd].
      apply adjust_s_finished' in solinas_property.
      rewrite solinas_property.
      cbn [fst].
      rewrite Z.mul_comm with (m:=Associational.eval c) (n:=(weight n / s)).
      rewrite (Z.add_comm _ (eval weight n lo)).
      rewrite <-Z.mul_assoc.
      rewrite <-reduction_rule.
      apply Z.elim_mod.
      rewrite Z.add_cancel_l.

      rewrite Z.mul_assoc.
      rewrite <-Z_div_exact_2.
      lia.
      lia.
      pose proof (adjust_s_invariant (S (S (S n))) s) as Hinv.
      rewrite solinas_property in Hinv.
      cbn [fst] in Hinv.
      apply Hinv.
      lia.
      lia.
      lia.
      solve_length p.
    Qed.

    Lemma reduce_third_canonical : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        (canonical_repr (S n) p) ->
        hi < up_bound ->
        let q := reduce1 base s c (S n) (S n) p in
        let r := reduce1 base s c (S n) n q in
        canonical_repr n r.
    Proof.
      intros.
      pose proof (reduce_second_canonical _ _ _ H H1 H0) as Hcanon.
      fold q in Hcanon.
      assert (Hcanon' := Hcanon).
      unfold canonical_repr in Hcanon'.
      destruct Hcanon' as [ Hlen _ ].
      assert (exists q_lo q_hi1 q_hi2, q = q_lo ++ [q_hi1] ++ [q_hi2]) as Hq.
      { pose proof (break_list_last q) as Hd1.
        destruct Hd1 as [ Hd1 | Hd1 ].
        rewrite Hd1 in Hlen.
        cbn in Hlen.
        lia.
        destruct Hd1 as [ q' Hd1 ].
        destruct Hd1 as [ q_hi2 Hd1].

        pose proof (break_list_last q') as Hd2.
        destruct Hd2 as [ Hd2 | Hd2 ].
        subst q'.
        rewrite Hd1 in Hlen.
        cbn in Hlen.
        lia.
        destruct Hd2 as [ q_lo Hd2 ].
        destruct Hd2 as [ q_hi1 Hd2 ].
        rewrite Hd2 in Hd1.
        rewrite <-app_assoc in Hd1.
        eauto. }
      destruct Hq as [ q_lo Hq ].
      destruct Hq as [ q_hi1 Hq ].
      destruct Hq as [ q_hi2 Hq ].

      pose proof (reduce_second _ _ _ H H0 H1 _ _ _ Hq).
      rewrite app_assoc in Hq.
      intuition.
      (* q_hi1 = 0, q_hi2 = 1 *)
      subst q_hi1 q_hi2.
      unfold canonical_repr.
      split.
      unfold r, reduce1.
      rewrite Rows.flatten_correct.
      cbn [fst].
      auto with push_length.
      auto.
      intros.
      eapply Rows.length_from_associational; eassumption.

      unfold r, reduce1.
      rewrite Rows.flatten_correct.
      cbn [fst].
      rewrite Partition.eval_partition.
      f_equal.
      apply Z.mod_small_sym.

      rewrite Rows.eval_from_associational.
      rewrite value_sat_reduce.
      apply adjust_s_finished' in solinas_property.
      rewrite solinas_property.
      autorewrite with push_eval zsimplify_const.
      cbn [fst snd].
      unfold to_associational.
      rewrite seq_snoc.
      rewrite map_app.
      rewrite Nat.add_0_l; cbn [map].
      rewrite Hq.
      rewrite combine_snoc.
      rewrite fst_split_app, snd_split_app.
      autorewrite with push_eval.
      destruct (split_p _ _ _ Hq Hcanon) as [Hsplit1 Hsplit2].
      rewrite Hsplit1, Hsplit2.
      cbn [fst snd].
      autorewrite with push_eval zsimplify_const.
      destruct n eqn:En; try lia.
      rewrite seq_snoc.
      rewrite map_app.
      cbn.
      rewrite combine_snoc.
      rewrite eval_app.
      autorewrite with push_eval zsimplify_const.
      split.

      solve_ineq.
      apply canonical_pos.
      canonical_app q.
      canonical_app (q_lo ++ [0]).
      replace n0 with (length q_lo) by (solve_length q).
      auto.
      etransitivity.
      solve_ineq.
      eauto.
      apply canonical_eval_bounded.
      canonical_app q.
      canonical_app (q_lo ++ [0]).
      replace n0 with (length q_lo) by (solve_length q).
      auto.
      apply reduce_in_range.
      vm_compute; auto.
      rewrite map_length, seq_length.
      solve_length q.
      rewrite map_length, seq_length.
      solve_length q.
      lia.
      lia.
      auto.
      lia.
      auto.
      auto.
      eapply Rows.length_from_associational; eassumption.

      (* q_hi2 = 0 *)
      subst q_hi2.
      split.
      unfold r, reduce1.
      rewrite Rows.flatten_correct.
      cbn [fst].
      auto with push_length.
      auto.
      intros.
      eapply Rows.length_from_associational; eassumption.

      unfold r, reduce1.
      rewrite Rows.flatten_correct.
      cbn [fst].
      rewrite Partition.eval_partition.
      f_equal.
      apply Z.mod_small_sym.

      rewrite Rows.eval_from_associational.
      rewrite value_sat_reduce.
      apply adjust_s_finished' in solinas_property.
      rewrite solinas_property.
      autorewrite with push_eval zsimplify_const.
      cbn [fst snd].
      unfold to_associational.
      rewrite seq_snoc.
      rewrite map_app.
      rewrite Nat.add_0_l; cbn [map].
      rewrite Hq.
      rewrite combine_snoc.
      rewrite fst_split_app, snd_split_app.
      autorewrite with push_eval.
      destruct (split_p _ _ _ Hq Hcanon) as [Hsplit1 Hsplit2].
      rewrite Hsplit1, Hsplit2.
      cbn [fst snd].
      autorewrite with push_eval zsimplify_const.
      cbn [snd].

      split.
      solve_ineq.
      apply canonical_pos.
      canonical_app q.
      replace n with (length (q_lo ++ [q_hi1])) by (solve_length q).
      auto.
      apply canonical_eval_bounded.
      canonical_app q.
      replace n with (length (q_lo ++ [q_hi1])) by (solve_length q).
      auto.
      rewrite map_length.
      rewrite seq_length.
      solve_length q.
      lia.
      lia.
      auto.
      lia.
      auto.
      auto.
      intros.
      eapply Rows.length_from_associational; eassumption.
    Qed.

    Lemma value_reduce_third : forall (q : list Z) q_lo q_hi1 q_hi2,
        q = q_lo ++ [q_hi1] ++ [q_hi2] ->
        canonical_repr (S n) q ->
        (q_hi2 = 1 /\ q_hi1 = 0) \/ (q_hi2 = 0) ->
        let r := reduce1 base s c (S n) n q in
        let s' := fst (Saturated.Rows.adjust_s weight (S (S (S n))) s) in
        let coef := Associational.sat_mul_const base [(1, s'/s)] c in
        eval weight n r = Associational.eval coef * q_hi2 + eval weight n (q_lo ++ [q_hi1]).
    Proof.
      intros.
      unfold reduce1 in *.
      unfold r, coef, s'.
      rewrite app_assoc in H.
      rewrite H.
      rewrite Rows.flatten_mod, Rows.eval_from_associational, value_sat_reduce.

      unfold to_associational.
      rewrite seq_snoc.
      rewrite map_app.
      rewrite Nat.add_0_l; cbn [map].
      rewrite combine_snoc.
      rewrite fst_split_app, snd_split_app.
      autorewrite with push_eval zsimplify_const.
      apply adjust_s_finished' in solinas_property.
      rewrite solinas_property.
      cbn [fst snd]; autorewrite with zsimplify_const.
      pose proof (split_p _ _ _ H H0) as Hsplit.
      destruct Hsplit as [ Hhi Hlo ].
      rewrite Hhi, Hlo.
      cbn [fst snd]; autorewrite with push_eval zsimplify_const; cbn [snd].

      destruct n eqn:En; try lia.
      rewrite seq_snoc, map_app.
      rewrite Nat.add_0_l; cbn [map].
      rewrite combine_snoc.
      rewrite eval_app.
      rewrite <-En.
      autorewrite with push_eval.
      rewrite En.
      cbn [fst snd].
      autorewrite with zsimplify_const.
      rewrite eval_snoc_S.

      apply Z.mod_small.
      assert (Hmach : 0 < machine_wordsize) by lia.
      apply BYInv.eval_bound with (n:=n0) (f:=q_lo) in Hmach.
      unfold eval, to_associational in Hmach.
      destruct H1.

      (* q_hi1 = 0, q_hi2 = 1 *)
      destruct H1.
      subst q_hi1.
      autorewrite with zsimplify_const.
      intuition.
      solve_ineq.
      apply canonical_pos.
      canonical_app q.
      canonical_app (q_lo ++ [0]).
      subst_canon q.
      etransitivity.
      solve_ineq.
      adjust_ineq coef_small.
      lia.
      apply canonical_eval_bounded.
      canonical_app q.
      canonical_app (q_lo ++ [0]).
      subst_canon q.

      apply reduce_in_range.
      subst q_hi2.
      weight_comp.
      unfold up_bound.
      vm_compute.
      auto.
      lia.
      lia.

      (* q_hi2 = 0 *)
      subst q_hi2.
      autorewrite with zsimplify_const.
      erewrite <-eval_snoc; try reflexivity.
      intuition.
      apply canonical_pos.
      canonical_app q.
      subst_canon q.
      apply canonical_eval_bounded.
      canonical_app q.
      subst_canon q.
      solve_length q.
      eapply canonical_iff.
      canonical_app q.
      canonical_app (q_lo ++ [q_hi1]).
      eauto.
      solve_length q.
      solve_length q.
      rewrite map_length.
      rewrite seq_length.
      solve_length q.
      lia.
      rewrite map_length.
      rewrite seq_length.
      solve_length q.
      lia.
      auto.
      lia.
      auto.
      eapply Rows.length_from_associational; eauto.
    Qed.

    Lemma reduce_third_correct : forall (p : list Z) lo hi,
        p = lo ++ [hi] ->
        (canonical_repr (S n) p) ->
        hi < up_bound ->
        let q := reduce1 base s c (S n) (S n) p in
        let r := reduce1 base s c (S n) n q in
        (Positional.eval weight (S n) p) mod (s - Associational.eval c)
        = (Positional.eval weight n r) mod (s - Associational.eval c).
    Proof.
      intros.
      pose proof (reduce_second_canonical _ _ _ H H1 H0) as Hcanon.
      fold q in Hcanon.
      assert (Hcanon' := Hcanon).
      unfold canonical_repr in Hcanon'.
      destruct Hcanon' as [ Hlen _ ].
      assert (exists q_lo q_hi1 q_hi2, q = q_lo ++ [q_hi1] ++ [q_hi2]) as Hq.
      { pose proof (break_list_last q) as Hd1.
        destruct Hd1 as [ Hd1 | Hd1 ].
        rewrite Hd1 in Hlen.
        cbn in Hlen.
        lia.
        destruct Hd1 as [ q' Hd1 ].
        destruct Hd1 as [ q_hi2 Hd1].

        pose proof (break_list_last q') as Hd2.
        destruct Hd2 as [ Hd2 | Hd2 ].
        subst q'.
        rewrite Hd1 in Hlen.
        cbn in Hlen.
        lia.
        destruct Hd2 as [ q_lo Hd2 ].
        destruct Hd2 as [ q_hi1 Hd2 ].
        rewrite Hd2 in Hd1.
        rewrite <-app_assoc in Hd1.
        eauto. }
      destruct Hq as [ q_lo Hq ].
      destruct Hq as [ q_hi1 Hq ].
      destruct Hq as [ q_hi2 Hq ].

      pose proof (reduce_second _ _ _ H H0 H1 _ _ _ Hq) as Hqhi.
      rewrite app_assoc in Hq.
      etransitivity.
      eapply reduce_second_correct; eauto.

      unfold r, q.
      rewrite value_reduce_third with (q_lo:=q_lo) (q_hi1:=q_hi1) (q_hi2:=q_hi2).
      autorewrite with push_eval zsimplify_const.
      erewrite adjust_s_finished'; eauto.
      cbn [fst snd].
      rewrite Z.mul_comm with (m:=Associational.eval c) (n:=(weight n / s)).
      rewrite Z.add_comm.
      rewrite <-Z.mul_assoc.
      rewrite <-reduction_rule.
      apply Z.elim_mod.
      fold q.
      rewrite Hq.
      rewrite eval_snoc_S.
      rewrite Z.add_cancel_l.

      rewrite Z.mul_assoc.
      rewrite <-Z_div_exact_2.
      lia.
      lia.
      pose proof (adjust_s_invariant (S (S (S n))) s) as Hinv.
      erewrite adjust_s_finished' in Hinv; eauto.
      cbn [fst] in Hinv.
      apply Hinv.
      lia.
      lia.
      solve_length q.
      lia.
      lia.
      fold q.
      rewrite Hq.
      rewrite app_assoc.
      auto.
      auto.
      lia.
    Qed.

  End __.

  Section test_reduce_full.

    Context (machine_wordsize := 64)
            (up_bound := 2 ^ (machine_wordsize / 4)).


    Definition is_bounded_by0 r v
      := ((lower r%zrange <=? v) && (v <=? upper r%zrange)).
    Fail Compute ltac:(let r := Reify (is_bounded_by0) in exact r).
    Definition is_bounded_by2 r v
      := (let '(v1, v2) := v in is_bounded_by0 (fst r) v1 && is_bounded_by0 (snd r) v2).
    Definition is_bounded_by0o r
      := (match r with Some r' => fun v' => is_bounded_by0 r' v' | None => fun _ => true end).
    Definition is_bounded_by bounds ls
      := (fold_andb_map (fun r v'' => is_bounded_by0o r v'') bounds ls).
    Fail Compute ltac:(let r := Reify (is_bounded_by) in exact r).

    Definition fold_andb ls :=
      fold_right andb true ls.
    Definition dual_map {A B : Type} (f : A -> B -> bool) (l1 : list A) (l2 : list B) :=
      map (fun x => (f (fst x) (snd x))) (combine l1 l2).
    Definition fold_andb_map' {A B : Type} (f : A -> B -> bool) (ls1 : list A) (ls2 : list B) :=
      fold_andb (dual_map f ls1 ls2).
    Succeed Compute ltac:(let r := Reify (@fold_andb_map' zrange Z) in exact r).
    Definition is_bounded_by' bounds ls
      := (fold_andb_map' (fun r v'' => is_bounded_by0o r v'') bounds ls).
    Fail Compute ltac:(let r := Reify (is_bounded_by') in exact r).


    Definition reduce_full base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) (S n) p in
      let bound := Some r[0 ~> 2^machine_wordsize - 1]%zrange in
      let bounds := repeat bound n ++ [Some r[0 ~> up_bound - 1]%zrange ] in
      if (is_bounded_by' bounds r1) then
        let r2 := reduce1 base s c (S n) (S n) r1 in
        let r3 := reduce1 base s c (S n) (n) r2 in
        r3
      else r1.
    Let s := 2^255.
    Let c := [(1, 19)].
    Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
    Let m : nat := 2 * n.
    Let w : nat -> Z := weight machine_wordsize 1.
    Let base : Z := 2 ^ machine_wordsize.
    Fail Compute ltac:(let n := (eval cbv in n) in
                       let r := Reify (reduce_full base s c n) in
                       exact r).


    Definition tmp r :=
      let '(x, y) := r in (x + y).
    Compute ltac:(let r := Reify (@combine Z Z) in exact r).
    Print IdentifiersBasicGENERATED.Compilers.ident.
    Locate IdentifiersBasicGENERATED.Compilers.ident.

    Search "zrange" "cast".
    Locate ZRange.type.base.option.is_bounded_by.
    Compute IdentifiersBasicGENERATED.Compilers.ident
                     (type.base
                        (base.type.type_base
                           IdentifiersBasicGENERATED.Compilers.zrange) ->
                      type.base
                        (base.type.type_base
                           IdentifiersBasicGENERATED.Compilers.Z) ->
                      type.base
                        (base.type.type_base
                           IdentifiersBasicGENERATED.Compilers.Z)).

    Let r : zrange := {| lower := 1; upper := 2 |}.

    Definition test (r : zrange) :=
      match r with
      | {| lower := _; upper := _ |} => r
      end.
    Fail Compute (ltac:(let r := Reify test in
                        exact r)).

    Compute (ltac:(let r := Reify r in
                   exact r)).
    (* Search IdentifiersBasicGENERATED.Compilers.zrange. *)

  End test_reduce_full.

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

    Let bounds := repeat bound n ++ [Some r[0 ~> (2^(machine_wordsize/4) - 1)]%zrange].

    Fail Time Compute
         Show.show
         (Pipeline.BoundsPipelineToString
            "fiat" "mul"
            false
            false
            None
            possible_values
            machine_wordsize
            ltac:(let n := (eval cbv in n) in
                  let r := Reify (reduce_full base s c n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (2*n)), tt)
                   (Some (repeat bound (n)))
                   (None, tt)
                   (None)
           : Pipeline.ErrorT _).

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
                  let r := Reify (reduce1 base s c (2*n) (S n)) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (2*n)), tt)
                   (Some bounds)
                   (None, tt)
                   (None)
           : Pipeline.ErrorT _).

  End compile.

End solinas_reduction.
