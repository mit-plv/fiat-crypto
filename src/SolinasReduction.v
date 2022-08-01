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

Require Import Crypto.Util.CPSUtil.
Require Import Crypto.Util.CPSNotations.
Local Open Scope cps_scope.
Notation "x' <- v ; C" := (v (fun x' => C)) (only parsing).

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
Local Instance : assembly_hints_lines_opt := [].
Local Instance : ignore_unique_asm_names_opt := false.
Local Instance : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.
Local Existing Instance default_language_naming_conventions.
Local Existing Instance default_documentation_options.
Local Instance : package_name_opt := None.
Local Instance : class_name_opt := None.

Local Existing Instance default_output_options.

Module solinas_reduction.

  Import Crypto.Arithmetic.Saturated.

  Module tmp.

    Section __.

      Context (machine_wordsize := 64)
              (weight := uweight machine_wordsize)
              (up_bound := 2 ^ (machine_wordsize / 4))
              {wprops : @weight_properties weight}.

      Definition dual_map {A B : Type} (f : A -> B -> bool) (l1 : list A) (l2 : list B) :=
        map (fun x => (f (fst x) (snd x))) (combine l1 l2).
      Definition fold_andb_map' {A B : Type} (f : A -> B -> bool) (ls1 : list A) (ls2 : list B) :=
        fold_right andb true (dual_map f ls1 ls2).
      Definition is_bounded_by bounds ls :=
        fold_andb_map' (fun r v'' => (fst r <=? v'') && (v'' <=? snd r)) bounds ls.

      Definition sat_reduce base s c n (p : list (Z * Z)) :=
        let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
        let lo_hi := Associational.split s' p in
        let coef := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
        let hi := Saturated.Associational.sat_mul_const base coef (snd lo_hi) in
        let r := (fst lo_hi) ++ hi in
        r.

      Definition reduce1_cps {T} base s c n m (p : list Z) (f : list Z -> T) :=
        let p_a := Positional.to_associational weight n p in
        let r_a := sat_reduce base s c n p_a in
        let r_rows := Saturated.Rows.from_associational weight m r_a in
        let r_flat := Saturated.Rows.flatten weight m r_rows in
        let bound := (0, 2^machine_wordsize - 1) in
        if (is_bounded_by (repeat bound n) p) then
          f (fst r_flat)
        else
          f (add_to_nth 0 (weight (m) * snd r_flat) (fst r_flat)).
      Check reduce1_cps.

      Definition reduce_full_cps {T} base s c n (p : list Z) (f : list Z -> T):=
        (r1 <- reduce1_cps base s c (2*n) (S n) p;
         (let bound := (0, 2^machine_wordsize) in
          if (is_bounded_by (repeat bound (S n)) r1) then
            (r2 <- reduce1_cps base s c (S n) (S n) r1;
             reduce1_cps base s c (S n) n r2 f)
          else
            f r1)).
      Check reduce_full_cps.

      Definition mul_no_reduce_cps {T} base n (p q : list Z) (f : list Z -> T):=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      let bound := (0, 2^machine_wordsize - 1) in
      if (is_bounded_by (repeat bound n) p && is_bounded_by (repeat bound n) q) then
        f (fst pq)
      else
        f (add_to_nth 0 (weight (2 * n) * snd pq) (fst pq)).
      Check mul_no_reduce_cps.

      Definition mulmod_cps {T} base s c n (p q : list Z) (f : list Z -> T) :=
        (mul <- mul_no_reduce_cps base n p q;
         reduce_full_cps base s c n mul f).
      Check mulmod_cps.

      Definition mulmod base s c n (p q : list Z) :=
        mulmod_cps (T := list Z) base s c n p q (id).
      Check mulmod.

      Definition x base s c n p q := ltac:(let y := (eval cbv beta delta [mulmod mulmod_cps mul_no_reduce_cps reduce_full_cps reduce1_cps id] in (mulmod base s c n p q)) in exact y).
      Print x.
      Check x.

    End __.

    Section __.

      Let s := 2^255.
      Let c := [(1, 19)].
      Let machine_wordsize := 64.
      Let n : nat := Z.to_nat (Qceiling (Z.log2_up s / machine_wordsize)).
      Let m : nat := 2 * n.
      Let w : nat -> Z := weight machine_wordsize 1.
      Let up_bound := 2 ^ (machine_wordsize / 4).
      Let base : Z := 2 ^ machine_wordsize.

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

      Let bound := Some r[0 ~> (2^machine_wordsize - 1)]%zrange.

      Time Compute
           Show.show
           (Pipeline.BoundsPipelineToString
              "fiat_p25519_" "fiat_p25519_mul"
              false
              false
              None
              possible_values
              machine_wordsize
              ltac:(let n := (eval cbv in n) in
                    let r := Reify (x base s c n) in
                    exact r)
                     (fun _ _ => [])
                     (Some (repeat bound (n)), (Some (repeat bound n), tt))
                     (Some (repeat bound (n)))
                     (None, (None, tt))
                     (None)
             : Pipeline.ErrorT _).

    End __.

  End tmp.

  Section __.

    Context (machine_wordsize := 64)
            (weight := uweight machine_wordsize)
            (up_bound := 2 ^ (machine_wordsize / 4))
            {wprops : @weight_properties weight}.

    Ltac weight_comp :=
      unfold weight, uweight, ModOps.weight, machine_wordsize;
      try rewrite !Z.div_1_r;
      try rewrite !Z.opp_involutive;
      try rewrite !Nat2Z.inj_succ;
      try rewrite !OrdersEx.Z_as_OT.mul_succ_r;
      try rewrite !OrdersEx.Z_as_OT.pow_add_r;
      autorewrite with zsimplify_const;
      ring_simplify.

    Ltac solve_ineq :=
      repeat
        match goal with
        | |- 0 <= _ + _ => apply OrdersEx.Z_as_OT.add_nonneg_nonneg
        | |- 0 < _ * _ => apply OrdersEx.Z_as_OT.mul_pos_pos
        | |- 0 <= _ * _ => apply OrdersEx.Z_as_OT.mul_nonneg_nonneg
        | |- 0 <= _ / _ => apply OrdersEx.Z_as_OT.div_pos
        | |- _ / _ < _ => apply OrdersEx.Z_as_OT.div_lt_upper_bound

        | |- _ + ?x < _ + ?x => apply OrdersEx.Z_as_OT.add_lt_mono_r
        | |- _ + _ < _ => apply OrdersEx.Z_as_OT.add_lt_mono
        | |- _ + _ <= _ => apply OrdersEx.Z_as_OT.add_le_mono
        | |- _ - ?x < _ - ?x => rewrite <-OrdersEx.Z_as_OT.sub_lt_mono_r
        | |- _ - ?x <= _ - ?x => rewrite <-OrdersEx.Z_as_OT.sub_le_mono_r

        | _ => apply Z.mod_small
        | |- _ mod (?x * ?y) < (?y * ?x) => rewrite Z.mul_comm with (n:=x)
        | _ => apply OrdersEx.Z_as_OT.mod_pos_bound
        | [ |- 0 <= _ mod _ ] => apply Z_mod_nonneg_nonneg
        | [ |- 0 <= weight _ ] => apply OrdersEx.Z_as_OT.lt_le_incl; auto

        | _ => split
        | _ => lia
        end.

    Ltac le_lt :=
      (rewrite Le.Z.le_sub_1_iff || rewrite <-Le.Z.le_sub_1_iff).

    Hint Rewrite Nat.add_0_l : const_simpl.
    Hint Rewrite Nat.add_0_r : const_simpl.
    Hint Rewrite Z.add_0_l : const_simpl.
    Hint Rewrite Z.add_0_r : const_simpl.
    Lemma S_sub_1 : forall (n : nat),
        (n > 0)%nat ->
        S (n - 1)%nat = n.
    Proof. lia. Qed.
    Hint Rewrite S_sub_1 using lia : const_simpl.
    Lemma Sn_sub_n : forall (n : nat),
        (S n - n)%nat = 1%nat.
    Proof. lia. Qed.
    Hint Rewrite Sn_sub_n : const_simpl.
    Lemma n2_sub : forall (n : nat),
        (2 * n - n)%nat = n.
    Proof. lia. Qed.
    Hint Rewrite n2_sub : const_simpl.
    Ltac const_simpl :=
      autorewrite with const_simpl in *.

    Hint Rewrite eval_cons using auto : push_eval.
    Hint Rewrite Associational.eval_sat_mul using lia : push_eval.
    Hint Rewrite Associational.eval_sat_mul_const using lia : push_eval.
    Hint Rewrite eval_split using auto : push_eval.
    Hint Rewrite Rows.eval_from_associational using (auto || lia) : push_eval.
    Hint Rewrite Rows.flatten_mod using (eauto using Rows.length_from_associational) : push_eval.
    Hint Rewrite Rows.flatten_correct using (eauto using Rows.length_from_associational) : push_eval.
    Hint Rewrite eval_add_to_nth using auto : push_eval.

    Hint Rewrite @nil_length0 cons_length app_length seq_length map_length firstn_length @skipn_length length_partition length_add_to_nth : push_length.
    Hint Rewrite (@ListUtil.length_snoc) : push_length.
    Hint Rewrite Rows.length_flatten using (eauto using Rows.length_from_associational) : push_length.

    Hint Rewrite map_nil map_cons map_app map_map in_map_iff : push_misc.
    Hint Rewrite @combine_app_samelength : push_misc.
    Hint Rewrite @combine_nil_r @combine_cons : push_misc.
    Hint Rewrite @fold_right_cons fold_right_app : push_misc.
    Hint Rewrite seq_add : push_misc.
    Hint Rewrite split_app : push_misc.
    Hint Rewrite @nth_default_cons_S : push_misc.
    Hint Rewrite @firstn_map firstn_seq firstn_app : push_misc.
    Hint Rewrite @skipn_app @skipn_0 : push_misc.
    Hint Rewrite @fst_pair @snd_pair : push_misc.
    Hint Rewrite app_nil_r app_nil_l : push_misc.
    Hint Rewrite Nat.sub_diag : push_misc.

    Hint Resolve in_or_app : core.
    Hint Resolve in_eq : core.
    Hint Resolve in_cons : core.

    Hint Unfold eval : unfold_eval.
    Hint Unfold Associational.eval : unfold_eval.
    Hint Unfold to_associational : unfold_eval.

    Ltac push :=
      autorewrite with push_eval push_length push_misc zsimplify_const;
      auto.

    Ltac push' H :=
      autorewrite with push_eval push_length push_misc zsimplify_const in H;
      auto.

    Lemma seq_double : forall n,
        seq 0 (2 * n) = seq 0 n ++ seq n n.
    Proof.
      intros n; replace (2*n)%nat with (n+n)%nat; push; lia.
    Qed.
    Hint Rewrite seq_double : push_misc.

    Lemma map_weight_seq : forall m p,
        map weight (seq 0 p) = map (fun t => t / (weight m)) (map weight (seq m p)).
    Proof.
      induction m; intros; push.
      erewrite map_ext.
      eauto.
      intros.
      cbn.
      rewrite Z.div_1_r.
      lia.

      rewrite IHm.
      rewrite <-seq_shift.
      push.
      apply map_ext_Forall.
      rewrite Forall_forall.
      intros.
      rewrite in_seq in H.
      weight_comp; try lia.
      rewrite <-!OrdersEx.Z_as_OT.pow_add_r; try lia.
      rewrite <-!OrdersEx.Z_as_OT.pow_sub_r; try lia.
      f_equal.
      lia.
    Qed.
    Hint Rewrite <-map_weight_seq : push_misc.

    Lemma seq_shift_1 : forall len,
        map S (seq 0 len) = seq 1 len.
    Proof.
      intros.
      apply seq_shift.
    Qed.
    Hint Rewrite <-seq_shift_1 : push_misc.

    (* SECTION CANONICAL_REPR *)

    Definition canonical_repr n (p : list Z) : Prop :=
      length p = n /\
        p = Partition.partition weight n (Positional.eval weight n p).

    Lemma canonical_pos n : forall (p : list Z),
        canonical_repr n p ->
        0 <= eval weight n p.
    Proof using wprops.
      intros;
        repeat match goal with
               | H : canonical_repr _ _ |- _ =>
                   unfold canonical_repr in H;
                   destruct H as [ _ H ];
                   rewrite H;
                   rewrite Partition.eval_partition
               | _ => apply Z.mod_pos_bound
               | _ => auto
               end.
    Qed.

    Lemma canonical_bounded n : forall (p : list Z),
        canonical_repr n p ->
        forall x, In x p -> 0 <= x < 2 ^ machine_wordsize.
    Proof using wprops.
      intros;
        repeat multimatch goal with
               | H : canonical_repr ?n ?p |- _ =>
                   pose proof (canonical_pos n p H);
                   cbv [canonical_repr Partition.partition] in H;
                   destruct H as [ Hlen Hpart ]
               | H1 : In _ ?p, H2 : ?p = _ |- _ =>
                   rewrite H2 in H1;
                   autorewrite with push_misc in H1
               | H : context[exists _, _] |- _ => destruct H
               | H : _ = ?x |- 0 <= ?x => rewrite <-H
               | H : _ = ?x |- ?x < _ => rewrite <-H
               | _ => unfold weight; rewrite uweight_S; fold weight
               | _ => solve_ineq
               | _ => progress intuition
               | _ => auto || lia
               end.
    Qed.

    Lemma canonical_iff p n :
      canonical_repr n p <->
        length p = n /\
          forall x, In x p -> 0 <= x < 2 ^ machine_wordsize.
    Proof using wprops.
      split; intros;
        repeat multimatch goal with
               | H : length _ = _ |- _ => rewrite H
               | |- length _ = _ => unfold canonical_repr in *
               | |- _ = Partition.partition _ _ _ => unfold canonical_repr in *
               | |- canonical_repr _ _ => unfold canonical_repr
               | _ => eapply canonical_bounded
               | _ => progress intuition
               | _ => eauto || lia
               end.
      apply uweight_partition_unique.
      lia.
      lia.
      intros.
      rewrite Le.Z.le_sub_1_iff.
      auto.
    Qed.

    Lemma canonical_cons n a p:
      canonical_repr (S n) (a :: p) ->
      canonical_repr n p.
    Proof.
      intros.
      rewrite canonical_iff in *.
      intuition;
        repeat multimatch goal with
               | H : context[_ <= _ < _] |- _ => apply H
               | _ => cbn
               | _ => auto
               end.
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
      rewrite canonical_iff in *; intuition;
        repeat multimatch goal with
               | H : context[_ <= _ < _] |- _ => apply H
               | H : ?x = _ ++ _ |- In _ ?x => rewrite H
               | _ => cbn
               | _ => auto
               end.
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
      rewrite canonical_iff in *; intuition;
        repeat multimatch goal with
               | H : context[_ <= _ < _] |- _ => apply H
               | H : ?x = _ ++ _ |- In _ ?x => rewrite H
               | _ => cbn
               | _ => auto
               end.
    Qed.

    Lemma fold_right_add : forall l x,
        fold_right Z.add x l = x + fold_right Z.add 0 l.
    Proof.
      intros l x.
      induction l as [ | l' IHl ]; cbn; try rewrite IHl; lia.
    Qed.

    Definition eval_weight_P p := forall a b,
        Associational.eval (combine (map (fun x0 : nat => weight (S x0)) (seq a b)) p) =
          weight 1 * Associational.eval (combine (map weight (seq a b)) p).

    Lemma eval_weight_S' : forall p,
        eval_weight_P p.
    Proof.
      apply (ListAux.list_length_induction Z).
      unfold eval_weight_P.
      intros l1 H n.
      pose proof (@break_list_last Z l1).
      cbv [eval_weight_P eval Associational.eval to_associational] in *.
      intuition;
        repeat multimatch goal with
               | H : context[exists _, _] |- _ => destruct H
               | _ => autorewrite with push_eval push_misc
               | _ => progress subst
               | _ => lia || auto
               end.

      destruct (b <=? length x)%nat eqn:E.
      rewrite Nat.leb_le in E.
      rewrite combine_truncate_r.
      rewrite combine_truncate_r with (xs:=map weight (seq n b)).
      push.
      apply H.
      push.
      rewrite Nat.min_l; lia.

      rewrite Nat.leb_gt in E.
      rewrite combine_truncate_l.
      rewrite combine_truncate_l with (xs:=map weight (seq n b)).
      autorewrite with push_length push_misc.
      rewrite Nat.min_l; [|lia].
      rewrite seq_snoc.
      autorewrite with push_misc.
      push.
      rewrite fold_right_add.
      rewrite fold_right_add with (x:=weight (n + Datatypes.length x) * x0).
      rewrite H.
      ring_simplify.
      unfold weight, machine_wordsize.
      rewrite uweight_S; [|lia].
      cbn; break_match; lia.
      push.
      push.
      push.
    Qed.

    Lemma eval_weight_S p n:
      eval (fun i : nat => weight (S i)) n p =
        (eval weight n p) * weight 1.
    Proof.
      cbv [eval to_associational].
      rewrite eval_weight_S'.
      lia.
    Qed.
    Hint Rewrite eval_weight_S : push_eval.

    Lemma eval_weight_S_gen p a b :
      Associational.eval (combine (map (fun x0 : nat => weight (S x0)) (seq a b)) p) =
        weight 1 * Associational.eval (combine (map weight (seq a b)) p).
    Proof.
      apply eval_weight_S'.
    Qed.
    Hint Rewrite eval_weight_S_gen : push_eval.

    Lemma canonical_eval_bounded n : forall (p : list Z),
        canonical_repr n p ->
        eval weight n p < weight n.
    Proof.
      intros p.
      generalize dependent n.
      induction p; intros; destruct n;
        repeat multimatch goal with
               | H : canonical_repr _ (_ :: _) |- _ =>
                   let H' := fresh "H" in
                   assert (H' := H);
                   pose proof (canonical_bounded _ _ H');
                   unfold canonical_repr in H';
                   apply canonical_cons in H
               | H : context[length _] |- _ => autorewrite with push_length in H; rewrite <-H
               | _ => push
               | _ => intuition
               | _ => ring_simplify
               | _ => auto || lia
               end.
      cbn; lia.
      le_lt.
      etransitivity.
      solve_ineq.
      le_lt.
      apply H1; auto.
      rewrite <-OrdersEx.Z_as_OT.mul_le_mono_pos_r; auto.
      le_lt; auto.
      ring_simplify.
      solve_ineq.
      rewrite H2.
      weight_comp; lia.
    Qed.

    Definition dual_map {A B : Type} (f : A -> B -> bool) (l1 : list A) (l2 : list B) :=
      map (fun x => (f (fst x) (snd x))) (combine l1 l2).
    Definition fold_andb_map' {A B : Type} (f : A -> B -> bool) (ls1 : list A) (ls2 : list B) :=
      fold_right andb true (dual_map f ls1 ls2).
    Definition is_bounded_by bounds ls :=
      fold_andb_map' (fun r v'' => (fst r <=? v'') && (v'' <=? snd r)) bounds ls.
    Hint Unfold is_bounded_by : core.
    Hint Unfold fold_andb_map' : core.
    Hint Unfold dual_map : core.

    Lemma canonical_is_bounded_by : forall n p,
        canonical_repr n p <->
          length p = n /\
            is_bounded_by (repeat (0, 2^machine_wordsize-1) n) p = true.
    Proof.
      intros.
      rewrite canonical_iff.
      autounfold.
      split.
      intuition.
      generalize dependent n.
      induction p; intros;
        repeat multimatch goal with
               | H : length _ = ?x |- _ => progress cbn in H; subst x
               | _ => apply andb_true_intro
               | _ => rewrite Z.leb_le
               | _ => rewrite Le.Z.le_sub_1_iff
               | _ => apply H1
               | _ => eapply IHp
               | _ => progress cbn || intuition
               | _ => progress intuition
               | _ => reflexivity || lia || auto
               | [ |- _ <= 18446744073709551615] => replace 18446744073709551615 with (18446744073709551616 - 1) by lia
               end.
      split.
      intuition.
      generalize dependent n.
      induction p; intros;
        repeat multimatch goal with
               | H : length _ = ?x |- _ => cbn in H; rewrite <-H in *
               | H : In _ _ |- _ => cbn in H
               | H : context[S _] |- _ => cbn in H
               | H : context[_ && _] |- _ => rewrite andb_true_iff in H
               | _ => progress cbn || intuition
               | _ => lia
               | _ => eapply IHp
               end.
    Qed.

    Lemma eval_is_bounded_by_pos n : forall p,
        is_bounded_by (repeat (0, 2 ^ machine_wordsize - 1) n) p = true ->
        0 <= eval weight n p.
    Proof using Type.
      intros.
      pose proof eval_weight_S as Heval.
      autounfold with * in *.
      generalize dependent n; induction p; intros; destruct n;
        repeat multimatch goal with
               | H : context[fold_right _ _ _] |- _ => cbn in H
               | _ => solve_ineq
               | _ => rewrite Heval
               | _ => push
               | _ => cbn
               | _ => intuition
               | _ => break_match
               | _ => lia
               end.
    Qed.

    Lemma eval_is_bounded_by n : forall p,
        is_bounded_by (repeat (0, 2 ^ machine_wordsize - 1) n) p = true ->
        0 <= eval weight n p < weight n.
    Proof.
      intros.
      split.
      apply eval_is_bounded_by_pos; auto.
      pose proof eval_weight_S as Heval.
      autounfold with * in *.
      generalize dependent n; induction p; intros; destruct n;
        repeat multimatch goal with
               | H : context[fold_right _ _ _] |- _ => progress cbn in H
               | H : context[_ && _] |- _ => rewrite andb_true_iff in H
               | H : context[_ <=? _] |- _ => rewrite Z.leb_le in H
               | _ => solve_ineq
               | _ => push
               | _ => rewrite Heval
               | _ => progress cbn || intuition
               | _ => lia || auto || reflexivity || discriminate
               end.
      le_lt.
      etransitivity.
      solve_ineq.
      break_match; eauto.
      apply OrdersEx.Z_as_OT.mul_le_mono_nonneg_r; try lia.
      le_lt.
      apply IHp; auto.
      weight_comp; unfold machine_wordsize; lia.
    Qed.
    Hint Resolve eval_is_bounded_by : ibb.

    Lemma is_bounded_by_cons1 : forall b bounds p' p,
        is_bounded_by (b :: bounds) (p' :: p) = true ->
        is_bounded_by bounds p = true.
    Proof.
      intros; autounfold in *; match goal with | H : _ |- _ => push' H end.
    Qed.
    Hint Resolve is_bounded_by_cons1 : ibb.

    Lemma is_bounded_by_cons2 : forall b bounds p' p,
        is_bounded_by (b :: bounds) (p' :: p) = true ->
        fst b <= p' <= snd b.
    Proof.
      intros; autounfold in *; match goal with | H : _ |- _ => push' H end.
    Qed.
    Hint Resolve is_bounded_by_cons2 : ibb.

    Lemma is_bounded_by_cons : forall b bounds p' p,
        is_bounded_by (b :: bounds) (p' :: p) = true ->
        is_bounded_by bounds p = true /\
          fst b <= p' <= snd b.
    Proof.
      intros; autounfold in *; match goal with | H : _ |- _ => push' H end.
    Qed.
    Hint Resolve is_bounded_by_cons : ibb.

    Lemma is_bounded_by_nth n : forall p bounds,
        is_bounded_by bounds p = true ->
        (n < length p)%nat ->
        (n < length bounds)%nat ->
        fst (nth_default (0,0) bounds n) <= nth_default 0 p n <= snd (nth_default (0,0) bounds n).
    Proof.
      intros.
      generalize dependent n.
      generalize dependent p.
      induction bounds as [ | b bounds IHbounds ];
        intros p ? n; destruct n; destruct p; intros;
        repeat multimatch goal with
               | H : _ |- _ => autorewrite with push_length in H
               | _ => apply IHbounds
               | _ => autorewrite with push_misc
               | _ => cbn
               | _ => eauto with ibb
               | _ => lia
               end.
    Qed.
    Hint Resolve is_bounded_by_nth : ibb.

    Lemma is_bounded_by_app_l : forall bound1 bound2 l1 l2,
        is_bounded_by (bound1 ++ bound2) (l1 ++ l2) = true ->
        length bound1 = length l1 ->
        is_bounded_by bound1 l1 = true.
    Proof.
      intros b1 b2 l1 l2 H H1.
      generalize dependent b1.
      generalize dependent b2.
      generalize dependent l2.
      induction l1 as [ | ? ? IHl1 ]; intros; destruct b1;
        repeat multimatch goal with
               | _ => autounfold in *
               | _ => eapply IHl1
               | _ => rewrite Z.leb_le
               | H : _ |- _ => rewrite <-!app_comm_cons in H; push' H
               | H : _ |- _ => rewrite andb_true_iff in H
               | _ => rewrite andb_true_iff
               | _ => intuition
               | _ => push
               | _ => lia
               | _ => eauto
               end.
    Qed.
    Hint Resolve is_bounded_by_app_l : ibb.

    Lemma fold_right_andb_default : forall d l,
        fold_right andb d l = true -> d = true.
    Proof.
      intros; induction l;
        repeat multimatch goal with
               | H : context[fold_right _ _ _] |- _ => push' H
               end.
    Qed.
    Hint Resolve fold_right_andb_default : core.

    Lemma is_bounded_by_app_r : forall bound1 bound2 l1 l2,
        is_bounded_by (bound1 ++ bound2) (l1 ++ l2) = true ->
        length bound1 = length l1 ->
        is_bounded_by bound2 l2 = true.
    Proof.
      intros b1 b2 l1 l2 H H1.
      generalize dependent b1.
      generalize dependent b2.
      generalize dependent l2.
      induction l1 as [ | ? ? IHl1 ];
        intros l2 b2 b1; [ | specialize (IHl1 l2 b2 b1)]; destruct b1;
        repeat multimatch goal with
               | _ => autounfold in *
               | _ => rewrite Z.leb_le
               | H : context[length _] |- _ => autorewrite with push_length in H
               | H : context[(_ :: _) ++ _] |- _ => rewrite <-!app_comm_cons in H; push' H
               | H : _ |- _ => rewrite andb_true_iff in H
               | _ => rewrite andb_true_iff
               | _ => intuition
               | _ => eauto
               | _ => discriminate
               end.
    Qed.

    Lemma is_bounded_by_loosen : forall l bound1 bound2,
        length bound1 = length bound2 ->
        is_bounded_by bound1 l = true ->
        fold_andb_map' (fun x y => (fst y <=? fst x) && (snd x <=? snd y)) bound1 bound2 = true ->
        is_bounded_by bound2 l = true.
    Proof.
      intros.
      generalize dependent bound1.
      generalize dependent bound2.
      autounfold.
      induction l as [ | ? ? IHl]; intros; destruct bound1; destruct bound2;
        repeat match goal with
               | H : context[length _] |- _ => progress autorewrite with push_length in H
               | H : context[_ :: _] |- _ => progress autorewrite with push_misc in H
               | _ => apply IHl
               | _ => rewrite Z.leb_le
               | H : _ |- _ => rewrite Z.leb_le in H
               | _ => rewrite andb_true_iff
               | H : _ |- _ => rewrite andb_true_iff in H
               | _ => progress intuition
               | _ => progress push
               | _ => lia
               | _ => eauto
               end.
    Qed.

    Lemma bounds_same : forall b,
        fold_andb_map' (fun x y => (fst y <=? fst x) && (snd x <=? snd y)) b b = true.
    Proof.
      intros.
      autounfold.
      induction b;
        repeat match goal with
               | _ => progress push
               | _ => rewrite andb_true_iff
               | _ => rewrite Z.leb_le
               | _ => progress intuition
               | _ => lia
               end.
    Qed.

    (* END SECTION CANONICAL_REPR *)

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

    Definition sat_reduce base s c n (p : list (Z * Z)) :=
      let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
      let lo_hi := Associational.split s' p in
      let coef := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let hi := Saturated.Associational.sat_mul_const base coef (snd lo_hi) in
      let r := (fst lo_hi) ++ hi in
      r.

    Lemma value_sat_reduce base s c n (p : list (Z * Z)) (basenz:base<>0):
      let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
      let coef := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let lo_hi := Associational.split s' p in
      Associational.eval (sat_reduce base s c n p) =
        Associational.eval coef * Associational.eval (snd lo_hi) + Associational.eval (fst lo_hi).
    Proof using Type.
      intros; cbv [sat_reduce] in *; cbv [s' lo_hi coef].
      autorewrite with push_eval; lia.
    Qed.
    Hint Rewrite value_sat_reduce : push_eval.

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

    Lemma eval_sat_reduce base s c fuel p :
      base <> 0
      -> s - Associational.eval c <> 0
      -> s <> 0
      -> Associational.eval (sat_reduce base s c fuel p) mod (s - Associational.eval c)
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

    Definition mul_no_reduce base n (p q : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      let bound := (0, 2^machine_wordsize - 1) in
      if (is_bounded_by (repeat bound n) p && is_bounded_by (repeat bound n) q) then
        fst pq
      else
        add_to_nth 0 (weight (2 * n) * snd pq) (fst pq).

    Definition reduce1 base s c n m (p : list Z) :=
      let p_a := Positional.to_associational weight n p in
      let r_a := sat_reduce base s c n p_a in
      let r_rows := Saturated.Rows.from_associational weight m r_a in
      let r_flat := Saturated.Rows.flatten weight m r_rows in
      let bound := (0, 2^machine_wordsize - 1) in
      if (is_bounded_by (repeat bound n) p) then
        fst r_flat
      else
        add_to_nth 0 (weight (m) * snd r_flat) (fst r_flat).

    Definition reduce_full base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) (S n) p in
      let bound := (0, 2^machine_wordsize - 1) in
      let bounds := repeat bound n ++ [(0, up_bound-1)] in
      if (is_bounded_by bounds r1) then
        let r2 := reduce1 base s c (S n) (S n) r1 in
        let r3 := reduce1 base s c (S n) (n) r2 in
        r3
      else add_to_nth 0 (weight n * nth_default 0 r1 n) (firstn n r1).

    Definition mulmod base s c n (p q : list Z) :=
      let prod := mul_no_reduce base n p q in
      let red := reduce_full base s c n prod in
      red.

    Hint Resolve length_partition : push_length.
    Hint Resolve Rows.length_from_associational : push_length.

    Lemma split_lt w l1 l2:
      (forall x, In x l1 -> 0 < x < w) ->
      split w (combine l1 l2) = (combine l1 l2, []).
    Proof.
      intros H.
      generalize dependent l2.
      induction l1; intros; destruct l2; push;
        match goal with
        | [ |- context[ ?x :: ?y ] ] => replace (x :: y) with ([x] ++ y) by auto
        end;
        specialize (IHl1 ltac:(auto));
        specialize (H a ltac:(auto));
        repeat multimatch goal with
               | |- context[_ mod _] => rewrite Z.mod_small
               | _ => rewrite IHl1
               | _ => push
               | _ => cbn
               | _ => lia
               | _ => auto
               | _ => break_match
               end.
    Qed.

    Lemma split_gt w l1 l2:
      (forall x, In x l1 -> x mod w = 0) ->
      split w (combine l1 l2) = ([], combine (map (fun t => t / w) l1) l2).
    Proof.
      intros.
      generalize dependent l2.
      induction l1; intros; destruct l2; push;
        match goal with
        | [ |- context[ ?x :: ?y ] ] => replace (x :: y) with ([x] ++ y) by eauto
        end;
        specialize (IHl1 ltac:(auto));
        specialize (H _ ltac:(auto));
        repeat multimatch goal with
               | _ => rewrite IHl1
               | _ => push
               | _ => cbn
               | _ => lia
               | _ => auto
               | _ => break_match
               end.
    Qed.

    Lemma weight_mono' x :
      weight x < weight (S x).
    Proof.
      weight_comp; lia.
    Qed.

    Lemma weight_mono'' x1 x2 :
      (x2 > 0)%nat
      -> weight x1 < weight (x2 + x1).
    Proof.
      intros H.
      induction H;
        repeat match goal with
               | _ => apply IHle
               | _ => apply weight_mono'
               | _ => etransitivity
               end.
    Qed.

    Lemma weight_mono x1 x2 :
      (x1 < x2)%nat ->
      weight x1 < weight x2.
    Proof.
      intros.
      replace x2%nat with ((x2 - x1) + x1)%nat by lia.
      apply weight_mono''; lia.
    Qed.

    Lemma weight_mono_le x1 x2 :
      (x1 <= x2)%nat ->
      weight x1 <= weight x2.
    Proof.
      intros H.
      apply le_lt_or_eq in H.
      intuition.
      pose proof (weight_mono x1 x2 ltac:(auto)); lia.
      subst; lia.
    Qed.

    Lemma map_seq_start : forall a b,
        map weight (seq a b) =
          map (fun t => t * weight a) (map weight (seq 0 b)).
    Proof.
      intros a b.
      induction b;
        repeat multimatch goal with
               | _ => rewrite IHb
               | _ => rewrite seq_snoc
               | _ => f_equal
               | _ => push
               | _ => cbn
               end.
      weight_comp.
      rewrite Nat2Z.inj_add.
      rewrite Z.mul_add_distr_l.
      rewrite Z.pow_add_r; lia.
    Qed.

    Lemma weight_dif_mono' : forall n,
        weight (S n) - weight n < weight (S (S n)) - weight (S n).
    Proof.
      intros.
      induction n.
      weight_comp; lia.
      cbv [weight].
      rewrite uweight_S; [ | lia].
      rewrite uweight_S with (n:=n) at 2; [ | lia].
      rewrite uweight_S with (n:=S (S n)); [ | lia].
      fold weight.
      rewrite <-!Z.mul_sub_distr_l.
      apply Zmult_lt_compat_l; lia.
    Qed.

    Lemma weight_dif_mono : forall n m,
        (n < m)%nat ->
        weight (S n) - weight n < weight (S m) - weight m.
    Proof.
      intros n m H.
      induction H;
        repeat multimatch goal with
               | _ => apply IHle
               | _ => apply weight_dif_mono'
               | _ => etransitivity
               end.
    Qed.

    Context (base : Z)
            (s : Z)
            (c : list (Z * Z))
            (n : nat).

    Context (n_gt_1 : (n > 1)%nat)
            (s_pos : s > 0)
            (c_pos : Associational.eval c > 0)
            (mod_nz : s - Associational.eval c <> 0)
            (base_nz : base <> 0)
            (solinas_property : Rows.adjust_s weight (S (S n)) s = (weight n, true))
            (coef_small : weight n / s * Associational.eval c < up_bound).

    (* SECTION MUL_NO_REDUCE *)

    Theorem eval_mul_no_reduce : forall p q,
        eval weight (2 * n) (mul_no_reduce base n p q) =
          eval weight n p * Positional.eval weight n q.
    Proof using base_nz n_gt_1 wprops.
      intros.
      cbv [mul_no_reduce].
      break_match.
      (* properly bounded *)
      push.
      apply Z.mod_small.
      repeat match goal with
             | H : context[_ && _] |- _ => rewrite andb_true_iff in Heqb
             | H : is_bounded_by _ _ = true |- _ => apply eval_is_bounded_by in H
             | _ => progress intuition
             | _ => solve_ineq
             end.
      le_lt.
      etransitivity.
      apply OrdersEx.Z_as_OT.mul_le_mono_nonneg; eauto; rewrite Le.Z.le_sub_1_iff; eauto.
      le_lt.
      replace (weight (2 * n)) with (weight n * weight n).
      solve_ineq.
      weight_comp.
      rewrite <-OrdersEx.Z_as_OT.pow_mul_r.
      f_equal.
      lia.
      lia.
      lia.

      (* not bounded *)
      push.
      ring_simplify.
      rewrite <-Z_div_mod_eq.
      auto.
      rewrite Z.gt_lt_iff.
      auto.
      push.
      lia.
      push.
    Qed.
    Hint Rewrite eval_mul_no_reduce : push_eval.

    Theorem length_mul_no_reduce : forall p q,
        length (mul_no_reduce base n p q) = (2 * n)%nat.
    Proof.
      intros; unfold mul_no_reduce; break_match; push.
    Qed.
    Hint Rewrite length_mul_no_reduce : push_length.

    (* END SECTION MUL_NO_REDUCE *)

    (* SECTION REDUCE1 *)

    Lemma reduce1_length : forall p m1 m2,
        length (reduce1 base s c m1 m2 p) = m2.
    Proof using wprops.
      intros; cbv [reduce1]; break_match; push.
    Qed.
    Hint Rewrite reduce1_length : push_length.

    Lemma split_p_firstn : forall p,
        n <= length p ->
        split (weight n) (combine (map weight (seq 0 n)) (firstn n p)) =
          (combine (map weight (seq 0 n)) (firstn n p), []).
    Proof using wprops.
      intros p Hlen.
      rewrite split_lt;
        repeat multimatch goal with
               | H : _ |- _ => autorewrite with push_misc in H
               | H : _ |- _ => rewrite in_seq in H
               | _ => rewrite min_l
               | H : context[exists _, _] |- _ => destruct H
               | H : _ = ?x |- context[?x] => rewrite <-H
               | _ => push
               | _ => apply weight_mono
               | _ => intuition
               | _ => auto || lia
               end.
    Qed.
    Hint Rewrite split_p_firstn : push_misc.

    Lemma split_p_skipn : forall p m1,
        n <= length p ->
        split (weight n) (combine (map weight (seq n (m1 - n))) (skipn n p)) =
          ([], combine (map weight (seq 0 (m1 - n))) (skipn n p)).
    Proof using wprops.
      intros p m1 Hlen.
      rewrite split_gt;
        repeat multimatch goal with
               | H : _ |- _ => autorewrite with push_misc in H
               | H : _ |- _ => rewrite in_seq in H
               | _ => apply Weight.weight_multiples_full
               | H : context[exists _, _] |- _ => destruct H
               | H : _ = ?x |- context[?x] => rewrite <-H
               | _ => push
               | _ => intuition
               end.
    Qed.
    Hint Rewrite split_p_skipn : push_misc.

    Lemma split_p : forall m1 p,
        (m1 >= n)%nat ->
        n <= length p ->
        split (weight n) (combine (map weight (seq 0 m1)) p) =
          (combine (map weight (seq 0 n)) (firstn n p),
            (combine (map weight (seq 0 (m1 - n))) (skipn n p))).
    Proof.
      intros.
      replace m1 with (n + (m1 - n))%nat at 1 by lia.
      rewrite <-(firstn_skipn n p) at 1.
      push.
      push.
      lia.
    Qed.
    Hint Rewrite split_p : push_misc.

    Hint Rewrite repeat_length : push_length.

    Ltac solve_ibb :=
        apply eval_is_bounded_by;
        match goal with
        | |- context [firstn _ _] => eapply is_bounded_by_app_l
        | |- context [skipn _ _] => eapply is_bounded_by_app_r
        end; eauto; push; try lia.

    Lemma value_reduce1 : forall p m1 m2,
        (m1 >= n)%nat ->
        (m2 > 0)%nat ->
        n <= length p ->
        up_bound * weight (m1 - n) + weight n < weight m2 ->
        let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
        let coef := Associational.sat_mul_const base [(1, s'/s)] c in
        eval weight m2 (reduce1 base s c m1 m2 p) =
          Associational.eval coef * eval weight (m1 - n) (skipn n p) + eval weight n (firstn n p).
    Proof using base_nz c_pos coef_small n_gt_1 s_pos solinas_property wprops.
      intros.
      assert (Rows.adjust_s weight (S (S m1)) s =
                Rows.adjust_s weight (S (S n)) s) as Hadjust.
      { destruct H.
        auto.
        rewrite solinas_property.
        eapply adjust_s_finished; try apply solinas_property.
        lia.
        lia. }
      cbv [s' coef reduce1]; break_match; push.
      rewrite Hadjust.
      rewrite solinas_property.
      cbv [to_associational].
      push.
      rewrite <-(firstn_skipn n p) in Heqb.
      replace m1 with (n + (m1 - n))%nat in Heqb by lia.
      rewrite repeat_app in Heqb.
      solve_ineq.
      solve_ibb.
      solve_ibb.
      etransitivity.
      solve_ineq.
      apply Z.mul_lt_mono_nonneg.
      solve_ineq.
      eauto.
      solve_ibb.
      solve_ibb.
      solve_ibb.
      lia.

      rewrite Hadjust.
      rewrite solinas_property.
      cbv [to_associational].
      push.
      rewrite <-Z_div_mod_eq_full.
      reflexivity.
      push.
      push.
    Qed.

    Lemma eval_seq_start : forall a b p,
        Associational.eval (combine (map weight (seq a b)) p) =
          weight a * Associational.eval (combine (map weight (seq 0 b)) p).
    Proof using n_gt_1 wprops.
      intros.
      generalize dependent a.
      generalize dependent b.
      induction p as [ | x p IHp ]; intros.
      push.
      destruct b.
      push.
      cbn [seq].
      rewrite <-seq_shift.
      push.
      rewrite IHp.
      lia.
    Qed.

    Lemma eval_reduce1 : forall p m1 m2,
        (m1 >= n)%nat ->
        (m2 > 0)%nat ->
        n <= length p ->
        up_bound * weight (m1 - n) + weight n < weight m2 ->
        let q := reduce1 base s c m1 m2 p in
        (Positional.eval weight m1 p) mod (s - Associational.eval c)
        = (Positional.eval weight m2 q) mod (s - Associational.eval c).
    Proof using base_nz c_pos coef_small mod_nz n_gt_1 s_pos solinas_property wprops.
      intros.
      cbv [q].
      rewrite value_reduce1; try lia.
      push.
      rewrite solinas_property.
      cbn [fst snd].
      match goal with
      | |- context[_ mod (_ - ?c)] =>
          lazymatch goal with
          | |- context[?x * ?c * ?y] => replace (x * c * y) with (c * (x * y)) by lia
          end
      end.
      rewrite Z.add_comm.
      rewrite <-reduction_rule.
      apply Z.elim_mod.
      rewrite <-(firstn_skipn n p) at 1.
      replace m1 with (n + (m1 - n))%nat by lia.
      cbv [eval to_associational].
      push.
      rewrite Z.mul_assoc.
      rewrite <-Z_div_exact_2.
      rewrite Z.add_cancel_l.
      cbn.
      replace (n + (m1 - n) - n)%nat with (m1 - n)%nat by lia.
      rewrite eval_seq_start.
      lia.
      lia.
      pose proof (adjust_s_invariant (S (S n)) s ltac:(lia)) as Hadj.
      rewrite solinas_property in Hadj.
      intuition.
      push.
      lia.
      lia.
    Qed.

    (* END SECTION REDUCE1 *)

    (* SECTION REDUCE_FIRST *)

    Lemma reduce_first_canonical : forall p,
        length p = (2 * n)%nat ->
        is_bounded_by (repeat (0, 2 ^ machine_wordsize - 1) (2 * n)) p = true->
        canonical_repr (S n) (reduce1 base s c (2*n) (S n) p).
    Proof.
      intros p Hlen H.
      cbv [reduce1 canonical_repr].
      rewrite H.
      push.
      intuition.
      erewrite adjust_s_finished; try apply solinas_property; try lia.
      push.
      f_equal.
      rewrite Z.mod_small.
      reflexivity.
      cbv [to_associational].
      push.
      rewrite <-(firstn_skipn n p) in H.
      replace (2*n-n)%nat with n by lia.
      replace (2 * n)%nat with (n + n)%nat in H by lia.
      rewrite repeat_app in H.
      solve_ineq.

      solve_ibb.
      solve_ibb.
      etransitivity.
      solve_ineq.
      apply Z.mul_lt_mono_nonneg.
      solve_ineq.
      eauto.
      solve_ibb.
      solve_ibb.
      solve_ibb.
      cbv [up_bound machine_wordsize].
      weight_comp.
      rewrite <-Z.mul_succ_l.
      apply Zmult_lt_compat_r.
      all: cbn; break_match; lia.
    Qed.

    (* END SECTION REDUCE_FIRST *)

    (* SECTION REDUCE_SECOND *)

    Lemma reduce_second_canonical : forall p,
        canonical_repr (S n) p ->
        canonical_repr (S n) (reduce1 base s c (S n) (S n) p).
    Proof.
      intros.
      cbv [canonical_repr].
      push.
      assert (Hcanon := H).
      cbv [canonical_repr] in H.
      intuition.
      rewrite value_reduce1.
      rewrite solinas_property.
      push.
      cbv [reduce1].
      break_match.
      push.
      erewrite adjust_s_finished'; try eapply solinas_property.
      cbv [to_associational].
      rewrite split_p.
      push.
      lia.
      lia.
      lia.

      rewrite canonical_is_bounded_by in Hcanon.
      intuition.
      match goal with
      | H : ?x = true, H1 : ?x = false |- _ => rewrite H in H1; discriminate
      end.
      lia.
      lia.
      lia.
      replace (S n - n)%nat with 1%nat by lia.
      cbv [up_bound machine_wordsize].
      rewrite Z.lt_add_lt_sub_r.
      etransitivity; [ | apply weight_dif_mono with (n:=1%nat); lia ].
      weight_comp; cbn; lia.
    Qed.

    Hint Rewrite nth_default_partition : push_misc.
    Lemma reduce_second_bounds : forall p,
        canonical_repr (S n) p ->
        (nth_default 0 p n) < up_bound ->
        let q := reduce1 base s c (S n) (S n) p in
        (nth_default 0 q (n-1) = 0 /\ nth_default 0 q n = 1) \/
          nth_default 0 q n = 0.
    Proof.
      intros.
      pose proof (reduce_second_canonical p ltac:(auto)) as Hcanonq.
      fold q in Hcanonq.
      pose proof (firstn_skipn n p) as Hp; symmetry in Hp.
      pose proof (firstn_skipn n q) as Hq; symmetry in Hq.
      canonical_app p.
      push' Hcanon_l.
      push' Hcanon_r.
      canonical_app q; push' Hcanon_l0; push' Hcanon_r0.
      replace (length p) with (S n) in * by (solve_length p).
      replace (length q) with (S n) in * by (solve_length q).
      rewrite min_l in *; [| lia | solve_length q].
      const_simpl.

      assert (0 <= nth_default 0 q n < 2).
      assert (Hcanonq' := Hcanonq).
      cbv [canonical_repr] in Hcanonq'.
      destruct Hcanonq as [ _ Hpartq ].
      rewrite Hpartq.
      push.
      solve_ineq; auto.
      rewrite Z.mod_small.
      cbv [q].
      rewrite value_reduce1.
      const_simpl.
      rewrite solinas_property.
      push.
      rewrite <-Zplus_diag_eq_mult_2.
      solve_ineq.
      etransitivity.
      apply Z.mul_lt_mono_nonneg.
      solve_ineq.
      eauto.
      apply canonical_pos; auto.
      rewrite skipn_nth_default with (d:=0).
      rewrite skipn_all.
      push; eauto.
      solve_length p.
      solve_length p.
      cbv [up_bound machine_wordsize].
      weight_comp.
      rewrite <-OrdersEx.Z_as_OT.pow_mul_r.
      apply Z.pow_lt_mono_r; cbn; break_match; lia.
      cbn; lia.
      lia.
      apply canonical_eval_bounded; auto.
      lia.
      lia.
      solve_length p.
      const_simpl.
      cbv [up_bound machine_wordsize].
      rewrite Z.lt_add_lt_sub_r.
      etransitivity; [ | apply weight_dif_mono with (n:=1%nat); lia ].
      weight_comp; cbn; lia.
      solve_ineq; [apply canonical_pos | apply canonical_eval_bounded]; auto.

      assert (Hnth : nth_default 0 q n = 0 \/ nth_default 0 q n = 1) by lia.
      destruct Hnth as [Hnth1 | Hnth2].
      intuition.
      left.
      intuition.
      assert (Hcanonq' := Hcanonq).
      destruct Hcanonq' as [_ Hpart].
      rewrite Hpart.
      push.
      assert (H' : Associational.eval (combine (map weight (seq 0 n)) (firstn n q)) = eval weight (S n) q - weight n).
      rewrite Hq at 2.
      cbv [eval to_associational].
      rewrite seq_snoc.
      push.
      rewrite skipn_nth_default with (d:=0).
      rewrite skipn_all.
      const_simpl.
      cbn [seq].
      push.
      lia.
      solve_length q.
      solve_length q.
      push.
      rewrite min_l; [lia | solve_length q].
      rewrite <-Z.add_move_l in H'.
      rewrite <-H'.
      const_simpl.
      rewrite Zplus_mod, Z.mod_same, Z.add_0_l, Z.mod_mod.
      rewrite Z.add_move_l in H'.
      apply Z.div_small.
      rewrite Z.mod_small.
      solve_ineq.
      apply canonical_pos; auto.
      rewrite H'.
      rewrite Z.lt_sub_lt_add_l.
      cbv [q].
      rewrite value_reduce1.
      rewrite solinas_property.
      push.
      const_simpl.
      rewrite Z.add_comm.
      solve_ineq.
      apply canonical_eval_bounded; auto.
      rewrite skipn_nth_default with (d:=0).
      rewrite skipn_all.
      push.
      etransitivity.
      apply Z.mul_lt_mono_nonneg.
      solve_ineq.
      eauto.
      apply (canonical_bounded (S n) p).
      auto.
      rewrite Hp at 2.
      apply in_or_app.
      right.
      rewrite skipn_nth_default with (d:=0).
      rewrite skipn_all.
      push.
      solve_length p.
      solve_length p.
      eauto.
      cbv [up_bound machine_wordsize].
      rewrite <-Le.Z.le_sub_1_iff.
      etransitivity; [| rewrite <-Z.sub_le_mono_r; apply (weight_mono_le 1)].
      weight_comp; cbn; lia.
      lia.
      solve_length p.
      solve_length p.
      lia.
      lia.
      solve_length p.
      const_simpl.
      cbv [up_bound machine_wordsize].
      rewrite Z.lt_add_lt_sub_r.
      etransitivity; [| apply (weight_dif_mono 1)].
      weight_comp; cbn; lia.
      lia.
      solve_ineq.
      apply canonical_pos; auto.
      apply canonical_eval_bounded; auto.
      auto.
      auto.
      lia.
    Qed.

    (* END SECTION REDUCE_SECOND *)

    (* SECTION REDUCE_THIRD *)

    Lemma value_reduce_third : forall p,
        canonical_repr (S n) p ->
        let q := reduce1 base s c (S n) n p in
        ((nth_default 0 p (n-1) = 0 /\ nth_default 0 p n = 1) \/
           nth_default 0 p n = 0) ->
        let r := reduce1 base s c (S n) n q in
        let s' := fst (Saturated.Rows.adjust_s weight (S (S (S n))) s) in
        let coef := Associational.sat_mul_const base [(1, s'/s)] c in
        eval weight n q = Associational.eval coef * (nth_default 0 p n) + eval weight n (firstn n p).
    Proof.
      intros p ? ? Hbounds ? ? ?.
      pose proof (firstn_skipn n p) as Hp; symmetry in Hp.
      canonical_app p.
      push' Hcanon_l.
      push' Hcanon_r.
      replace (length p) with (S n) in * by (solve_length p).
      rewrite min_l in Hcanon_l; [| lia].
      const_simpl.
      pose proof (firstn_succ 0 (n - 1) p ltac:(solve_length p)) as Hpfirst.
      const_simpl.
      canonical_app (firstn n p).
      push' Hcanon_l0.
      push' Hcanon_r0.
      rewrite min_l in Hcanon_l0; [| solve_length p].
      cbv [q s' coef reduce1]; push.
      erewrite adjust_s_finished'; try apply solinas_property; try lia.
      push.
      cbv [to_associational].
      rewrite split_p; [| lia | solve_length p].
      const_simpl.
      cbn [seq].
      push.
      rewrite skipn_nth_default with (d:=0); [| solve_length p].
      rewrite skipn_all; [| solve_length p].
      push.
      break_match; push.
      apply Z.mod_small.
      cbv [eval to_associational].
      destruct Hbounds as [ Hbounds | Hbounds ].
      destruct Hbounds as [ Hbounds1 Hbounds2 ].
      replace n with (S (n-1))%nat at 3 4 7 8 by lia.
      rewrite firstn_succ with (d:=0).
      rewrite seq_snoc.
      rewrite Hbounds1.
      rewrite Hbounds2.
      push.
      solve_ineq.
      apply canonical_pos; auto.
      etransitivity.
      solve_ineq.
      eauto.
      apply canonical_eval_bounded; auto.
      rewrite Z.lt_add_lt_sub_r.
      replace n with (S (n-1))%nat at 1 by lia.
      etransitivity; [| apply (weight_dif_mono 0)].
      weight_comp; cbn; lia.
      lia.
      push.
      rewrite min_l; solve_length p.
      solve_length p.
      rewrite Hbounds.
      push.
      solve_ineq.
      apply canonical_pos; auto.
      apply canonical_eval_bounded; auto.

      (* not bounded *)
      rewrite <-Z_div_mod_eq_full.
      auto.
      push.
      lia.
      push.
    Qed.

    Lemma eval_reduce_third : forall p,
        (canonical_repr (S n) p) ->
        let q := reduce1 base s c (S n) n p in
        ((nth_default 0 p (n-1) = 0 /\ nth_default 0 p n = 1) \/
           nth_default 0 p n = 0) ->
        (Positional.eval weight (S n) p) mod (s - Associational.eval c)
        = (Positional.eval weight n q) mod (s - Associational.eval c).
    Proof.
      intros.
      pose proof (firstn_skipn n p) as Hp; symmetry in Hp.
      rewrite Hp at 1.
      unfold eval at 1.
      unfold to_associational.
      rewrite seq_snoc.
      rewrite skipn_nth_default with (d:=0) by (solve_length p).
      rewrite skipn_all by (solve_length p).
      cbv [q].
      rewrite value_reduce_third; auto.
      erewrite adjust_s_finished'; try apply solinas_property; [| lia].
      push.
      match goal with
      | |- context[_ mod (_ - ?c)] =>
          repeat multimatch goal with
                 | |- context[?x * ?c * ?y] => replace (x * c * y) with (c * (x * y)) by lia
                 | |- context[?c * _ + ?x] => rewrite (Z.add_comm _ x)
                 end
      end.
      rewrite <-reduction_rule; [| lia].
      apply Z.elim_mod.
      unfold eval, to_associational at 1.
      rewrite Z.add_cancel_l.
      rewrite Z.mul_assoc.
      rewrite <-Z_div_exact_2.
      const_simpl.
      lia.
      lia.
      pose proof (adjust_s_invariant (S (S n)) s ltac:(lia)) as Hinv.
      rewrite solinas_property in Hinv.
      cbn [fst] in Hinv.
      apply Hinv.
      push.
      rewrite min_l by (solve_length p).
      lia.
    Qed.

    (* END SECTION REDUCE_THIRD *)

    (* SECTION REDUCE_FULL] *)
    Theorem reduce_full_correct : forall (p : list Z),
        n <= length p ->
        let r := reduce_full base s c n p in
        (Positional.eval weight (2 * n) p) mod (s - Associational.eval c)
        = (Positional.eval weight n r) mod (s - Associational.eval c).
    Proof.
      intros; cbv [r reduce_full]; break_match.
      (* bounds are good *)
      pose proof (is_bounded_by_nth n _ _ Heqb ltac:(push) ltac:(push)) as Hnth.
      repeat match goal with
             | H : context[nth_default _ (_ ++ _) _] |- _ => rewrite nth_default_app in H
             | H : context[snd (nth_default _ _ _)] |- _ => progress cbn in H
             | H : _ |- _ => progress push' H
             | _ => progress destruct lt_dec
             | _ => progress intuition
             | _ => lia
             end.
      apply is_bounded_by_loosen with (bound2:=repeat (0, 2^machine_wordsize-1) (S n)) in Heqb.
      assert (canonical_repr (S n) (reduce1 base s c (2*n) (S n) p)).
      rewrite canonical_is_bounded_by.
      intuition; push.
      rewrite <-eval_reduce_third.
      rewrite <-eval_reduce1.
      rewrite <-eval_reduce1.
      auto.
      pose proof (firstn_skipn n p) as Hp; symmetry in Hp.

      all:
        repeat multimatch goal with
               | _ => apply reduce_second_canonical
               | _ => apply reduce_second_bounds
               | _ => solve_length p
               | _ => const_simpl
               | _ => cbv [up_bound]
               | _ => push
               | _ => auto
               | _ => lia
               end.
      weight_comp; try lia.
      rewrite <-Z.mul_succ_l.
      apply Zmult_lt_compat_r; cbn; break_match; lia.
      rewrite Z.lt_add_lt_sub_r.
      etransitivity; [| apply (weight_dif_mono 1); lia].
      weight_comp; cbn; break_match; lia.
      cbn; const_simpl; lia.
      replace (S n) with (n+1)%nat.
      rewrite repeat_app.
      autounfold.
      push.
      cbn.
      apply bounds_same.
      lia.

      (* not canonical *)
      rewrite eval_reduce1 with (m2:=S n).
      rewrite <-(firstn_skipn n (reduce1 base s c (2 * n) (S n) p)) at 1.
      unfold eval at 1.
      unfold to_associational.
      rewrite seq_snoc.
      rewrite skipn_nth_default with (d:=0).
      rewrite skipn_all.
      push.
      apply Z.elim_mod.
      const_simpl.
      rewrite Z.add_comm at 1.
      auto.
      all:
        repeat multimatch goal with
               | _ => push
               | _ => lia
               end.
      const_simpl.
      cbv [up_bound].
      weight_comp; try lia.
      rewrite <-Z.mul_succ_l.
      apply Zmult_lt_compat_r; cbn; break_match; lia.
    Qed.
    (* END SECTION REDUCE_FULL *)

    (* SECTION MULMOD *)
    Theorem mulmod_correct : forall p q,
        Positional.eval weight n (mulmod base s c n p q) mod (s - Associational.eval c) =
          (Positional.eval weight n p * Positional.eval weight n q) mod (s - Associational.eval c).
    Proof.
      intros.
      cbv [mulmod].
      rewrite <-reduce_full_correct; push; lia.
    Qed.
    (* END SECTION MULMOD *)

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

    Let bounds := repeat bound n ++ [Some r[0 ~> (2^(machine_wordsize/4) - 1)]%zrange].

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
                  let r := Reify (reduce_full base s c n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound (2*n)), tt)
                   (Some (repeat bound (n)))
                   (None, tt)
                   (None)
           : Pipeline.ErrorT _).
    (*
     = "Success (""/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
static void mul(uint64_t out1[4], const uint64_t arg1[8]) {
  uint64_t x1;
  uint64_t x2;
  uint64_t x3;
  uint64_t x4;
  uint64_t x5;
  uint64_t x6;
  uint64_t x7;
  uint64_t x8;
  uint64_t x9;
  uint64_t x10;
  uint64_t x11;
  uint64_t x12;
  uint64_t x13;
  fiatuint1 x14;
  uint64_t x15;
  fiatuint1 x16;
  uint64_t x17;
  fiatuint1 x18;
  uint64_t x19;
  uint64_t x20;
  fiatuint1 x21;
  uint64_t x22;
  fiatuint1 x23;
  uint64_t x24;
  fiatuint1 x25;
  uint64_t x26;
  fiatuint1 x27;
  uint64_t x28;
  uint64_t x29;
  uint64_t x30;
  uint64_t x31;
  fiatuint1 x32;
  uint64_t x33;
  fiatuint1 x34;
  uint64_t x35;
  fiatuint1 x36;
  uint64_t x37;
  fiatuint1 x38;
  uint64_t x39;
  uint64_t x40;
  uint64_t x41;
  fiatuint1 x42;
  uint64_t x43;
  fiatuint1 x44;
  uint64_t x45;
  fiatuint1 x46;
  uint64_t x47;
  fiatuint1 x48;
  fiatmulx_u64(&x1, &x2, UINT8_C(0x26), (arg1[7]));
  fiatmulx_u64(&x3, &x4, UINT8_C(0x26), (arg1[6]));
  fiatmulx_u64(&x5, &x6, UINT8_C(0x26), (arg1[5]));
  fiatmulx_u64(&x7, &x8, UINT8_C(0x26), (arg1[4]));
  x9 = (arg1[3]);
  x10 = (arg1[2]);
  x11 = (arg1[1]);
  x12 = (arg1[0]);
  fiataddcarryx_u64(&x13, &x14, 0x0, x11, x5);
  fiataddcarryx_u64(&x15, &x16, x14, x10, x3);
  fiataddcarryx_u64(&x17, &x18, x16, x9, x1);
  x19 = (x18 + x2);
  fiataddcarryx_u64(&x20, &x21, 0x0, x12, x7);
  fiataddcarryx_u64(&x22, &x23, x21, x13, x8);
  fiataddcarryx_u64(&x24, &x25, x23, x15, x6);
  fiataddcarryx_u64(&x26, &x27, x25, x17, x4);
  x28 = (x27 + x19);
  fiatmulx_u64(&x29, &x30, UINT8_C(0x26), x28);
  fiataddcarryx_u64(&x31, &x32, 0x0, x20, x29);
  fiataddcarryx_u64(&x33, &x34, x32, x22, 0x0);
  fiataddcarryx_u64(&x35, &x36, x34, x24, 0x0);
  fiataddcarryx_u64(&x37, &x38, x36, x26, 0x0);
  fiatmulx_u64(&x39, &x40, UINT8_C(0x26), x38);
  fiataddcarryx_u64(&x41, &x42, 0x0, x31, x39);
  fiataddcarryx_u64(&x43, &x44, x42, x33, 0x0);
  fiataddcarryx_u64(&x45, &x46, x44, x35, 0x0);
  fiataddcarryx_u64(&x47, &x48, x46, x37, 0x0);
  out1[0] = x41;
  out1[1] = x43;
  out1[2] = x45;
  out1[3] = x47;
}"", {| bitwidths_used := [uint1, uint64] ; addcarryx_lg_splits := [64] ; mulx_lg_splits := [64] ; cmovznz_bitwidths := [] ; value_barrier_bitwidths := [] ; typedefs_used := [] |})"
     : string
Finished transaction in 4.561 secs (4.508u,0.047s) (successful)
     *)

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
                  let r := Reify (mul_no_reduce base n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound n), (Some (repeat bound n), tt))
                   (Some (repeat bound (2 * n)))
                   (None, (None, tt))
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
                  let r := Reify (mulmod base s c n) in
                  exact r)
                   (fun _ _ => [])
                   (Some (repeat bound n), (Some (repeat bound n), tt))
                   (Some (repeat bound (n)))
                   (None, (None, tt))
                   (None)
           : Pipeline.ErrorT _).
(*
     = "Success (""/*
 * Input Bounds:
 *   arg1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 *   arg2: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 * Output Bounds:
 *   out1: [[0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff], [0x0 ~> 0xffffffffffffffff]]
 */
static void mul(uint64_t out1[4], const uint64_t arg1[4], const uint64_t arg2[4]) {
  uint64_t x1;
  uint64_t x2;
  uint64_t x3;
  uint64_t x4;
  uint64_t x5;
  uint64_t x6;
  uint64_t x7;
  uint64_t x8;
  uint64_t x9;
  uint64_t x10;
  uint64_t x11;
  uint64_t x12;
  uint64_t x13;
  uint64_t x14;
  uint64_t x15;
  uint64_t x16;
  uint64_t x17;
  uint64_t x18;
  uint64_t x19;
  uint64_t x20;
  uint64_t x21;
  uint64_t x22;
  uint64_t x23;
  uint64_t x24;
  uint64_t x25;
  uint64_t x26;
  uint64_t x27;
  uint64_t x28;
  uint64_t x29;
  uint64_t x30;
  uint64_t x31;
  uint64_t x32;
  uint64_t x33;
  fiatuint1 x34;
  uint64_t x35;
  fiatuint1 x36;
  uint64_t x37;
  uint64_t x38;
  fiatuint1 x39;
  uint64_t x40;
  fiatuint1 x41;
  uint64_t x42;
  fiatuint1 x43;
  uint64_t x44;
  uint64_t x45;
  fiatuint1 x46;
  uint64_t x47;
  fiatuint1 x48;
  uint64_t x49;
  fiatuint1 x50;
  uint64_t x51;
  fiatuint1 x52;
  uint64_t x53;
  fiatuint1 x54;
  uint64_t x55;
  uint64_t x56;
  fiatuint1 x57;
  uint64_t x58;
  fiatuint1 x59;
  uint64_t x60;
  fiatuint1 x61;
  uint64_t x62;
  fiatuint1 x63;
  uint64_t x64;
  fiatuint1 x65;
  uint64_t x66;
  fiatuint1 x67;
  uint64_t x68;
  fiatuint1 x69;
  uint64_t x70;
  fiatuint1 x71;
  uint64_t x72;
  fiatuint1 x73;
  uint64_t x74;
  fiatuint1 x75;
  uint64_t x76;
  fiatuint1 x77;
  uint64_t x78;
  fiatuint1 x79;
  uint64_t x80;
  fiatuint1 x81;
  uint64_t x82;
  fiatuint1 x83;
  uint64_t x84;
  fiatuint1 x85;
  uint64_t x86;
  fiatuint1 x87;
  uint64_t x88;
  fiatuint1 x89;
  uint64_t x90;
  fiatuint1 x91;
  uint64_t x92;
  fiatuint1 x93;
  uint64_t x94;
  fiatuint1 x95;
  uint64_t x96;
  uint64_t x97;
  uint64_t x98;
  uint64_t x99;
  uint64_t x100;
  uint64_t x101;
  uint64_t x102;
  uint64_t x103;
  uint64_t x104;
  fiatuint1 x105;
  uint64_t x106;
  fiatuint1 x107;
  uint64_t x108;
  fiatuint1 x109;
  uint64_t x110;
  uint64_t x111;
  fiatuint1 x112;
  uint64_t x113;
  fiatuint1 x114;
  uint64_t x115;
  fiatuint1 x116;
  uint64_t x117;
  fiatuint1 x118;
  uint64_t x119;
  uint64_t x120;
  uint64_t x121;
  uint64_t x122;
  fiatuint1 x123;
  uint64_t x124;
  fiatuint1 x125;
  uint64_t x126;
  fiatuint1 x127;
  uint64_t x128;
  fiatuint1 x129;
  uint64_t x130;
  uint64_t x131;
  uint64_t x132;
  fiatuint1 x133;
  uint64_t x134;
  fiatuint1 x135;
  uint64_t x136;
  fiatuint1 x137;
  uint64_t x138;
  fiatuint1 x139;
  fiatmulx_u64(&x1, &x2, (arg1[3]), (arg2[3]));
  fiatmulx_u64(&x3, &x4, (arg1[3]), (arg2[2]));
  fiatmulx_u64(&x5, &x6, (arg1[3]), (arg2[1]));
  fiatmulx_u64(&x7, &x8, (arg1[3]), (arg2[0]));
  fiatmulx_u64(&x9, &x10, (arg1[2]), (arg2[3]));
  fiatmulx_u64(&x11, &x12, (arg1[2]), (arg2[2]));
  fiatmulx_u64(&x13, &x14, (arg1[2]), (arg2[1]));
  fiatmulx_u64(&x15, &x16, (arg1[2]), (arg2[0]));
  fiatmulx_u64(&x17, &x18, (arg1[1]), (arg2[3]));
  fiatmulx_u64(&x19, &x20, (arg1[1]), (arg2[2]));
  fiatmulx_u64(&x21, &x22, (arg1[1]), (arg2[1]));
  fiatmulx_u64(&x23, &x24, (arg1[1]), (arg2[0]));
  fiatmulx_u64(&x25, &x26, (arg1[0]), (arg2[3]));
  fiatmulx_u64(&x27, &x28, (arg1[0]), (arg2[2]));
  fiatmulx_u64(&x29, &x30, (arg1[0]), (arg2[1]));
  fiatmulx_u64(&x31, &x32, (arg1[0]), (arg2[0]));
  fiataddcarryx_u64(&x33, &x34, 0x0, x28, x7);
  fiataddcarryx_u64(&x35, &x36, x34, x26, x5);
  x37 = (x36 + x18);
  fiataddcarryx_u64(&x38, &x39, 0x0, x33, x13);
  fiataddcarryx_u64(&x40, &x41, x39, x35, x8);
  fiataddcarryx_u64(&x42, &x43, x41, x37, 0x0);
  x44 = (x43 + x10);
  fiataddcarryx_u64(&x45, &x46, 0x0, x30, x15);
  fiataddcarryx_u64(&x47, &x48, x46, x38, x16);
  fiataddcarryx_u64(&x49, &x50, x48, x40, x11);
  fiataddcarryx_u64(&x51, &x52, x50, x42, x3);
  fiataddcarryx_u64(&x53, &x54, x52, x44, 0x0);
  x55 = (x54 + x2);
  fiataddcarryx_u64(&x56, &x57, 0x0, x45, x21);
  fiataddcarryx_u64(&x58, &x59, x57, x47, x19);
  fiataddcarryx_u64(&x60, &x61, x59, x49, x14);
  fiataddcarryx_u64(&x62, &x63, x61, x51, x6);
  fiataddcarryx_u64(&x64, &x65, x63, x53, 0x0);
  fiataddcarryx_u64(&x66, &x67, x65, x55, 0x0);
  fiataddcarryx_u64(&x68, &x69, 0x0, x32, x23);
  fiataddcarryx_u64(&x70, &x71, x69, x56, x24);
  fiataddcarryx_u64(&x72, &x73, x71, x58, x22);
  fiataddcarryx_u64(&x74, &x75, x73, x60, x17);
  fiataddcarryx_u64(&x76, &x77, x75, x62, x9);
  fiataddcarryx_u64(&x78, &x79, x77, x64, x1);
  fiataddcarryx_u64(&x80, &x81, x79, x66, 0x0);
  fiataddcarryx_u64(&x82, &x83, 0x0, x68, x29);
  fiataddcarryx_u64(&x84, &x85, x83, x70, x27);
  fiataddcarryx_u64(&x86, &x87, x85, x72, x25);
  fiataddcarryx_u64(&x88, &x89, x87, x74, x20);
  fiataddcarryx_u64(&x90, &x91, x89, x76, x12);
  fiataddcarryx_u64(&x92, &x93, x91, x78, x4);
  fiataddcarryx_u64(&x94, &x95, x93, x80, 0x0);
  fiatmulx_u64(&x96, &x97, UINT8_C(0x26), x94);
  fiatmulx_u64(&x98, &x99, UINT8_C(0x26), x92);
  fiatmulx_u64(&x100, &x101, UINT8_C(0x26), x90);
  fiatmulx_u64(&x102, &x103, UINT8_C(0x26), x88);
  fiataddcarryx_u64(&x104, &x105, 0x0, x82, x100);
  fiataddcarryx_u64(&x106, &x107, x105, x84, x98);
  fiataddcarryx_u64(&x108, &x109, x107, x86, x96);
  x110 = (x109 + x97);
  fiataddcarryx_u64(&x111, &x112, 0x0, x31, x102);
  fiataddcarryx_u64(&x113, &x114, x112, x104, x103);
  fiataddcarryx_u64(&x115, &x116, x114, x106, x101);
  fiataddcarryx_u64(&x117, &x118, x116, x108, x99);
  x119 = (x118 + x110);
  fiatmulx_u64(&x120, &x121, UINT8_C(0x26), x119);
  fiataddcarryx_u64(&x122, &x123, 0x0, x111, x120);
  fiataddcarryx_u64(&x124, &x125, x123, x113, 0x0);
  fiataddcarryx_u64(&x126, &x127, x125, x115, 0x0);
  fiataddcarryx_u64(&x128, &x129, x127, x117, 0x0);
  fiatmulx_u64(&x130, &x131, UINT8_C(0x26), x129);
  fiataddcarryx_u64(&x132, &x133, 0x0, x122, x130);
  fiataddcarryx_u64(&x134, &x135, x133, x124, 0x0);
  fiataddcarryx_u64(&x136, &x137, x135, x126, 0x0);
  fiataddcarryx_u64(&x138, &x139, x137, x128, 0x0);
  out1[0] = x132;
  out1[1] = x134;
  out1[2] = x136;
  out1[3] = x138;
}"", {| bitwidths_used := [uint1, uint64] ; addcarryx_lg_splits := [64] ; mulx_lg_splits := [64] ; cmovznz_bitwidths := [] ; value_barrier_bitwidths := [] ; typedefs_used := [] |})"
     : string
Finished transaction in 5.821 secs (5.782u,0.039s) (successful)
*)

  End compile.

End solinas_reduction.
