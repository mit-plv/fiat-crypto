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
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import (*hints*) Coq.btauto.Algebra.
Require Coq.Structures.OrdersEx.
Require Import Crypto.Util.ListUtil.StdlibCompat.
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

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Module SolinasReduction.

  Import Core.Associational.
  Import Core.Positional.

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
        (* | [ |- 0 <= _ mod _ ] => apply Z_mod_nonneg_nonneg *)
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
    Proof using Type. lia. Qed.
    Hint Rewrite S_sub_1 using lia : const_simpl.
    Lemma Sn_sub_n : forall (n : nat),
        (S n - n)%nat = 1%nat.
    Proof using Type. lia. Qed.
    Hint Rewrite Sn_sub_n : const_simpl.
    Lemma n2_sub : forall (n : nat),
        (2 * n - n)%nat = n.
    Proof using Type. lia. Qed.
    Hint Rewrite n2_sub : const_simpl.
    Ltac const_simpl :=
      autorewrite with const_simpl in *.

    Hint Rewrite eval_cons using auto : push_eval.
    Hint Rewrite eval_sat_mul using lia : push_eval.
    Hint Rewrite eval_sat_mul_const using lia : push_eval.
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
    Proof using Type.
      intros n; replace (2*n)%nat with (n+n)%nat; push; lia.
    Qed.
    Hint Rewrite seq_double : push_misc.

    Lemma map_weight_seq : forall m p,
        map weight (seq 0 p) = map (fun t => t / (weight m)) (map weight (seq m p)).
    Proof using wprops.
      induction m as [| m IHm]; intros; push.
      erewrite map_ext.
      eauto.
      intros.
      cbn.
      rewrite Z.div_1_r.
      lia.

      rewrite IHm.
      rewrite <-seq_shift.
      push.
      apply map_ext_in.
      intros a H.
      rewrite in_seq in H.
      weight_comp; try lia.
      rewrite <-!Z.pow_add_r; try lia.
      rewrite <-!Z.pow_sub_r; try lia.
      f_equal.
      lia.
    Qed.
    Hint Rewrite <-map_weight_seq : push_misc.

    Lemma seq_shift_1 : forall len,
        map S (seq 0 len) = seq 1 len.
    Proof using Type.
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
    Proof using wprops.
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
    Proof using wprops.
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
    Proof using wprops.
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
    Proof using Type.
      intros l x.
      induction l as [ | l' IHl ]; cbn; try rewrite IHl; lia.
    Qed.

    Definition eval_weight_P p := forall a b,
        Associational.eval (combine (map (fun x0 : nat => weight (S x0)) (seq a b)) p) =
          weight 1 * Associational.eval (combine (map weight (seq a b)) p).

    Lemma eval_weight_S' : forall p,
        eval_weight_P p.
    Proof using Type.
      apply (ListAux.list_length_induction Z).
      unfold eval_weight_P.
      intros l1 H n b.
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
      symmetry.
      rewrite fold_right_add.
      symmetry.
      rewrite fold_right_add.
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
    Proof using Type.
      cbv [eval to_associational].
      rewrite eval_weight_S'.
      lia.
    Qed.
    Hint Rewrite eval_weight_S : push_eval.

    Lemma eval_weight_S_gen p a b :
      Associational.eval (combine (map (fun x0 : nat => weight (S x0)) (seq a b)) p) =
        weight 1 * Associational.eval (combine (map weight (seq a b)) p).
    Proof using Type.
      apply eval_weight_S'.
    Qed.
    Hint Rewrite eval_weight_S_gen : push_eval.

    Lemma canonical_eval_bounded n : forall (p : list Z),
        canonical_repr n p ->
        eval weight n p < weight n.
    Proof using wprops.
      intros p.
      generalize dependent n.
      induction p as [| a p IHp]; intros n H; destruct n; push; try lia;
        assert (H' := H); unfold canonical_repr in H'; push' H'.
      lia.
      le_lt.
      etransitivity.
      solve_ineq.
      le_lt.
      eapply canonical_bounded; eauto.
      rewrite <-OrdersEx.Z_as_OT.mul_le_mono_pos_r; eauto.
      le_lt.
      apply IHp.
      eapply canonical_app_r with (l1:=[a]); eauto.
      all: try lia.
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
    Proof using wprops.
      intros n p.
      rewrite canonical_iff.
      repeat autounfold.
      split.
      intros H.
      destruct H as [H H1].
      intuition.
      generalize dependent n.
      induction p as [| a p IHp]; intros;
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
               | H : context[_ <=? _] |- _ => rewrite <-Zle_is_le_bool in H
               | _ => progress cbn || intuition || subst
               | _ => lia
               | _ => eapply IHp
               end.
    Qed.

    Lemma eval_is_bounded_by_pos n : forall p,
        is_bounded_by (repeat (0, 2 ^ machine_wordsize - 1) n) p = true ->
        0 <= eval weight n p.
    Proof.
      intros p.
      pose proof eval_weight_S as Heval.
      repeat autounfold with * in *.
      generalize dependent n; induction p; intros n; destruct n;
        repeat multimatch goal with
               | H : context[fold_right _ _ _] |- _ => cbn in H
               | H : context[_ && _] |- _ => rewrite andb_true_iff in H
               | H : context[_ <=? _] |- _ => rewrite <-Zle_is_le_bool in H
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
    Proof using wprops.
      intros p.
      split.
      apply eval_is_bounded_by_pos; auto.
      pose proof eval_weight_S as Heval.
      repeat autounfold with * in *.
      generalize dependent n; induction p; intros n; destruct n;
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
      apply Z.mul_le_mono_nonneg_r; try lia.
      le_lt.
      apply IHp; auto.
      weight_comp; lia.
    Qed.
    Hint Resolve eval_is_bounded_by : ibb.

    Lemma is_bounded_by_cons1 : forall b bounds p' p,
        is_bounded_by (b :: bounds) (p' :: p) = true ->
        is_bounded_by bounds p = true.
    Proof using Type.
      intros; repeat autounfold in *; match goal with | H : _ |- _ => push' H end.
    Qed.
    Hint Resolve is_bounded_by_cons1 : ibb.

    Lemma is_bounded_by_cons2 : forall b bounds p' p,
        is_bounded_by (b :: bounds) (p' :: p) = true ->
        fst b <= p' <= snd b.
    Proof using Type.
      intros; repeat autounfold in *; match goal with | H : _ |- _ => push' H end.
    Qed.
    Hint Resolve is_bounded_by_cons2 : ibb.

    Lemma is_bounded_by_cons : forall b bounds p' p,
        is_bounded_by (b :: bounds) (p' :: p) = true ->
        is_bounded_by bounds p = true /\
          fst b <= p' <= snd b.
    Proof using Type.
      intros; repeat autounfold in *; match goal with | H : _ |- _ => push' H end.
    Qed.
    Hint Resolve is_bounded_by_cons : ibb.

    Lemma is_bounded_by_nth n : forall p bounds,
        is_bounded_by bounds p = true ->
        (n < length p)%nat ->
        (n < length bounds)%nat ->
        fst (nth_default (0,0) bounds n) <= nth_default 0 p n <= snd (nth_default (0,0) bounds n).
    Proof using Type.
      intros p bounds H H0 H1.
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
    Proof using Type.
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
    Proof using Type.
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
    Proof using Type.
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
    Proof using Type.
      intros l bound1 bound2 H H0 H1.
      generalize dependent bound1.
      generalize dependent bound2.
      repeat autounfold.
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
    Proof using Type.
      intros b.
      repeat autounfold.
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
    Proof.
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
    Proof using Type.
      cbv [Rows.adjust_s].
      rewrite !fold_right_map.
      replace (rev (seq 0 (S fuel))) with (fuel :: rev (seq 0 fuel)).
      generalize (rev (seq 0 fuel)).
      cbn in *.
      intros l.
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
    Proof using Type.
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
      if (is_bounded_by (repeat bound n) p) then
        if (is_bounded_by (repeat bound n) q) then
          fst pq
        else
          add_to_nth 0 (weight (2 * n) * snd pq) (fst pq)
      else
        add_to_nth 0 (weight (2 * n) * snd pq) (fst pq).

    Definition reduce1 base s c n m (p : list Z) :=
      let bound := (0, 2^machine_wordsize - 1) in
      if (is_bounded_by (repeat bound n) p) then
        let p_a := Positional.to_associational weight n p in
        let r_a := sat_reduce base s c n p_a in
        let r_rows := Saturated.Rows.from_associational weight m r_a in
        let r_flat := Saturated.Rows.flatten weight m r_rows in
        fst r_flat
      else
        let p_a := Positional.to_associational weight n p in
        let r_a := sat_reduce base s c n p_a in
        let r_rows := Saturated.Rows.from_associational weight m r_a in
        let r_flat := Saturated.Rows.flatten weight m r_rows in
        add_to_nth 0 (weight (m) * snd r_flat) (fst r_flat).

    (* S n -> n limbs *)
    Definition reduce3 base s c n (p : list Z) :=
      let bound := (0, 2^machine_wordsize-1) in
      let bounds := (repeat bound n) ++ [(0, 1)] in
      let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
      let coef_a := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let coef := Associational.eval coef_a in
      dlet_nd hi := Z.zselect (nth_default 0 p n) 0 coef in
          let lo := Saturated.Rows.flatten weight 1 [ [hi]; [nth_default 0 p 0] ] in
          if (is_bounded_by bounds p) then
            (fst lo) ++ (skipn 1 (firstn n p))
          else
            let hi' := coef * (nth_default 0 p n) in
            add_to_nth 0 hi' (firstn n p).

    Definition reduce_full base s c n (p : list Z) :=
      let r1 := reduce1 base s c (2*n) (S n) p in
      let bound := (0, 2^machine_wordsize - 1) in
      let bounds := repeat bound n ++ [(0, up_bound-1)] in
      let r2 := reduce1 base s c (S n) (S n) r1 in
      let r3 := reduce3 base s c n r2 in
      if (is_bounded_by bounds r1) then r3
      else add_to_nth 0 (weight n * nth_default 0 r1 n) (firstn n r1).

    Definition mulmod' base s c n (p q : list Z) :=
      let prod := mul_no_reduce base n p q in
      let red := reduce_full base s c n prod in
      red.

    Definition reduce1_cps {T} base s c n m (p : list Z) (f : list Z -> T) :=
      let bound := (0, 2^machine_wordsize - 1) in
      if (is_bounded_by (repeat bound n) p) then
        let p_a := Positional.to_associational weight n p in
        let r_a := sat_reduce base s c n p_a in
        let r_rows := Saturated.Rows.from_associational weight m r_a in
        let r_flat := Saturated.Rows.flatten weight m r_rows in
        f (fst r_flat)
      else
        let p_a := Positional.to_associational weight n p in
        let r_a := sat_reduce base s c n p_a in
        let r_rows := Saturated.Rows.from_associational weight m r_a in
        let r_flat := Saturated.Rows.flatten weight m r_rows in
        f (add_to_nth 0 (weight (m) * snd r_flat) (fst r_flat)).

    Lemma reduce1_cps_ok {T} base s c n m (f : list Z -> T) : forall p,
        reduce1_cps base s c n m p f = f (reduce1 base s c n m p).
    Proof using Type.
      intros.
      cbv [reduce1 reduce1_cps].
      break_match; reflexivity.
    Qed.

    Definition reduce3_cps {T} base s c n (p : list Z) (f : list Z -> T) :=
      let bound := (0, 2^machine_wordsize-1) in
      let bounds := (repeat bound n) ++ [(0, 1)] in
      let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
      let coef_a := Saturated.Associational.sat_mul_const base [(1, s'/s)] c in
      let coef := Associational.eval coef_a in
      dlet_nd hi := Z.zselect (nth_default 0 p n) 0 coef in
          let lo := Saturated.Rows.flatten weight 1 [ [hi]; [nth_default 0 p 0] ] in
          if (is_bounded_by bounds p) then
            f ((fst lo) ++ (skipn 1 (firstn n p)))
          else
            let hi' := coef * (nth_default 0 p n) in
            f (add_to_nth 0 hi' (firstn n p)).

    Lemma reduce3_cps_ok {T} base s c n (f : list Z -> T) : forall p,
        reduce3_cps base s c n p f = f (reduce3 base s c n p).
    Proof.
      intros.
      cbv [reduce3 reduce3_cps].
      break_match; reflexivity.
    Qed.

    Definition reduce_full_cps {T} base s c n (p : list Z) (f : list Z -> T):=
      (r1 <- reduce1_cps base s c (2*n) (S n) p;
       (let bound := (0, 2^machine_wordsize - 1) in
        let bounds := repeat bound n ++ [(0, up_bound-1)] in
        r2 <- reduce1_cps base s c (S n) (S n) r1;
        (if (is_bounded_by bounds r1) then
           reduce3_cps base s c n r2 f
         else
           f (add_to_nth 0 (weight n * nth_default 0 r1 n) (firstn n r1))))).

    Definition reduce_full' base s c n p :=
      ltac:(let x := (eval cbv beta delta [reduce_full_cps reduce1_cps reduce3_cps id] in (@reduce_full_cps (list Z) base s c n p id)) in
            exact x).

    Lemma reduce_full_cps_ok {T} base s c n (f : list Z -> T) : forall p,
        reduce_full_cps base s c n p f = f (reduce_full base s c n p).
    Proof using Type.
      intros.
      cbv [reduce_full reduce_full_cps].
      repeat (rewrite reduce1_cps_ok ||
                rewrite reduce3_cps_ok ||
                  reflexivity ||
                    break_match).
    Qed.

    Definition mul_no_reduce_cps {T} base n (p q : list Z) (f : list Z -> T):=
      let p_a := Positional.to_associational weight n p in
      let q_a := Positional.to_associational weight n q in
      let pq_a := Saturated.Associational.sat_mul base p_a q_a in
      let pq_rows := Saturated.Rows.from_associational weight (2*n) pq_a in
      let pq := Saturated.Rows.flatten weight (2*n) pq_rows in
      let bound := (0, 2^machine_wordsize - 1) in
      if (is_bounded_by (repeat bound n) p) then
        if (is_bounded_by (repeat bound n) q) then
          f (fst pq)
        else
          f (add_to_nth 0 (weight (2 * n) * snd pq) (fst pq))
      else
        f (add_to_nth 0 (weight (2 * n) * snd pq) (fst pq)).

    Lemma mul_no_reduce_cps_ok {T} base n (f : list Z -> T) : forall p q,
        mul_no_reduce_cps base n p q f = f (mul_no_reduce base n p q).
    Proof using Type.
      intros.
      cbv [mul_no_reduce mul_no_reduce_cps].
      break_match; reflexivity.
    Qed.

    Definition mulmod_cps {T} base s c n (p q : list Z) (f : list Z -> T) :=
      (mul <- mul_no_reduce_cps base n p q;
       reduce_full_cps base s c n mul f).

    Lemma mulmod_cps_ok {T} base s c n (f : list Z -> T) : forall p q,
        mulmod_cps base s c n p q f = f (mulmod' base s c n p q).
    Proof using Type.
      intros.
      cbv [mulmod' mulmod_cps].
      rewrite mul_no_reduce_cps_ok, reduce_full_cps_ok.
      reflexivity.
    Qed.

    Definition mulmod base s c n (p q : list Z) :=
      ltac:(let x := (eval cbv beta delta [mulmod_cps mul_no_reduce_cps reduce_full_cps reduce1_cps reduce3_cps id] in (@mulmod_cps (list Z) base s c n p q id)) in
            exact x).

    Lemma mulmod_unfold base s c n : forall p q,
        mulmod' base s c n p q = mulmod_cps base s c n p q id.
    Proof using Type.
      intros.
      rewrite mulmod_cps_ok.
      reflexivity.
    Qed.

    Lemma mulmod_cps_conv base s c n : forall p q,
      mulmod base s c n p q = mulmod' base s c n p q.
    Proof using Type.
      intros.
      rewrite mulmod_unfold.
      reflexivity.
    Qed.

    Hint Resolve length_partition : push_length.
    Hint Resolve Rows.length_from_associational : push_length.

    Lemma split_lt w l1 l2:
      (forall x, In x l1 -> 0 < x < w) ->
      split w (combine l1 l2) = (combine l1 l2, []).
    Proof using Type.
      intros H.
      generalize dependent l2.
      induction l1 as [| ? ? IHl1]; intros l2; destruct l2; push;
        match goal with
        | [ |- context[ ?x :: ?y ] ] => replace (x :: y) with ([x] ++ y) by auto
        end;
        specialize (IHl1 ltac:(auto));
        specialize (H _ ltac:(auto));
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
    Proof using Type.
      intros H.
      generalize dependent l2.
      induction l1 as [| ? ? IHl1]; intros l2; destruct l2; push;
        match goal with
        | [ |- context[ ?x :: ?y ] ] => replace (x :: y) with ([x] ++ y) by eauto
        end;
        specialize (IHl1 ltac:(auto));
        specialize (H _ ltac:(auto));
        repeat multimatch goal with
               | H : ?x = 0, H1 : (?x =? 0) = false |- _ => rewrite H in H1
               | _ => rewrite IHl1
               | _ => push
               | _ => cbn
               | _ => lia
               | _ => auto
               | _ => break_match
               | _ => discriminate
               end.
    Qed.

    Lemma weight_mono' x :
      weight x < weight (S x).
    Proof using Type.
      weight_comp.
      rewrite Zred_factor0 at 1.
      rewrite Z.mul_comm.
      apply Zmult_lt_compat_r.
      apply Z.pow_pos_nonneg.
      all: lia.
    Qed.

    Lemma weight_mono'' x1 x2 :
      (x2 > 0)%nat
      -> weight x1 < weight (x2 + x1).
    Proof using Type.
      intros H.
      induction H as [| ? ? IHle];
        repeat match goal with
               | _ => apply IHle
               | _ => apply weight_mono'
               | _ => etransitivity
               end.
    Qed.

    Lemma weight_mono x1 x2 :
      (x1 < x2)%nat ->
      weight x1 < weight x2.
    Proof using Type.
      intros.
      replace x2%nat with ((x2 - x1) + x1)%nat by lia.
      apply weight_mono''; lia.
    Qed.

    Lemma weight_mono_le x1 x2 :
      (x1 <= x2)%nat ->
      weight x1 <= weight x2.
    Proof using Type.
      intros H.
      apply le_lt_or_eq in H.
      intuition.
      pose proof (weight_mono x1 x2 ltac:(auto)); lia.
      subst; lia.
    Qed.

    Lemma map_seq_start : forall a b,
        map weight (seq a b) =
          map (fun t => t * weight a) (map weight (seq 0 b)).
    Proof using Type.
      intros a b.
      induction b as [| ? IHb];
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

    Lemma eval_seq_start : forall a b p,
        Associational.eval (combine (map weight (seq a b)) p) =
          weight a * Associational.eval (combine (map weight (seq 0 b)) p).
    Proof using wprops.
      intros a b p.
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

    Lemma weight_dif_mono' : forall n,
        weight (S n) - weight n < weight (S (S n)) - weight (S n).
    Proof using Type.
      intros n.
      induction n.
      weight_comp; lia.
      cbv [weight].
      rewrite uweight_S; [ | lia].
      rewrite uweight_S with (n:=n) at 2; [ | lia].
      rewrite uweight_S with (n:=S (S n)); [ | lia].
      fold weight.
      rewrite <-!Z.mul_sub_distr_l.
      apply Zmult_lt_compat_l; unfold machine_wordsize; lia.
    Qed.

    Lemma weight_dif_mono : forall n m,
        (n < m)%nat ->
        weight (S n) - weight n < weight (S m) - weight m.
    Proof using Type.
      intros n m H.
      induction H;
        repeat multimatch goal with
               | _ => apply IHle
               | _ => apply weight_dif_mono'
               | _ => etransitivity
               end.
    Qed.

    Lemma weight_dif_lt : forall n m a,
        (n < m)%nat ->
        a < weight (S n) - weight n ->
        a < weight (S m) - weight m.
    Proof.
      intros n m a H H0.
      induction H.
      etransitivity; [| apply weight_dif_mono'].
      auto.
      etransitivity; [| apply weight_dif_mono'].
      auto.
    Qed.

    Section mulmod.

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
        intros p q.
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
        rewrite <-Z_div_mod_eq_full.
        auto.
        push.
        lia.
        push.

        push.
        rewrite <-Z_div_mod_eq_full.
        auto.
        push.
        lia.
        push.
      Qed.
      Hint Rewrite eval_mul_no_reduce : push_eval.

      Theorem length_mul_no_reduce : forall p q,
          length (mul_no_reduce base n p q) = (2 * n)%nat.
      Proof using base_nz n_gt_1 wprops.
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
        intros.
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
        intros.
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
      Proof using n_gt_1 wprops.
        intros m1 p ? ?.
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
        intros p m1 m2 H.
        intros.
        assert (Rows.adjust_s weight (S (S m1)) s =
                  Rows.adjust_s weight (S (S n)) s) as Hadjust.
        { destruct H.
          auto.
          rewrite solinas_property.
          eapply adjust_s_finished; try apply solinas_property.
          lia.
          lia. }
        cbv [s' coef reduce1].
        destruct (is_bounded_by (repeat (0, 2 ^ machine_wordsize - 1) m1) p) eqn:Heqb; push.
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
        all: push.
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
        intros p m1 m2; intros.
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

      (* SECTION REDUCE3 *)

      Lemma value_reduce1' : forall p m,
          m = n ->
          length p = S m ->
          nth_default 0 p n <= 1 ->
          (weight n / s * Associational.eval c) * (nth_default 0 p n) + eval weight n (firstn n p) < weight n ->
          let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
          let coef := Associational.sat_mul_const base [(1, s'/s)] c in
          eval weight m (reduce1 base s c (S m) m p) =
            Associational.eval coef * nth_default 0 p n + eval weight n (firstn n p).
      Proof.
        intros p m H H1 H2 H3.
        cbv [reduce1].
        rewrite H.
        push.
        erewrite adjust_s_finished'; try apply solinas_property.
        rewrite solinas_property.
        cbv [to_associational].
        push.
        const_simpl.
        rewrite skipn_nth_default with (d:=0) by lia.
        rewrite skipn_all.
        cbn [seq map].
        push.

        break_match.
        assert (0 <= nth_default 0 p n).
        apply is_bounded_by_nth with (n:=n) in Heqb.
        etransitivity.
        2: apply Heqb.
        rewrite nth_default_repeat.
        break_match; try lia.
        reflexivity.
        lia.
        push.

        push.
        rewrite Z.mod_small.
        reflexivity.
        solve_ineq.
        rewrite <-firstn_skipn with (l:=p) (n:=n) in Heqb.
        replace (S n) with (n + 1)%nat in Heqb by lia.
        rewrite repeat_app in Heqb.
        solve_ibb.
        auto.
        push.
        rewrite <-Z_div_mod_eq_full.
        all: push; lia.
      Qed.

      Lemma eval_reduce1' : forall p m,
          m = n ->
          length p = S m ->
          nth_default 0 p n <= 1 ->
          (weight n / s * Associational.eval c) * (nth_default 0 p n) + eval weight n (firstn n p) < weight n ->
          let s' := fst (Saturated.Rows.adjust_s weight (S (S n)) s) in
          let coef := Associational.sat_mul_const base [(1, s'/s)] c in
          let q := reduce1 base s c (S m) m p in
          (Positional.eval weight (S m) p) mod (s - Associational.eval c)
          = (Positional.eval weight m q) mod (s - Associational.eval c).
      Proof using base_nz c_pos coef_small mod_nz n_gt_1 s_pos solinas_property wprops.
        intros p m H H1 H2 H3 s' coef q.
        cbv [q].
        rewrite value_reduce1'; try lia.
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
        replace (S m) with (m+1)%nat by lia.
        cbv [eval to_associational].
        push.
        rewrite Z.mul_assoc.
        rewrite <-Z_div_exact_2.
        rewrite H.
        rewrite Z.add_cancel_l.
        const_simpl.
        rewrite eval_seq_start.
        f_equal.
        rewrite skipn_nth_default with (d:=0).
        rewrite skipn_all.
        cbn.
        break_match; lia.

        lia.
        lia.
        lia.
        pose proof (adjust_s_invariant (S (S n)) s ltac:(lia)) as Hadj.
        rewrite solinas_property in Hadj.
        intuition.
        push; lia.
        lia.
      Qed.

      Lemma firstn_nth_default_0 : forall p,
          length p > 0 ->
          firstn 1 p = [nth_default 0 p 0].
      Proof.
        intros p H.
        induction p as [| a p IHp].
        push' H.
        lia.
        push.
      Qed.

      Lemma eval_smaller m p :
          (length p <= m)%nat ->
          eval weight m p = eval weight (length p) p.
      Proof.
        intros H.
        destruct p using rev_ind.
        push.
        unfold eval at 1.
        cbv [to_associational].
        replace m with ((length (p ++ [x])) + (m - length (p ++ [x])))%nat.
        rewrite seq_app.
        rewrite map_app.
        rewrite combine_truncate_l.
        rewrite firstn_app_inleft.
        rewrite firstn_all.
        reflexivity.
        push.
        push.
        lia.
      Qed.

      Lemma eval_reduce3 : forall p,
          canonical_repr (S n) p ->
          (nth_default 0 p (n-1) = 0 /\ nth_default 0 p n = 1 /\ nth_default 0 p 0 < up_bound * up_bound + 1) \/ nth_default 0 p n = 0 ->
          let q := reduce3 base s c n p in
          (Positional.eval weight (S n) p) mod (s - Associational.eval c)
          = (Positional.eval weight n q) mod (s - Associational.eval c).
      Proof.
        intros.
        rewrite eval_reduce1'.
        rewrite value_reduce1'.
        rewrite solinas_property.
        push.
        const_simpl.
        cbv [q reduce3 Let_In].
        assert (Hcanon := H).
        unfold canonical_repr in Hcanon.
        destruct Hcanon.
        break_match.

        (* bounded *)
        pose proof (is_bounded_by_nth 0 _ _ Heqb ltac:(lia)) .
        specialize (H3 ltac:(push; try lia)).
        rewrite nth_default_app in H3.
        destruct (lt_dec 0 (Datatypes.length (repeat (0, 2 ^ machine_wordsize - 1) n))).
        rewrite nth_default_repeat in H3.
        destruct (dec (0 < n)%nat).
        push' H3.

        match goal with
        | |- context[fst (Rows.flatten weight 1 [ [?x]; [?y] ])] =>
            assert (fst (Rows.flatten weight 1 [ [x]; [y] ]) =
              [fst (Z.add_get_carry machine_wordsize x y)])
        end.
        { cbv [Z.add_get_carry Z.add_with_get_carry Z.add_with_carry Z.get_carry Let_In].
          rewrite solinas_property.
          push.
          rewrite !Rows.eval_cons.
          rewrite Rows.eval_nil.
          push.
          rewrite Partition.partition_step.
          push.
          intros.
          cbn in H4.
          intuition.
          rewrite <-H7; push.
          rewrite <-H4; push.
          rewrite <-H0; push.
          rewrite <-H4; push. }
        rewrite H4.

        cbv [Z.add_get_carry Z.add_with_get_carry Z.add_with_carry Z.get_carry Let_In Z.zselect].
        rewrite solinas_property.
        push.
        rewrite <-firstn_skipn with (l:=(firstn n p)) (n:=1%nat) at 1.
        rewrite firstn_firstn.
        rewrite firstn_nth_default_0.
        intuition.
        (* nth_default 0 p n = 1 *)
        rewrite H3.
        break_match; [lia|].
        push.

        f_equal.
        rewrite Z.mod_small.
        cbv [eval to_associational].
        destruct n eqn:E1.
        lia.
        cbn [seq map].
        replace (weight 0 :: map weight (seq 1 n0)) with ([weight 0] ++ map weight (seq 1 n0)) by auto.
        rewrite !combine_app_samelength.
        cbn [combine].
        rewrite !eval_app.
        push.
        lia.
        cbn; lia.
        cbn; lia.
        solve_ineq.
        etransitivity.
        apply Z.add_lt_mono.
        eauto.
        eauto.
        cbv [up_bound]; weight_comp; simpl; lia.

        (* nth_default 0 p n = 0 *)
        rewrite H3.
        break_match; [| lia].
        push.
        f_equal.
        rewrite Z.mod_small.
        lia.
        solve_ineq.
        lia.
        lia.
        lia.
        intuition.
        push' n0.
        lia.
        push' n0.
        lia.

        (* not bounded *)
        rewrite solinas_property.
        push.
        push; lia.
        push; lia.
        lia.
        solve_length p.
        lia.

        intuition.
        { rewrite H1.
          rewrite <-firstn_skipn with (n:=(n-1)%nat) (l:=firstn n p).
          rewrite firstn_firstn by lia.
          rewrite skipn_nth_default with (d:=0).
          rewrite skipn_all.
          rewrite nth_default_firstn.
          destruct le_dec.
          destruct lt_dec; [| lia].
          rewrite H0.
          cbv [eval to_associational].
          destruct n eqn:E; [lia|].
          rewrite seq_snoc.
          rewrite map_app, combine_app_samelength.
          rewrite eval_app.
          push.
          pose proof (firstn_skipn n0 p).
          symmetry in H2.
          canonical_app p.
          push' Hcanon_l.
          rewrite min_l in Hcanon_l by lia.
          pose proof (canonical_eval_bounded n0 (firstn n0 p) ltac:(auto)).
          etransitivity.
          cbv [eval to_associational] in H4.
          replace (S n0 - 1)%nat with (n0) by lia.
          apply Z.add_lt_le_mono.
          eauto.
          le_lt; eauto.
          cbv [up_bound].
          rewrite Z.add_sub_assoc.
          rewrite Z.add_sub_swap.
          rewrite Z.lt_add_lt_sub_r.
          apply weight_dif_lt with (n:=0%nat).
          lia.
          weight_comp; simpl; lia.
          push.
          lia.
          push.
          intuition.
          exfalso.
          apply n0.
          unfold canonical_repr in H.
          lia.
          push.
          lia.
          push.
          unfold canonical_repr in H.
          lia. }
        rewrite H1.
        ring_simplify.
        pose proof (firstn_skipn n p).
        symmetry in H0.
        canonical_app p.
        push' Hcanon_l.
        rewrite min_l in Hcanon_l; [|solve_length p].
        apply canonical_eval_bounded; auto.
        lia.
        solve_length p.
        lia.
        intuition.
        { rewrite H1.
          rewrite <-firstn_skipn with (n:=(n-1)%nat) (l:=firstn n p).
          rewrite firstn_firstn by lia.
          rewrite skipn_nth_default with (d:=0).
          rewrite skipn_all.
          rewrite nth_default_firstn.
          destruct le_dec.
          destruct lt_dec; [| lia].
          rewrite H0.
          cbv [eval to_associational].
          destruct n eqn:E; [lia|].
          rewrite seq_snoc.
          rewrite map_app, combine_app_samelength.
          rewrite eval_app.
          push.
          pose proof (firstn_skipn n0 p).
          symmetry in H2.
          canonical_app p.
          push' Hcanon_l.
          rewrite min_l in Hcanon_l by lia.
          pose proof (canonical_eval_bounded n0 (firstn n0 p) ltac:(auto)).
          etransitivity.
          cbv [eval to_associational] in H4.
          replace (S n0 - 1)%nat with (n0) by lia.
          apply Z.add_lt_le_mono.
          eauto.
          le_lt; eauto.
          cbv [up_bound].
          rewrite Z.add_sub_assoc.
          rewrite Z.add_sub_swap.
          rewrite Z.lt_add_lt_sub_r.
          apply weight_dif_lt with (n:=0%nat).
          lia.
          weight_comp; simpl; lia.
          push.
          lia.
          push.
          intuition.
          exfalso.
          apply n0.
          unfold canonical_repr in H.
          lia.
          push.
          lia.
          push.
          unfold canonical_repr in H.
          lia. }
        rewrite H1.
        ring_simplify.
        pose proof (firstn_skipn n p).
        symmetry in H0.
        canonical_app p.
        push' Hcanon_l.
        rewrite min_l in Hcanon_l; [|solve_length p].
        apply canonical_eval_bounded; auto.
      Qed.

      (* END SECTION REDUCE3 *)

      (* SECTION REDUCE_FIRST *)

      Lemma reduce_first_canonical : forall p,
          length p = (2 * n)%nat ->
          is_bounded_by (repeat (0, 2 ^ machine_wordsize - 1) (2 * n)) p = true->
          canonical_repr (S n) (reduce1 base s c (2*n) (S n) p).
      Proof using base_nz c_pos coef_small n_gt_1 s_pos solinas_property wprops.
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
        apply Z.pow_pos_nonneg; lia.
        all: cbn; break_match; lia.
      Qed.

      (* END SECTION REDUCE_FIRST *)

      (* SECTION REDUCE_SECOND *)

      Lemma reduce_second_canonical : forall p,
          canonical_repr (S n) p ->
          canonical_repr (S n) (reduce1 base s c (S n) (S n) p).
      Proof using base_nz c_pos coef_small n_gt_1 s_pos solinas_property wprops.
        intros p H.
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

      Lemma up_bound_weight1 : forall m,
          (m > 1)%nat ->
          up_bound * weight 1 < weight (S m) - weight m.
      Proof.
        intros m H.
        induction H.
        cbv [up_bound].
        weight_comp; try lia.
        simpl; break_match; lia.
        etransitivity.
        2: apply weight_dif_mono'.
        auto.
      Qed.

      Hint Rewrite nth_default_partition : push_misc.
      Lemma reduce_second_bounds : forall p,
          canonical_repr (S n) p ->
          (nth_default 0 p n) < up_bound ->
          let q := reduce1 base s c (S n) (S n) p in
          (nth_default 0 q (n-1) = 0 /\ nth_default 0 q n = 1 /\ nth_default 0 q 0 < up_bound * up_bound + 1) \/
            nth_default 0 q n = 0.
      Proof using base_nz c_pos coef_small n_gt_1 s_pos solinas_property wprops.
        intros p ? ? q.
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

        assert (Hcanonq' := Hcanonq).
        destruct Hcanonq as [ _ Hpartq].
        rewrite Hpartq.
        rewrite nth_default_partition.
        rewrite weight_0.
        rewrite Z.div_1_r.
        assert (eval weight (S n) q = eval weight n (firstn n q) + weight n).
        { rewrite Hq at 1.
          rewrite skipn_nth_default with (d:=0).
          rewrite skipn_all.
          rewrite eval_snoc_S.
          lia.
          push.
          rewrite min_l.
          lia.
          solve_length q.
          solve_length q.
          solve_length q. }
        assert (eval weight (S n) q = weight n / s * Associational.eval c * nth_default 0 p n + eval weight n (firstn n p)).
        { unfold q at 1.
          rewrite value_reduce1.
          rewrite solinas_property.
          push.
          const_simpl.
          unfold eval at 1.
          unfold to_associational at 1.
          rewrite skipn_nth_default with (d:=0).
          rewrite skipn_all.
          cbn [seq map combine].
          push.
          solve_length p.
          solve_length p.
          lia.
          lia.
          solve_length p.
          const_simpl.
          rewrite Z.lt_add_lt_sub_r.
          apply up_bound_weight1; lia. }
        rewrite H1 in H4.
        apply LinearSubstitute.Z.move_R_pX in H4.
        rewrite H1.
        rewrite PullPush.Z.add_mod_r.
        rewrite Weight.weight_multiples_full.
        const_simpl.
        rewrite Z.mod_small.
        rewrite H4.
        etransitivity.
        apply Z.add_lt_mono_r.
        apply Z.add_lt_mono.
        apply Z.mul_lt_mono_nonneg.
        solve_ineq.
        eauto.
        eapply canonical_bounded with (n:=S n) (p:=p).
        auto.
        rewrite Hp.
        rewrite nth_default_app.
        break_match.
        push' H5.
        rewrite min_l in H5.
        lia.
        lia.
        push.
        rewrite min_l.
        rewrite Nat.sub_diag.
        rewrite skipn_nth_default with (d:=0).
        rewrite skipn_all.
        apply in_or_app.
        right.
        push.
        solve_length p.
        solve_length p.
        solve_length p.
        eauto.
        apply canonical_eval_bounded.
        eauto.
        lia.
        solve_ineq.
        apply canonical_pos; auto.
        rewrite H4.
        etransitivity.
        apply Z.add_lt_mono_r.
        apply Z.add_lt_mono.
        apply Z.mul_lt_mono_nonneg.
        solve_ineq.
        eauto.
        eapply canonical_bounded with (n:=S n) (p:=p).
        auto.
        rewrite Hp.
        rewrite nth_default_app.
        break_match.
        push' H5.
        rewrite min_l in H5.
        lia.
        lia.
        push.
        rewrite min_l.
        rewrite Nat.sub_diag.
        rewrite skipn_nth_default with (d:=0).
        rewrite skipn_all.
        apply in_or_app.
        right.
        push.
        solve_length p.
        solve_length p.
        solve_length p.
        eauto.
        apply canonical_eval_bounded.
        eauto.
        rewrite <-Z.add_assoc.
        rewrite Z.add_opp_diag_r.
        const_simpl.
        cbv [up_bound].
        weight_comp.
        simpl; break_match; lia.
        lia.
        lia.
        auto.
        auto.
        lia.
        auto.
        lia.
      Qed.

      (* END SECTION REDUCE_SECOND *)

      (* (* SECTION REDUCE_THIRD *) *)

      (* Lemma eval_reduce_third' : forall p, *)
      (*     (canonical_repr (S n) p) -> *)
      (*     let q := reduce3 base s c n p in *)
      (*     ((nth_default 0 p (n-1) = 0 /\ nth_default 0 q n = 1 /\ nth_default 0 q 0 < up_bound * up_bound + 1) \/ nth_default 0 q n = 0) -> *)
      (*     (Positional.eval weight (S n) p) mod (s - Associational.eval c) *)
      (*     = (Positional.eval weight n q) mod (s - Associational.eval c). *)
      (* Proof. *)
      (*   intros p ? q ?. *)
      (*   cbv [q]. *)
      (*   rewrite eval_reduce3. *)
      (*   lia. *)
      (*   lia. *)
      (*   solve_length p. *)
      (* Qed. *)

      (* (* END SECTION REDUCE_THIRD *) *)

      (* SECTION REDUCE_FULL] *)
      Theorem reduce_full_correct : forall (p : list Z),
          n <= length p ->
          let r := reduce_full base s c n p in
          (Positional.eval weight (2 * n) p) mod (s - Associational.eval c)
          = (Positional.eval weight n r) mod (s - Associational.eval c).
      Proof.
        intros p ? r; cbv [r reduce_full]; break_match.
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
        rewrite <-eval_reduce3.
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
        apply Zmult_lt_compat_r.
        apply Z.pow_pos_nonneg; cbn; break_match; lia.
        cbn; lia.
        rewrite Z.lt_add_lt_sub_r.
        etransitivity; [| apply (weight_dif_mono 1); lia].
        weight_comp; cbn; break_match; lia.
        autounfold.
        replace (S n) with (n+1)%nat.
        cbn.
        const_simpl.
        replace (n+1)%nat with (S n) by lia.
        lia.
        lia.
        cbv [fold_andb_map' dual_map].
        cbn [repeat].
        rewrite repeat_cons.
        rewrite combine_app_samelength.
        rewrite map_app.
        rewrite fold_right_app.
        cbn.
        pose proof (bounds_same (repeat (0, 18446744073709551615) n)).
        auto.
        auto.

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
        apply Zmult_lt_compat_r.
        apply Z.pow_pos_nonneg; cbn; break_match; lia.
        cbn; lia.
      Qed.

      (* END SECTION REDUCE_FULL *)

      (* SECTION MULMOD *)
      Theorem mulmod'_correct : forall p q,
          Positional.eval weight n (mulmod' base s c n p q) mod (s - Associational.eval c) =
            (Positional.eval weight n p * Positional.eval weight n q) mod (s - Associational.eval c).
      Proof using base_nz c_pos coef_small mod_nz n_gt_1 s_pos solinas_property wprops.
        intros.
        cbv [mulmod'].
        rewrite <-reduce_full_correct; push; lia.
      Qed.

      Theorem mulmod_correct : forall p q,
          Positional.eval weight n (mulmod base s c n p q) mod (s - Associational.eval c) =
            (Positional.eval weight n p * Positional.eval weight n q) mod (s - Associational.eval c).
      Proof using base_nz c_pos coef_small mod_nz n_gt_1 s_pos solinas_property wprops.
        intros.
        rewrite mulmod_cps_conv.
        apply mulmod'_correct.
      Qed.
      (* END SECTION MULMOD *)

    End mulmod.

    Section squaremod.

      Definition sqr_indiv' base (state : list (Z * Z)) (p : list (Z * Z)) :=
        fold_right (fun a b => b ++ Associational.sat_mul base [a] [a]) state p.

      Definition sqr_indiv base (p : list (Z * Z)) :=
        sqr_indiv' base [] p.

      Definition square1 base (p : list (Z * Z)) :=
         let prod0 := Saturated.Associational.sat_mul base (firstn 1 p) (skipn 1 p) in
         let prod1 := Saturated.Associational.sat_mul base (skipn 3 p) (firstn 2 (skipn 1 p)) in
         let carry1_a := prod0 ++ prod1 in
        let carry1_rows := Saturated.Rows.from_associational weight 7 carry1_a in
        let carry1 := Saturated.Rows.flatten weight 7 carry1_rows in
         let prod2 := Saturated.Associational.sat_mul base (firstn 1 (skipn 1 p)) (firstn 1 (skipn 2 p)) in
        let carry2_rows := Saturated.Rows.from_associational weight 7 prod2 in
        let carry2 := Saturated.Rows.flatten' weight carry1 carry2_rows in
        let carry2 := (fst carry2) ++ [snd carry2] in
        carry2.

      Definition square_no_reduce base n (p : list Z) :=
        let p_a := Positional.to_associational weight 4 p in
        let carry2 := square1 base p_a in
        let double := Saturated.Rows.flatten weight 8 [carry2; carry2] in
        let square_a := sqr_indiv base p_a in
        let square_rows := Saturated.Rows.from_associational weight 8 square_a in
        let square := Saturated.Rows.flatten' weight double square_rows in
        let bound := (0, 2^machine_wordsize-1) in
        if ((n =? 4)%nat) then
          if ((length p =? 4)%nat) then
            if (is_bounded_by (repeat bound 4) p) then
              fst square
            else
              mul_no_reduce base n p p
          else
            mul_no_reduce base n p p
        else
          mul_no_reduce base n p p.

      Definition square_no_reduce_cps {T} base n (p : list Z) (f : list Z -> T) :=
        let p_a := Positional.to_associational weight 4 p in
        let carry2 := square1 base p_a in
        let double := Saturated.Rows.flatten weight 8 [carry2; carry2] in
        let square_a := sqr_indiv base p_a in
        let square_rows := Saturated.Rows.from_associational weight 8 square_a in
        let square := Saturated.Rows.flatten' weight double square_rows in
        let bound := (0, 2^machine_wordsize-1) in
        if ((n =? 4)%nat) then
          if ((length p =? 4)%nat) then
            if (is_bounded_by (repeat bound 4) p) then
              f (fst square)
            else
              mul_no_reduce_cps base n p p f
          else
            mul_no_reduce_cps base n p p f
        else
          mul_no_reduce_cps base n p p f.

      Definition squaremod' base s c n (p : list Z) :=
        let sqr := square_no_reduce base n p in
        let r := reduce_full base s c n sqr in
        r.

      Definition squaremod_cps {T} base s c n (p : list Z) (f : list Z -> T) :=
        (sqr <- square_no_reduce_cps base n p;
         reduce_full_cps base s c n sqr f).

      Definition squaremod base s c n (p : list Z) :=
        ltac:(let x := (eval cbv beta delta [squaremod_cps square_no_reduce_cps mul_no_reduce_cps reduce_full_cps reduce1_cps reduce3_cps id] in (@squaremod_cps (list Z) base s c n p id)) in
              exact x).

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

      Lemma square_no_reduce_cps_ok {T} (f : list Z -> T) : forall p,
          square_no_reduce_cps base n p f = f (square_no_reduce base n p).
      Proof.
        intros.
        cbv [square_no_reduce square_no_reduce_cps].
        break_match.
        reflexivity.
        apply mul_no_reduce_cps_ok.
        apply mul_no_reduce_cps_ok.
        apply mul_no_reduce_cps_ok.
      Qed.

      Lemma squaremod_cps_ok : forall {T} p (f : list Z -> T),
          squaremod_cps base s c n p f = f (squaremod' base s c n p).
      Proof.
        intros.
        cbv [squaremod' squaremod_cps].
        rewrite square_no_reduce_cps_ok, reduce_full_cps_ok.
        reflexivity.
      Qed.

      Lemma squaremod_unfold : forall p,
          squaremod' base s c n p = squaremod_cps base s c n p id.
      Proof.
        intros.
        rewrite squaremod_cps_ok.
        reflexivity.
      Qed.

      Lemma squaremod_cps_conv : forall p,
          squaremod base s c n p = squaremod' base s c n p.
      Proof.
        intros.
        rewrite squaremod_unfold.
        reflexivity.
      Qed.

      Lemma sat_mul_comm (p q : list (Z * Z)) :
        Associational.eval (Associational.sat_mul base p q) =
          Associational.eval (Associational.sat_mul base q p).
      Proof using base_nz n_gt_1. push; lia. Qed.

      Lemma sat_mul_distr (p q1 q2 : list (Z * Z)) :
        Associational.eval (Associational.sat_mul base p (q1 ++ q2)) =
          Associational.eval (Associational.sat_mul base p q1) +
            Associational.eval (Associational.sat_mul base p q2).
      Proof using base_nz n_gt_1. push; lia. Qed.

      Lemma cons_to_app {A} a (p : list A) :
        a :: p = [a] ++ p.
      Proof. reflexivity. Qed.

      Lemma flatten'_mod state (inp : list (list Z)) (m : nat) :
        inp <> [] ->
        Datatypes.length (fst state) = m ->
        (forall row : list Z, In row inp -> Datatypes.length row = m) ->
        eval weight m (fst (Rows.flatten' weight state inp)) =
          (Rows.eval weight m inp + eval weight m (fst state) + weight m * snd state) mod weight m.
      Proof using n_gt_1 wprops.
        intros.
        rewrite Rows.flatten'_correct with (n:=m) by auto.
        push.
        f_equal.
        lia.
      Qed.

      Hint Rewrite Nat.sub_diag : const_simpl.
      Hint Rewrite Z.sub_diag : const_simpl.

      Lemma sum_one x :
        sum [x] = x.
      Proof. cbn; lia. Qed.

      Lemma square_indiv_cons (p : list (Z * Z)) (a : Z * Z) :
        Associational.eval (sqr_indiv base (a :: p)) =
          Associational.eval (sqr_indiv base [a]) +
            Associational.eval (sqr_indiv base p).
      Proof using base_nz n_gt_1.
        cbv [sqr_indiv sqr_indiv'].
        cbn [fold_right].
        push.
        lia.
      Qed.

      Lemma square_indiv_app (p q : list (Z * Z)) :
        Associational.eval (sqr_indiv base (p ++ q)) =
          Associational.eval (sqr_indiv base p) + Associational.eval (sqr_indiv base q).
      Proof using base_nz n_gt_1.
        generalize dependent q.
        induction p as [| a p IHp] using rev_ind; intros q.
        push.
        rewrite <-app_assoc.
        rewrite !IHp.
        rewrite <-cons_to_app.
        rewrite square_indiv_cons.
        lia.
      Qed.

      Lemma eval_square_indiv (p : list Z) : forall x x0 x1 x2 q,
        p = x :: x0 :: x1 :: x2 :: q ->
        Associational.eval (sqr_indiv base (to_associational weight 4 p)) = (Associational.eval (sat_mul base [(weight 0, x)] [(weight 0, x)]) +
                                                                               (Associational.eval (sat_mul base [(weight 1, x0)] [(weight 1, x0)]) +
                                                                                  (Associational.eval (sat_mul base [(weight 2, x1)] [(weight 2, x1)]) +
                                                                                     Associational.eval (sat_mul base [(weight 3, x2)] [(weight 3, x2)])))).
      Proof using base_nz wprops n_gt_1.
        intros x x0 x1 x2 q H.
        rewrite H.
        cbv [to_associational].
        cbn [seq map weight combine].
        repeat multimatch goal with
               | |- _ => rewrite app_comm_cons
               | |- context[?x :: ?y :: ?z] =>
                   rewrite cons_to_app with (a:=x) (p:=y::z)
               | |- context[?x ++ ?y :: ?z] =>
                   rewrite cons_to_app with (a:=y) (p:=z);
                   rewrite app_nil_r
               end.
        rewrite !square_indiv_app.
        cbv [sqr_indiv sqr_indiv'].
        cbn [fold_right].
        push.
      Qed.

      Lemma length_square1 (p : list Z) : forall x x0 x1 x2 q,
        p = x :: x0 :: x1 :: x2 :: q ->
        length (square1 base (to_associational weight 4 p)) = 8%nat.
      Proof using base_nz wprops n_gt_1.
        intros x x0 x1 x2 q H.
        cbv [square1].
        push.
        rewrite Rows.flatten'_correct with (n:=7%nat).
        push.
        auto.
        push.
        intros.
        eapply Rows.length_from_associational.
        eauto.
        apply Rows.from_associational_nonnil.
        lia.
        rewrite H.
        discriminate.
      Qed.

      Lemma eval_square1 (p : list Z) : forall x x0 x1 x2 q,
          let bound := (0, 2^machine_wordsize-1) in
          is_bounded_by (repeat bound 4) p = true ->
          p = x :: x0 :: x1 :: x2 :: q ->
          eval weight 8 (square1 base (Positional.to_associational weight 4 p)) =
            Associational.eval (sat_mul base [(weight 1, x0)] [(weight 2, x1)]) +
              (Associational.eval (sat_mul base [(weight 0, x)] [(weight 1, x0)]) +
                 (Associational.eval (sat_mul base [(weight 0, x)] [(weight 2, x1)]) +
                    Associational.eval (sat_mul base [(weight 0, x)] [(weight 3, x2)])) +
                 (Associational.eval (sat_mul base [(weight 3, x2)] [(weight 1, x0)]) +
                    Associational.eval (sat_mul base [(weight 3, x2)] [(weight 2, x1)]))).
      Proof using base_nz wprops n_gt_1.
        intros x x0 x1 x2 q bound H H1.
        rewrite H1.
        cbv [to_associational].
        cbn [seq map combine].
        cbv [square1].
        cbn [firstn skipn].

        rewrite H1 in H.
        cbv [is_bounded_by fold_andb_map' dual_map bound] in H.
        cbn [repeat combine map fold_right fst snd] in H.
        repeat match goal with
               | H : _ && _ = true |- _ => apply andb_prop in H
               | H : _ /\ _ |- _ => destruct H
               | H : _ <=? _ = true |- _ => rewrite Z.leb_le in H
               end.

        repeat multimatch goal with
               | |- _ => rewrite app_comm_cons
               | |- context[?x :: ?y :: ?z] =>
                   rewrite cons_to_app with (a:=x) (p:=y::z) by discriminate
               end.
        repeat multimatch goal with
               | _ => rewrite eval_snoc_S
               | _ => rewrite Rows.flatten_mod
               | _ => rewrite flatten'_mod
               | _ => rewrite Rows.flatten'_correct with (n:=7%nat); cbn [snd]
               | _ => rewrite Rows.flatten_correct; cbn [snd]
               | _ => rewrite Rows.eval_from_associational
               | _ => rewrite eval_app
               | _ => rewrite sat_mul_distr
               | _ => cbn [fst]
               end.
        all: repeat match goal with
                    | _ => assumption
                    | _ => lia
                    | |- Rows.from_associational _ _ _ <> [] =>
                        apply Rows.from_associational_nonnil
                    | |- context[length (Partition.partition _ _ _)] =>
                        autorewrite with push_length
                    | |- forall _ : _, In _ _ -> _ =>
                        intros; eapply Rows.length_from_associational; eassumption
                    | _ => discriminate
                    end.

        repeat rewrite Z.div_small.
        all: repeat match goal with
                    | |- context[_ mod _] => rewrite Z.mod_small
                    end.
        all: const_simpl; try lia.
        all: push; solve_ineq; le_lt; replace x with (weight 0 * x) by (weight_comp; lia); etransitivity; [
            repeat match goal with
                   | |- _ + _ <= _ => apply OrdersEx.Z_as_DT.add_le_mono
                   | |- _ * _ * _ <= _ => apply Z.mul_le_mono_nonneg
                   | |- _ * _ <= _ => apply OrdersEx.Z_as_DT.mul_le_mono_nonneg_l
                   | |- 0 <= _ => solve_ineq
                   | H : ?x <= _ |- ?x <= _ => eassumption
                   end | (weight_comp; lia) ].
      Qed.

      Lemma eval_square1_bounded (p : list Z) : forall x x0 x1 x2 q,
        let bound := (0, 2^machine_wordsize-1) in
        is_bounded_by (repeat bound 4) p = true ->
        p = x :: x0 :: x1 :: x2 :: q ->
        0 <= eval weight 8 (square1 base (to_associational weight 4 p)) < weight 7.
      Proof using base_nz wprops n_gt_1.
        intros x x0 x1 x2 q bound H H0.
        erewrite eval_square1; [| eauto | eauto].
        rewrite H0 in H.
        cbv [is_bounded_by fold_andb_map' dual_map bound] in H.
        cbn [repeat combine map fold_right fst snd] in H.
        repeat match goal with
               | H : _ && _ = true |- _ => apply andb_prop in H
               | H : _ /\ _ |- _ => destruct H
               | H : _ <=? _ = true |- _ => rewrite Z.leb_le in H
               end.
        push; solve_ineq; le_lt; replace x with (weight 0 * x) by (weight_comp; lia); etransitivity;
          [repeat match goal with
                  | |- _ + _ <= _ => apply OrdersEx.Z_as_DT.add_le_mono
                  | |- _ * _ * _ <= _ => apply Z.mul_le_mono_nonneg
                  | |- _ * _ <= _ => apply OrdersEx.Z_as_DT.mul_le_mono_nonneg_l
                  | |- 0 <= _ => solve_ineq
                  | H : ?x <= _ |- ?x <= _ => eassumption
                  end | (weight_comp; lia) ].
      Qed.

      Theorem eval_square_no_reduce (p : list Z) :
        eval weight (2 * n) (square_no_reduce base n p) = (eval weight n p) * (eval weight n p).
      Proof using base_nz wprops n_gt_1.
        rewrite <-eval_mul_no_reduce with (base:=base) by lia.
        cbv [square_no_reduce].
        break_match.

        rewrite Nat.eqb_eq in Heqb.
        rewrite Heqb.
        assert (exists p1 p2 p3 p4, p = p1 :: p2 :: p3 :: p4 :: nil).
        { repeat (destruct p; [cbn in Heqb0; lia|]).
          destruct p; [| cbn in Heqb0; lia].
          eauto. }
        destruct H; destruct H; destruct H; destruct H.

        pose proof (eval_square1_bounded p x x0 x1 x2 nil ltac:(auto) ltac:(auto)).

        rewrite flatten'_mod.
        rewrite Rows.flatten_mod.
        rewrite Rows.eval_from_associational.

        rewrite Zplus_mod.
        rewrite PullPush.Z.mul_mod_full.
        rewrite Z.mod_same.
        const_simpl.
        rewrite Zmod_mod.
        rewrite Zplus_mod.
        rewrite Zmod_mod.
        rewrite <-Zplus_mod.

        rewrite Rows.eval_cons.
        cbv [Rows.eval map].
        rewrite sum_one.
        erewrite eval_square1; try eapply H.
        erewrite eval_square_indiv; try eapply H.

        rewrite H.
        cbv [mul_no_reduce].
        break_match.
        replace (2*4)%nat with 8%nat by lia.
        cbv [to_associational].
        rewrite combine_firstn_l.
        cbn [seq map length].
        cbn [firstn seq map combine].
        repeat multimatch goal with
               | |- _ => rewrite app_comm_cons
               | |- context[?x :: ?y :: ?z] =>
                   rewrite cons_to_app with (a:=x) (p:=y::z)
               end.
        rewrite Rows.flatten_mod.
        rewrite Rows.eval_from_associational.
        rewrite !sat_mul_distr.
        repeat multimatch goal with
               | |- context[sat_mul _ (?y ++ ?z) ?x] => rewrite sat_mul_comm with (p:=(y ++ z)) (q:=x)
               end.
        rewrite !sat_mul_distr.
        push.
        f_equal.
        lia.
        auto.
        lia.
        auto.

        all: repeat match goal with
                    | |- forall _ : _, In _ _ -> _ =>
                        intros; eapply Rows.length_from_associational; eassumption
                    | _ => auto
                    end.
        rewrite H in Heqb1.
        rewrite Heqb1 in Heqb2.
        lia.
        repeat match goal with
               | H : In _ (_ :: _) |- _ =>
                   apply in_inv in H
               | H : In _ [] |- _ => apply in_nil in H; lia
               | H : _ = ?x |- length ?x = _ => rewrite <-H
               | _ => eapply length_square1; eauto
               | _ => intuition
               end.
        apply Rows.from_associational_nonnil.
        lia.
        rewrite H.
        discriminate.
        push.
        repeat match goal with
               | H : In _ (_ :: _) |- _ =>
                   apply in_inv in H
               | H : In _ [] |- _ => apply in_nil in H; lia
               | H : _ = ?x |- length ?x = _ => rewrite <-H
               | _ => eapply length_square1; eauto
               | _ => intuition
               end.
      Qed.

      Theorem length_square_no_reduce (p : list Z):
        length (square_no_reduce base n p) = (2 * n)%nat.
      Proof using base_nz wprops n_gt_1.
        cbv [square_no_reduce].
        break_match.
        rewrite Nat.eqb_eq in Heqb.
        assert (exists p1 p2 p3 p4, p = p1 :: p2 :: p3 :: p4 :: nil).
        { repeat (destruct p; [cbn in Heqb0; lia|]).
          destruct p; [| cbn in Heqb0; lia].
          eauto. }
        destruct H; destruct H; destruct H; destruct H.
        rewrite Rows.flatten'_correct with (n:=8%nat).
        push.
        lia.
        repeat match goal with
               | H : In _ (_ :: _) |- _ =>
                   apply in_inv in H
               | H : In _ [] |- _ => apply in_nil in H; lia
               | H : _ = ?x |- length ?x = _ => rewrite <-H
               | _ => eapply length_square1; eauto
               | _ => intuition
               end.
        auto.
        push.
        repeat match goal with
               | H : In _ (_ :: _) |- _ =>
                   apply in_inv in H
               | H : In _ [] |- _ => apply in_nil in H; lia
               | H : _ = ?x |- length ?x = _ => rewrite <-H
               | _ => eapply length_square1; eauto
               | _ => intuition
               end.
        intros; eapply Rows.length_from_associational; eauto.
        apply Rows.from_associational_nonnil.
        lia.
        rewrite H.
        discriminate.
        apply length_mul_no_reduce; auto.
        apply length_mul_no_reduce; auto.
        apply length_mul_no_reduce; auto.
      Qed.

      Lemma squaremod'_correct : forall p,
          Positional.eval weight n (squaremod' base s c n p) mod (s - Associational.eval c) =
            (Positional.eval weight n p * Positional.eval weight n p) mod (s - Associational.eval c).
      Proof using base_nz c_pos coef_small mod_nz n_gt_1 s_pos solinas_property wprops.
        intros.
        cbv [squaremod'].
        rewrite <-reduce_full_correct.
        rewrite eval_square_no_reduce.
        all: try lia.
        assumption.
        rewrite length_square_no_reduce.
        lia.
      Qed.

      Theorem squaremod_correct : forall p ,
          Positional.eval weight n (squaremod base s c n p) mod (s - Associational.eval c) =
            (Positional.eval weight n p * Positional.eval weight n p) mod (s - Associational.eval c).
      Proof using base_nz c_pos coef_small mod_nz n_gt_1 s_pos solinas_property wprops.
        intros.
        rewrite squaremod_cps_conv.
        apply squaremod'_correct.
      Qed.

    End squaremod.

  End __.

End SolinasReduction.
