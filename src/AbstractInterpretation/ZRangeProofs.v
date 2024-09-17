From Coq Require Import Lia.
From Coq Require Import ZArith.
From Coq Require Import Morphisms.
From Coq Require Import RelationPairs.
From Coq Require Import Relations.
From Coq Require Import List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.Operations.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.ZRange.SplitBounds.
Require Import Crypto.Util.ZRange.CornersMonotoneBounds.
Require Import Crypto.Util.ZRange.LandLorBounds.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.FoldBool.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Combine.
Require Import Crypto.Util.ZUtil.Le.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.ZUtil.Tactics.ReplaceNegWithPos.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Morphisms.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.PrintGoal.
Require Import Crypto.Util.Tactics.DoWithHyp.
Require Import Crypto.Language.PreExtra.
Require Import Crypto.CastLemmas.
Require Import Crypto.AbstractInterpretation.ZRange.
Require Import Crypto.AbstractInterpretation.ZRangeCommonProofs.
Import ListNotations. Import EqNotations.

Module Compilers.
  Import AbstractInterpretation.ZRange.Compilers.
  Import AbstractInterpretation.ZRangeCommonProofs.Compilers.
  Import Rewriter.Language.Wf.Compilers. (* for properties about type.related_hetero *)
  Export ZRange.Settings.

  Module ZRange.
    Module type.
      Module base.
        Module option.
          Lemma is_bounded_by_None t v : ZRange.type.base.option.is_bounded_by (@ZRange.type.base.option.None t) v = true.
          Proof. induction t; cbn; cbv [andb]; break_innermost_match; eauto. Qed.

          Lemma tighter_than_union t (rx ry : ZRange.type.base.option.interp t) :
            ZRange.type.base.option.is_tighter_than rx (ZRange.type.base.option.union rx ry) = true /\
              ZRange.type.base.option.is_tighter_than ry (ZRange.type.base.option.union rx ry) = true.
          Proof.
            induction t; [destruct t|..]; destruct rx, ry;
              cbn [
                  ZRange.type.base.interp
                    ZRange.type.base.option.interp
                    ZRange.type.base.option.is_tighter_than
                    ZRange.type.base.is_tighter_than
                    ZRange.type.base.option.union
                    Option.map2
                    Option.bind2
                ] in *; auto 2.
            all: fold (@ZRange.type.base.option.interp) in *.
            all: break_innermost_match; reflect_hyps; inversion_option; subst; auto 2.
            all: split_and.
            all: cbn [option_beq].
            all: rewrite ?Bool.andb_true_iff; auto.
            all: try now split; first [ apply ZRange.is_tighter_than_bool_union_l | apply ZRange.is_tighter_than_bool_union_r ].
            all: do 2 try (match goal with
                           | [ |- context[?x = true] ]
                             => lazymatch x with true => fail | false => fail | _ => idtac end;
                                destruct x eqn:?; progress reflect_hyps
                           end;
                           cbn [ZRange.type.base.option.None] in *;
                           auto 2; subst; try congruence).
            { rewrite 2 fold_andb_map_map.
              rewrite 2 fold_andb_map_iff.
              rewrite List.combine_length.
              do_with_hyp' ltac:(fun H => rewrite H).
              rewrite Nat.min_id.
              repeat split; intros *; destruct_head'_prod; cbn [uncurry fst snd].
              all: rewrite In_nth_error_iff.
              all: intros [n H']; revert H'.
              all: rewrite !nth_error_combine.
              all: break_innermost_match; intros; inversion_option; inversion_pair; subst; auto. }
          Qed.

          Lemma is_bounded_by_union_l t (rx ry : ZRange.type.base.option.interp t) x :
            ZRange.type.base.option.is_bounded_by rx x = true ->
            ZRange.type.base.option.is_bounded_by (ZRange.type.base.option.union rx ry) x = true.
          Proof.
            eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; try eassumption;
              eapply tighter_than_union.
          Qed.

          Lemma is_bounded_by_union_r t (rx ry : ZRange.type.base.option.interp t) y :
            ZRange.type.base.option.is_bounded_by ry y = true ->
            ZRange.type.base.option.is_bounded_by (ZRange.type.base.option.union rx ry) y = true.
          Proof.
            eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; try eassumption;
              eapply tighter_than_union.
          Qed.
        End option.
      End base.

      Module option.
        Lemma app_curried_None {t args} : type.app_curried (@ZRange.type.option.None t) args = ZRange.type.base.option.None.
        Proof. induction t; cbn; auto. Qed.

        Lemma is_bounded_by_impl_related_hetero t
          (x : ZRange.type.option.interp t) (v : type.interp base.interp t)
        : ZRange.type.option.is_bounded_by x v = true
          -> type.related_hetero (fun t x v => ZRange.type.base.option.is_bounded_by x v = true) x v.
        Proof. induction t; cbn in *; intuition congruence. Qed.

        Lemma is_bounded_by_impl_related_hetero_and_Proper {skip_base} t
              (x : ZRange.type.option.interp t) (v : type.interp base.interp t)
        : ZRange.type.option.is_bounded_by x v = true
          -> type.related_hetero_and_Proper (skip_base:=skip_base) (fun _ => eq) (fun _ => eq) (fun t x v => ZRange.type.base.option.is_bounded_by x v = true) x v.
        Proof. induction t; cbn in *; break_innermost_match; intuition congruence. Qed.

        Lemma is_bounded_by_impl_eqv_refl t
          (x : ZRange.type.option.interp t) (v : type.interp base.interp t)
          : ZRange.type.option.is_bounded_by x v = true
            -> x == x /\ v == v.
        Proof. induction t; cbn; split; try reflexivity; try congruence. Qed.

        Lemma is_bounded_by_impl_eqv_refl1 t
          (x : ZRange.type.option.interp t) (v : type.interp base.interp t)
          : ZRange.type.option.is_bounded_by x v = true
            -> x == x.
        Proof. intros; eapply is_bounded_by_impl_eqv_refl; eassumption. Qed.

        Lemma is_bounded_by_impl_eqv_refl2 t
          (x : ZRange.type.option.interp t) (v : type.interp base.interp t)
          : ZRange.type.option.is_bounded_by x v = true
            -> v == v.
        Proof. intros; eapply is_bounded_by_impl_eqv_refl; eassumption. Qed.

        Lemma andb_bool_for_each_lhs_of_arrow_is_bounded_by_impl_and_for_each_lhs_of_arrow_eqv_refl t
          (x : type.for_each_lhs_of_arrow ZRange.type.option.interp t) (v : type.for_each_lhs_of_arrow (type.interp base.interp) t)
          : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) x v = true
            -> type.and_for_each_lhs_of_arrow (@type.eqv) v v.
        Proof.
          induction t; cbn; [ reflexivity | ].
          rewrite Bool.andb_true_iff.
          intros [H0 H1].
          split; eauto using is_bounded_by_impl_eqv_refl2.
        Qed.
      End option.
    End type.

    Module ident.
      Module option.
        (** First we prove relatedness for some particularly complicated identifiers separately *)
        Section interp_related.
          Context {shiftr_avoid_uint1 : shiftr_avoid_uint1_opt}
                  (assume_cast_truncates : bool).
          Local Notation interp_is_related idc
            := (type.related_hetero
                  (fun t st v => ZRange.type.base.option.is_bounded_by st v = true)
                  (ZRange.ident.option.interp assume_cast_truncates idc)
                  (ident.interp idc)).
          Local Notation interp_is_related_and_Proper idc
            := (type.related_hetero_and_Proper
                  (skip_base:=true)
                  (fun t => eq)
                  (fun t => eq)
                  (fun t st v => ZRange.type.base.option.is_bounded_by st v = true)
                  (ZRange.ident.option.interp assume_cast_truncates idc)
                  (ident.interp idc)).

          Local Ltac z_cast_t :=
            cbn [type.related_hetero ZRange.ident.option.interp ident.interp respectful_hetero type.interp ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp ZRange.type.base.option.Some];
            cbv [ZRange.ident.option.interp_Z_cast ZRange.ident.option.interp_Z_cast_truncate ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by respectful_hetero];
            cbn [base.interp_beq base.base_interp_beq option_map] in *;
            cbv [ident.cast2] in *; cbn [fst snd] in *;
            intros; break_innermost_match; break_innermost_match_hyps; trivial;
            cbn [option_map] in *; inversion_option;
            rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff in *; destruct_head'_and; destruct_head'_or; repeat apply conj; Z.ltb_to_lt;
            reflect_beq_to_eq zrange_beq; subst;
            rewrite ?ident.cast_in_bounds by (eapply ZRange.is_bounded_by_iff_is_tighter_than; eauto);
            try reflexivity; try lia; try assumption;
            auto using ident.cast_always_bounded.

          Lemma interp_related_Z_cast : interp_is_related ident.Z_cast.
          Proof using Type. z_cast_t. Qed.

          Lemma interp_related_Z_cast2 : interp_is_related ident.Z_cast2.
          Proof using Type. z_cast_t. Qed.

          Lemma interp_related_List_flat_map A B : interp_is_related (@ident.List_flat_map A B).
          Proof using Type.
            cbn; cbv [respectful_hetero]; intros.
            destruct_head' option; cbn in *; [ | reflexivity ].
            break_match; cbn in *; [ | reflexivity ].
            rewrite fold_andb_map_iff in *.
            rewrite OptionList.fold_right_option_seq in *.
            destruct_head'_ex.
            destruct_head'_and.
            rewrite List.flat_map_concat_map, concat_fold_right_app.
            subst.
            lazymatch goal with
            | [ H : List.map _ ?ls1 = List.map _ ?ls' |- length (List.fold_right _ _ ?ls1) = length (List.fold_right _ _ (List.map _ ?ls2)) /\ _ ]
              => is_var ls1; is_var ls2; is_var ls';
                   revert dependent ls'; intro ls'; revert dependent ls2; revert ls'; induction ls1 as [|? xs IHxs];
                     intros [|? ls'] [|? ls2]; cbn [length] in *; intros; cbn in *;
                     [ tauto | exfalso; discriminate.. | ]
            end.
            repeat first [ progress cbn in *
                         | progress subst
                         | discriminate
                         | congruence
                         | progress autorewrite with distr_length
                         | progress destruct_head'_and
                         | rewrite combine_app_samelength
                         | rewrite fold_andb_map_iff in *
                         | specialize (IHxs _ _ ltac:(eassumption) ltac:(eassumption) ltac:(eassumption))
                         | match goal with
                           | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
                           | [ H : S _ = S _ |- _ ] => inversion H; clear H
                           | [ H : forall v, _ = v \/ _ -> _ |- _ ] => pose proof (H _ (or_introl eq_refl)); specialize (fun v pf => H v (or_intror pf))
                           | [ H : forall x y, ?R x y = true -> match ?f x with Some _ => _ | None => _ end = true, H' : Some _ = ?f ?x' |- _ ]
                             => specialize (H _ _ ltac:(eassumption)); rewrite <- H' in H
                           | [ |- context[List.In _ (_ ++ _)] ] => setoid_rewrite List.in_app_iff
                           end
                         | solve [ intuition ] ].
          Qed.

          Lemma interp_related_List_partition A : interp_is_related (@ident.List_partition A).
          Proof using Type.
            cbn; cbv [respectful_hetero]; intros.
            destruct_head' option; cbn in *; [ | break_innermost_match; reflexivity ].
            rewrite fold_andb_map_iff in *.
            destruct_head'_ex.
            destruct_head'_and.
            repeat break_match_step ltac:(fun v => let t := type of v in match (eval hnf in t) with prod _ _ => idtac end).
            repeat match goal with H : option (list _) |- _ => revert dependent H end.
            lazymatch goal with
            | [ Heq : List.partition _ _ = (?l0, ?l1), H : length ?ls1 = length ?ls2 |- _ ]
              => is_var ls1; is_var ls2; is_var l0; is_var l1;
                   revert dependent l0; intro l0; revert dependent l1; intro l1;
                     revert dependent ls2; intro ls2;
                       revert ls2 l0 l1;
                       induction ls1 as [|? xs IHxs]; intros [|? ls2]; cbn [length] in *; cbn in *;
                         [ intros [|? ?] [|? ?]; cbn in *; intros; break_innermost_match; cbn in *;
                           inversion_prod; inversion_option; subst..
                         | ];
                         [ tauto | exfalso; discriminate.. | intros ]
            end.
            repeat first [ progress cbn in *
                         | progress subst
                         | match goal with
                           | [ H : S _ = S _ |- _ ] => inversion H; clear H
                           end
                         | discriminate
                         | congruence
                         | progress destruct_head'_and
                         | progress inversion_prod
                         | progress eta_expand
                         | rewrite Bool.if_const
                         | specialize (fun l0 l1 => IHxs _ l0 l1 ltac:(eassumption))
                         | specialize (fun l0 l1 => IHxs l0 l1 ltac:(eassumption))
                         | specialize (IHxs _ _ (@surjective_pairing _ _ _))
                         | progress Bool.split_andb
                         | match goal with
                           | [ |- context[(_ <- ?x; _)%option] ] => destruct x eqn:?
                           | [ H : bool_eq _ _ = true |- _ ] => apply bool_eq_ok in H
                           | [ H : forall v, _ = v \/ _ -> _ |- _ ] => pose proof (H _ (or_introl eq_refl)); specialize (fun v pf => H v (or_intror pf))
                           | [ |- context[match ?b with true => ?f ?x | false => ?f ?y end] ]
                             => replace (match b with true => f x | false => f y end)
                               with (f match b with true => x | false => y end)
                                    by now case b
                           | [ H : context[match ?b with true => ?f ?x | false => ?f ?y end] |- _ ]
                             => replace (match b with true => f x | false => f y end)
                               with (f match b with true => x | false => y end)
                               in H
                               by now case b
                           | [ H : _ = (_, _) -> _ |- _ ] => specialize (fun pf1 pf2 => H (@path_prod _ _ _ _ pf1 pf2))
                           | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
                           | [ H : ?x = _ :> bool |- context[?x] ] => rewrite H
                           | [ H : forall x y, ?R x y = true -> match ?f x with Some _ => _ | None => _ end _ = true, H' : ?f ?x' = Some _ |- _ ]
                             => specialize (H _ _ ltac:(eassumption)); rewrite H' in H
                           end
                         | progress break_innermost_match_step ].
          Qed.

          Lemma interp_related_List_filter A : interp_is_related (@ident.List_filter A).
          Proof using Type.
            cbn; cbv [respectful_hetero]. intros f g H0 l1 l2 H1.
            destruct l1 as [l1|]; try reflexivity.
            destruct (list_rect _ _) as [l3 |] eqn:E; try reflexivity.
            rewrite fold_andb_map_iff in *. destruct H1 as [H1 H2].
            cbv [list_rect] in E. generalize dependent l2. generalize dependent l3.
            induction l1 as [|a l1' IHl1'].
            - intros l3 E l2 H1 H2. injection E as E. subst. simpl. simpl in H1.
              destruct l2 as [|l2_0 l2']; try discriminate H1. constructor.
              + reflexivity.
              + intros v H. destruct H.
            - intros l3 E l2 H1 H2. cbv [bind] in E.
              destruct (f a) as [ [|]|] eqn:E'; try discriminate E.
              + destruct (_ l1') as [v|] eqn:E''; try discriminate E.
                destruct l3 as [| a' l3']; try discriminate E.
                injection E as E1 E2. subst. destruct l2 as [| a l2']; try discriminate H1.
                injection H1 as H1. assert (Htemp: Some l3' = Some l3') by reflexivity.
                simpl in H2. remember (IHl1' l3' Htemp l2' H1) as IHl1'' eqn:clearMe.
                clear IHl1' clearMe. assert (IHhyp: forall v, List.In v (List.combine l1' l2') ->
                                                              ZRange.type.base.option.is_bounded_by (fst v) (snd v) = true).
                { intros v H. apply H2. right. apply H. }
                apply IHl1'' in IHhyp. clear IHl1''. destruct IHhyp as [IH1 IH2].
                assert (H2': ZRange.type.base.option.is_bounded_by a' a = true).
                { apply (H2 (pair a' a)). simpl. left. reflexivity. }
                clear H2. remember (H0 _ _ H2') as H0' eqn:clearMe. clear H0 clearMe.
                destruct (f a') as [r|]; try discriminate E'. injection E' as E'. subst.
                simpl in H0'. destruct (g a) as [|] eqn:E'''; try discriminate H0'.
                clear H0'. simpl. rewrite E'''. simpl. constructor.
                -- f_equal. assumption.
                -- intros v [H|H].
                   ++ subst. simpl. assumption.
                   ++ apply IH2. assumption.
              + destruct (_ l1') as [v|] eqn:E''; try discriminate E.
                injection E as E. subst. destruct l2 as [| a' l2']; try discriminate H1.
                injection H1 as H1. assert (Htemp: Some l3 = Some l3) by reflexivity.
                simpl in H2. remember (IHl1' l3 Htemp l2' H1) as IHl1'' eqn:clearMe.
                clear IHl1' clearMe. assert (IHhyp: forall v, List.In v (List.combine l1' l2') ->
                                                              ZRange.type.base.option.is_bounded_by (fst v) (snd v) = true).
                { intros v H. apply H2. right. apply H. }
                apply IHl1'' in IHhyp. clear IHl1''. destruct IHhyp as [IH1 IH2].
                assert (H2': ZRange.type.base.option.is_bounded_by a a' = true).
                { apply (H2 (pair a a')). simpl. left. reflexivity. }
                clear H2. remember (H0 _ _ H2') as H0' eqn:clearMe. clear H0 clearMe.
                destruct (f a) as [r|]; try discriminate E'. injection E' as E'. subst.
                simpl in H0'. destruct (g a') as [|] eqn:E'''; try discriminate H0'.
                clear H0'. simpl. rewrite E'''. constructor.
                -- f_equal. assumption.
                -- intros v H. apply IH2. assumption.
          Qed.

          Local Ltac handle_lt_le_t_step_fast :=
            first [ match goal with
                    | [ H : (?a <= ?b)%Z, H' : (?b <= ?a)%Z |- _ ]
                      => pose proof (@Z.le_antisymm _ _ H H'); clear H H'
                    | [ H : (?a <= ?b <= ?a)%Z |- _ ]
                      => pose proof (@Z.le_antisymm _ _ (proj1 H) (proj2 H)); clear H
                    end ].

          Local Ltac handle_lt_le_t_step :=
            first [ handle_lt_le_t_step_fast
                  | match goal with
                    | [ |- context[Z.leb ?a ?b = true] ] => rewrite !Z.leb_le
                    | [ |- context[Z.ltb ?a ?b = true] ] => rewrite !Z.ltb_lt
                    | [ |- context[Nat.eqb ?a ?b = true] ] => rewrite !Nat.eqb_eq
                    | [ |- context[Z.eqb ?a ?b = true] ] => rewrite !Z.eqb_eq
                    | [ H : context[andb ?a ?b = true] |- _ ] => rewrite !Bool.andb_true_iff in H
                    | [ H : context[Z.leb ?a ?b = true] |- _ ] => rewrite !Z.leb_le in H
                    | [ H : context[Z.ltb ?a ?b = true] |- _ ] => rewrite !Z.ltb_lt in H
                    | [ H : context[Nat.eqb ?a ?b = true] |- _ ] => rewrite !Nat.eqb_eq in H
                    | [ H : context[Z.eqb ?a ?b = true] |- _ ] => rewrite !Z.eqb_eq in H
                    end ].

          Local Ltac handle_mod_bounds_t_step_fast :=
            first [ match goal with
                    | [ |- (0 <= _ mod _)%Z ] => apply Z.mod_pos_bound
                    | [ |- (_ mod ?m < ?m)%Z ] => apply Z.mod_pos_bound
                    | [ |- (?x mod ?m <= ?m - 1)%Z ] => cut (x mod m < m)%Z; [ clear; lia | ]
                    end ].

          Local Ltac simplify_ranges_t_step_fast :=
            first [ match goal with
                    | [ H : ZRange.lower ?r = ZRange.upper ?r |- _ ]
                      => is_var r; let x := fresh in destruct r as [r x]; cbn in H; subst x
                    | [ H : context[ZRange.type.base.is_bounded_by r[_ ~> _]%zrange _] |- _ ]
                      => progress cbn [ZRange.type.base.is_bounded_by] in H
                    | [ H : context[is_bounded_by_bool _ r[_ ~> _]%zrange] |- _ ]
                      => progress cbv [is_bounded_by_bool] in H
                    end ].
          Local Ltac simplify_ranges_t_step :=
            first [ simplify_ranges_t_step_fast ].

          Local Ltac non_arith_t :=
            repeat first [ assumption
                         | match goal with
                           | [ |- ?R ?x ?x ] => reflexivity
                           | [ H : forall x : unit, _ |- _ ] => specialize (H tt)
                           | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                           | [ H : ?x = ?x |- _ ] => clear H
                           | [ H : false = true |- _ ] => exfalso; clear -H; discriminate
                           | [ H : ~?R ?x ?x |- _ ] => exfalso; apply H; reflexivity
                           | [ |- ZRange.type.base.option.is_bounded_by ZRange.type.base.option.None _ = true ]
                             => apply type.base.option.is_bounded_by_None
                           | [ H : fold_andb_map _ ?l1 ?l2 = true |- length ?l1 = length ?l2 ]
                             => eapply fold_andb_map_length, H
                           | [ H : forall x y, Nat.eqb x y = true -> _ |- _ ] => specialize (fun x => H x x (@Nat.eqb_refl x))
                           | [ H : forall x, true = true -> _ |- _ ] => specialize (fun x => H x eq_refl)
                           | [ H : forall v, List.In v (List.combine ?ls1 ?ls2) -> ?R (fst v) (snd v) = true,
                                 H1 : List.nth_error ?ls1 ?n = Some ?v1,
                                 H2 : List.nth_error ?ls2 ?n = Some ?v2
                                 |- ?R ?v1 ?v2 = true ]
                             => apply (H (v1, v2)), (@nth_error_In _ _ n); clear -H1 H2
                           | [ H : ?T, H' : ~?T |- _ ] => exfalso; solve [ apply H', H ]
                           | [ H : List.nth_error ?ls ?n = Some _, H' : List.nth_error ?ls' ?n = None |- _ ]
                             => let Hlen := fresh in
                                assert (Hlen : length ls = length ls') by congruence;
                                exfalso; clear -H H' Hlen;
                                apply nth_error_value_length in H;
                                apply nth_error_error_length in H';
                                lia
                           | [ |- (0 <= 1)%Z ] => clear; lia
                           | [ H : ?beq ?x ?y = true |- ?x = ?y ]
                             => progress reflect_beq_to_eq beq
                           | [ |- ?beq ?x ?x = true ]
                             => progress reflect_beq_to_eq beq
                           end
                         | handle_lt_le_t_step_fast
                         | simplify_ranges_t_step_fast
                         | handle_mod_bounds_t_step_fast
                         | progress intros
                         | progress subst
                         | progress inversion_option
                         | progress inversion_prod
                         | progress destruct_head'_and
                         | progress destruct_head'_unit
                         | progress destruct_head'_prod
                         | progress destruct_head'_ex
                         | break_innermost_match_step
                         | break_innermost_match_hyps_step
                         | progress cbn [id
                                           ZRange.type.base.option.is_bounded_by is_bounded_by_bool ZRange.type.base.is_bounded_by lower upper fst snd projT1 projT2 bool_eq base.interp base.base_interp Crypto.Util.Option.bind fold_andb_map negb ZRange.ident.option.to_literal ZRange.type.base.option.None fst snd ZRange.type.base.option.interp ZRange.type.base.interp List.combine List.In base.interp_beq base.base_interp_beq base.base_interp ZRange.type.option.None] in *
                         | progress ident.fancy.cbv_fancy_in_all
                         | progress destruct_head'_bool
                         | solve [ auto with nocore ]
                         | progress fold (@base.interp) in *
                         | progress fold (@ZRange.type.base.option.interp) in *
                         | let v := (eval cbv [base.interp ZRange.type.base.option.interp ZRange.type.base.interp] in (@ZRange.type.base.option.interp)) in
                           progress change v with (@ZRange.type.base.option.interp) in *
                         | handle_lt_le_t_step
                         | simplify_ranges_t_step
                         | match goal with
                           | [ |- context[andb ?a ?b = true] ] => rewrite !Bool.andb_true_iff
                           | [ H : context[andb ?a ?b = true] |- _ ] => rewrite !Bool.andb_true_iff
                           | [ H : fold_andb_map _ _ _ = true |- _ ] => rewrite fold_andb_map_iff in H
                           | [ |- fold_andb_map _ _ _ = true ] => rewrite fold_andb_map_iff
                           | [ H : forall (x : option _), _ |- _ ] => pose proof (H None); specialize (fun x => H (Some x))
                           | [ H : forall x y z (w : option _), _ |- _ ] => pose proof (fun x y z => H x y z None); specialize (fun x y z w => H x y z (Some w))
                           | [ H : forall v, _ = v \/ _ -> _ |- _ ] => pose proof (H _ (or_introl eq_refl)); specialize (fun v pf => H v (or_intror pf))
                           | [ |- context[length ?x] ] => tryif is_var x then fail else (progress autorewrite with distr_length)
                           | [ H : List.In _ (List.combine _ _) |- _ ] => apply List.In_nth_error in H
                           | [ H : context[List.nth_error (List.combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                           | [ |- context[List.nth_error (List.combine _ _) _] ] => rewrite nth_error_combine
                           | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map_ex in H
                           | [ H : context[List.nth_error (List.seq _ _) _] |- _ ] => rewrite nth_error_seq in H
                           | [ |- context[List.nth_error (List.seq _ _) _] ] => rewrite nth_error_seq
                           | [ H : context[List.nth_error (List.firstn _ _) _] |- _ ] => rewrite nth_error_firstn in H
                           | [ |- context[List.nth_error (List.firstn _ _) _] ] => rewrite nth_error_firstn
                           | [ H : context[List.nth_error (List.skipn _ _) _] |- _ ] => rewrite nth_error_skipn in H
                           | [ |- context[List.nth_error (List.skipn _ _) _] ] => rewrite nth_error_skipn
                           | [ H : context[List.nth_error (update_nth _ _ _) _] |- _ ] => rewrite nth_update_nth in H
                           | [ |- context[List.nth_error (update_nth _ _ _) _] ] => rewrite nth_update_nth
                           | [ H : context[List.nth_error (List.app _ _) _] |- _ ] => rewrite nth_error_app in H
                           | [ |- context[List.nth_error (List.app _ _) _] ] => rewrite nth_error_app
                           | [ H : context[List.nth_error (List.rev _) _] |- _ ] => rewrite nth_error_rev in H
                           | [ |- context[List.nth_error (List.rev _) _] ] => rewrite nth_error_rev
                           | [ H : List.nth_error (Lists.List.repeat _ _) _ = Some _ |- _ ] => apply nth_error_repeat in H
                           | [ H : List.nth_error (List.repeat _ _) _ = Some _ |- _ ] => apply nth_error_repeat in H
                           | [ H : length ?l1 = length ?l2 |- context[length ?l1] ] => rewrite H
                           | [ H : length ?l1 = length ?l2, H' : context[length ?l1] |- _ ] => rewrite H in H'
                           | [ |- context[List.flat_map _ _] ] => rewrite List.flat_map_concat_map, concat_fold_right_app
                           | [ H : S _ = S _ |- _ ] => inversion H; clear H
                           | [ H : List.fold_right (fun x y => x' <- x; y' <- y; Some _)%option (Some ?init) ?ls = Some ?v |- _]
                             => rewrite OptionList.fold_right_option_seq in H
                           | [ |- and _ _ ] => apply conj
                           end
                         | progress cbv [bool_eq Bool.eqb option_map List.nth_default Definitions.Z.bneg is_bounded_by_bool zrange_beq] in *
                         | let rec do_rect_head lhs rhs k :=
                             lazymatch lhs with
                             | nat_rect ?P ?O ?S ?n
                               => lazymatch rhs with
                                  | nat_rect ?P' ?O' ?S' n
                                    => is_var n;
                                       k ();
                                       induction n; cbn [nat_rect];
                                       generalize dependent (nat_rect P O S); generalize dependent (nat_rect P' O' S');
                                       intros
                                  end
                             | list_rect ?P ?N ?C ?ls
                               => lazymatch rhs with
                                  | list_rect ?P' ?N' ?C' ?ls'
                                    => lazymatch goal with
                                       | [ H : length ls = length ls' |- _ ]
                                         => is_var ls; is_var ls'; k ();
                                            let IH := fresh "IH" in
                                            (revert dependent ls'; induction ls as [|? ls IH]; intros [|? ls']; intros; cbn [list_rect length] in * );
                                            [
                                            | exfalso; discriminate | exfalso; discriminate
                                            | specialize (IH ls');
                                              generalize dependent (list_rect P N C); generalize dependent (list_rect P' N' C') ];
                                            intros
                                       end
                                  end
                             | ?f ?x
                               => lazymatch rhs with
                                  | ?g ?y
                                    => is_var x; is_var y;
                                       do_rect_head f g ltac:(fun _ => k (); revert dependent x; try revert dependent y)
                                  end
                             end in
                           lazymatch goal with
                           | [ |- ?R ?lhs ?rhs = true ] => do_rect_head lhs rhs ltac:(fun _ => idtac)
                           end
                         | match goal with
                           | [ H : length ?ls = length ?ls' |- ?R (List.fold_right ?f ?x ?ls) (List.fold_right ?f' ?x' ?ls') = true ]
                             => is_var ls; is_var ls';
                                let IH := fresh "IH" in
                                revert dependent ls'; induction ls as [|? ls IH]; intros [|? ls']; cbn [List.fold_right length] in *;
                                [
                                 | exfalso; clear -H; discriminate | exfalso; clear -H; discriminate
                                 | specialize (IH ls');
                                   generalize dependent (List.fold_right f x); generalize dependent (List.fold_right f' x') ];
                                intros
                           | [ H : length ?ls = length ?ls' |- ?R (List.fold_right ?f ?x ?ls) (List.fold_right ?f' ?x' ?ls') = true ]
                             => is_var ls; is_var ls';
                                let IH := fresh "IH" in
                                revert dependent ls'; induction ls as [|? ls IH]; intros [|? ls']; intros; cbn [List.fold_right length] in *;
                                [
                                 | exfalso; discriminate | exfalso; discriminate
                                 | specialize (IH ls');
                                   generalize dependent (List.fold_right f x); generalize dependent (List.fold_right f' x') ];
                                intros
                           | [ H : forall a b, ?R a b = true -> ?R' (?f a) (?g b) = true |- ?R' (?f _) (?g _) = true ] => apply H; clear H
                           | [ H : forall a b, ?R a b = true -> forall c d, ?R' c d = true -> ?R'' (?f a c) (?g b d) = true |- ?R'' (?f _ _) (?g _ _) = true ]
                             => apply H; clear H
                           | [ H : forall a b, ?R a b = true -> forall c d, ?R' c d = true -> forall e f, ?R'' e f = true -> ?R''' (?F _ _ _) (?G _ _ _) = true |- ?R''' (?F _ _ _) (?G _ _ _) = true ]
                             => apply H; clear H
                           | [ H : context[ZRange.type.base.option.is_bounded_by (?f (Some _) (Some _)) (?g _ _) = true]
                               |- ZRange.type.base.option.is_bounded_by (?f (Some _) (Some _)) (?g _ _) = true ]
                             => apply H
                           | [ H : (forall a b, ?R0 a b = true -> forall c d, ?R1 c d = true -> forall e f, (forall g h, ?R3 g h = true -> ?R4 (e g) (f h) = true) -> forall i j, ?R5 i j = true -> ?R6 (?F _ _ _ _) (?G _ _ _ _) = true)
                               |- ?R6 (?F _ _ _ _) (?G _ _ _ _) = true ]
                             => apply H; clear H
                           end
                         | match goal with
                           | [ |- ZRange.type.base.option.is_bounded_by (ZRange.type.base.option.union _ _) (Bool.Thunked.bool_rect _ _ _ true) = true ]
                             => apply ZRange.type.base.option.is_bounded_by_union_l
                           | [ |- ZRange.type.base.option.is_bounded_by (ZRange.type.base.option.union _ _) (Bool.Thunked.bool_rect _ _ _ false) = true ]
                             => apply ZRange.type.base.option.is_bounded_by_union_r
                           | [ |- ZRange.type.base.option.is_bounded_by (ZRange.type.base.option.union _ _) (Bool.bool_rect_nodep _ _ true) = true ]
                             => apply ZRange.type.base.option.is_bounded_by_union_l
                           | [ |- ZRange.type.base.option.is_bounded_by (ZRange.type.base.option.union _ _) (Bool.bool_rect_nodep _ _ false) = true ]
                             => apply ZRange.type.base.option.is_bounded_by_union_r
                           end
                         | do_with_hyp' ltac:(fun H => apply H; clear H; now non_arith_t) ].

          Local Lemma mul_by_halves_bounds x y n :
            (0 <= x < 2^ (n / 2))%Z ->
            (0 <= y < 2^ (n / 2))%Z ->
            (0 <= x * y <= 2 ^ n - 1)%Z.
          Proof using Type.
            intros. rewrite Z.le_sub_1_iff.
            assert (2 ^ (n / 2) * 2 ^ (n / 2) <= 2 ^ n)%Z.
            { rewrite <-Z.pow_twice_r.
              apply Z.pow_le_mono_r; auto with zarith; [ ].
              Z.div_mod_to_quot_rem. nia. }
            Z.div_mod_to_quot_rem; nia.
          Qed.

          Local Ltac mul_by_halves_t :=
            apply mul_by_halves_bounds;
            match goal with
            | |- context [Z.land _ (2 ^ ?n - 1)%Z] =>
              rewrite (Z.sub_1_r (2 ^ n)), <-Z.ones_equiv, !Z.land_ones by auto with zarith
            | |- context [Z.shiftr ?a ?n] =>
            apply LandLorShiftBounds.Z.shiftr_range; auto with zarith; rewrite Z.add_diag, <-Z_div_exact_full_2 by auto with zarith
            end; auto using Z.mod_pos_bound with zarith.

          Local Lemma invert_to_literal {t} e v
            : ZRange.ident.option.to_literal (t:=t) e = Some v
              <-> e = ZRange.ident.option.of_literal v.
          Proof using Type.
            induction t; split_iff; split; cbn; cbv [Crypto.Util.Option.bind option_map Option.lift]; break_innermost_match;
              repeat first [ progress Z.ltb_to_lt
                           | reflexivity
                           | congruence
                           | apply (f_equal2 (@pair _ _))
                           | progress cbn [ZRange.lower ZRange.upper] in *
                           | progress cbv [Crypto.Util.Option.bind] in *; break_match_hyps
                           | progress subst
                           | progress intros
                           | progress inversion_option
                           | progress inversion_prod
                           | progress inversion_zrange
                           | progress destruct_head_hnf' zrange
                           | progress destruct_head_hnf' unit
                           | solve [ eauto ]
                           | match goal with
                             | [ H : Crypto.Util.OptionList.Option.List.lift (List.map ZRange.ident.option.to_literal ?l) = Some ?v |- _ ]
                               => cbv [Crypto.Util.OptionList.Option.List.lift] in H; revert v H; induction l; intro v; destruct v; cbn [List.fold_right List.map]; intro
                             | [ |- Crypto.Util.OptionList.Option.List.lift (List.map ZRange.ident.option.to_literal (List.map ZRange.ident.option.of_literal ?v)) = Some ?v ]
                               => cbv [Crypto.Util.OptionList.Option.List.lift]; induction v; cbn [List.fold_right List.map]
                             | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
                             | [ H : forall x, Some x = Some _ -> _ |- _ ] => specialize (H _ eq_refl)
                             | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                             | [ H : forall e v, ?f e = Some v -> e = ?g v, H' : ?f ?e' = Some ?v' |- _ ]
                               => is_var v'; specialize (H e' v' H')
                             | [ H : forall e v, e = ?f v -> ?g e = Some v, H' : ?g ?e' = _ |- _ ]
                               => erewrite H in H' by reflexivity
                             end
                           | progress break_match
                           | apply (f_equal2 (@cons _))
                           | apply (f_equal (@Some _)) ].
          Qed.

          Local Lemma is_bounded_by_of_literal {t} x y
            : ZRange.type.base.option.is_bounded_by (t:=t) (ZRange.ident.option.of_literal x) y = true <-> x = y.
          Proof using Type.
            induction t; split_iff; split; cbn [ZRange.ident.option.of_literal ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by]; break_innermost_match.
            all: repeat first [ progress intros
                              | progress subst
                              | progress destruct_head'_and
                              | progress cbv [option_beq_hetero option_map] in *
                         | match goal with
                           | [ H : forall x y, x = y -> _ |- _ ] => specialize (fun x => H x x eq_refl)
                           | [ H : andb _ _ = true |- _ ] => rewrite Bool.andb_true_iff in H
                           | [ |- andb _ _ = true ] => rewrite Bool.andb_true_iff
                           | [ |- and _ _ ] => split
                           | [ H : is_bounded_by_bool _ r[?x ~> ?x] = true |- _ ]
                             => apply ZRange.is_bounded_by_bool_constant_iff in H
                           | [ H : ?beq ?x ?y = true |- ?x = ?y ]
                             => progress reflect_beq_to_eq beq
                           | [ |- ?beq ?x ?x = true ]
                             => progress reflect_beq_to_eq beq
                           end
                         | solve [ eauto with nocore ]
                         | reflexivity
                         | apply ZRange.is_bounded_by_bool_constant
                         | progress inversion_prod
                         | progress destruct_head_hnf' unit
                         | progress break_innermost_match_hyps
                         | progress break_innermost_match
                         | congruence
                         | apply (f_equal2 (@pair _ _))
                         | apply (f_equal2 (@cons _))
                         | apply (f_equal (@Some _))
                         | match goal with
                           | [ H : fold_andb_map ZRange.type.base.option.is_bounded_by (List.map ZRange.ident.option.of_literal ?x) ?y = true |- ?x = ?y ]
                             => is_var x; is_var y; revert dependent y; induction x; intro y; destruct y; cbn [fold_andb_map List.map] in *; generalize dependent (@fold_andb_map); intros
                           | [ |- fold_andb_map ZRange.type.base.option.is_bounded_by (List.map ZRange.ident.option.of_literal ?x) ?x = true ]
                             => is_var x; induction x; cbn [fold_andb_map List.map] in *; generalize dependent (@fold_andb_map); intros
                           end ].
          Qed.

          Local Ltac require_pairs_of_literals term :=
            lazymatch term with
            | ZRange.ident.option.of_literal _ => idtac
            | (?x, ?y) => require_pairs_of_literals x; require_pairs_of_literals y
            end.
          Local Ltac handle_to_literal :=
            repeat match goal with
                   | [ |- context[ZRange.ident.option.to_literal (t:=?T) ?x] ]
                     => is_var x;
                        let H := fresh in
                        destruct (ZRange.ident.option.to_literal (t:=T) x) eqn:H;
                        [ rewrite invert_to_literal in H; subst x | ]
                   | [ H : ZRange.type.base.option.is_bounded_by (t:=?T1*?T2) (?r1, ?r2) (?x1, ?x2) = true |- _ ]
                     => require_pairs_of_literals r1;
                        change (ZRange.type.base.option.is_bounded_by (t:=T1) r1 x1 && ZRange.type.base.option.is_bounded_by (t:=T2) r2 x2 = true)%bool in H;
                        rewrite Bool.andb_true_iff in H; destruct H
                   | [ H : ZRange.type.base.option.is_bounded_by (ZRange.ident.option.of_literal ?x) ?y = true |- _ ]
                     => rewrite is_bounded_by_of_literal in H; (subst x || subst y)
                   end.

          Local Lemma interp_related_fancy_rshi :
            interp_is_related ident.fancy_rshi.
          Proof using Type.
            cbn [type.related_hetero ZRange.ident.option.interp ident.interp respectful_hetero type.interp ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp ZRange.type.base.option.Some ZRange.ident.option.of_literal].
            cbv [respectful_hetero option_map list_case].
            intros.
            destruct_head_hnf' prod.
            handle_to_literal;
              break_innermost_match;
              auto using type.base.option.is_bounded_by_None;
              ident.fancy.cbv_fancy_in_all; cbn [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by Crypto.Util.Option.bind ZRange.ident.option.to_literal fst snd] in *;
              repeat match goal with
                     | H : _ |- _ =>
                     rewrite Bool.andb_true_iff in H;
                       destruct H
                     | _ => progress destruct_head_hnf' option; try congruence; [ ]
                     | _ => progress cbv [is_bounded_by_bool is_tighter_than_bool] in *; cbn in *
                     | _ => progress cbn in *
                     end.

             { Z.ltb_to_lt. rewrite !Z.rshi_small by lia.
               apply Bool.andb_true_iff; split; apply Z.leb_le;
                 Z.div_mod_to_quot_rem; nia. }
             { Z.ltb_to_lt.
               rewrite Z.rshi_correct_full by lia.
               break_innermost_match; apply Bool.andb_true_iff; split; apply Z.leb_le; try apply Z.le_sub_1_iff; auto with zarith. }
          Qed.

          (** In abstract interpretation, we only need this version of the lemma for less-than-third-order types, but in Assembly/Symbolic, we use it for all identifiers *)
          Lemma interp_related {t} (idc : ident t) (*H : type.is_not_higher_order_than 3 t = true*) : interp_is_related idc.
          Proof using Type.
            destruct idc.
            (*
            (** clear out higher-than-third-order types *)
            all: cbn in H; try congruence.*)
            all: lazymatch goal with
                 | [ |- context[ident.Z_cast] ] => apply interp_related_Z_cast
                 | [ |- context[ident.Z_cast2] ] => apply interp_related_Z_cast2
                 | [ |- context[ident.List_flat_map] ] => apply interp_related_List_flat_map
                 | [ |- context[ident.List_partition] ] => apply interp_related_List_partition
                 | [ |- context[ident.List_filter] ] => apply interp_related_List_filter
                 | [ |- context[ident.fancy_rshi] ] => apply interp_related_fancy_rshi
                 | _ => idtac
                 end.
            all: cbn [type.related_hetero ZRange.ident.option.interp ident.interp respectful_hetero type.interp ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp ZRange.type.base.option.Some ZRange.ident.option.of_literal].
            all: cbv [ident.cast2 ident.literal prod_rect_nodep prod_rect ident.eagerly] in *.
            all: change (@zrange_rect_nodep) with (fun T => @zrange_rect (fun _ => T)) in *.
            all: change (@Thunked.nat_rect) with (fun P P0 => @nat_rect (fun _ => P) (P0 Datatypes.tt)) in *.
            all: change (@nat_rect_arrow_nodep) with (fun P Q => @nat_rect (fun _ => P -> Q)).
            all: change (@Thunked.list_rect) with (fun A P PNil => @list_rect A (fun _ => P) (PNil Datatypes.tt)) in *.
            all: change (@list_rect_arrow_nodep) with (fun A P Q => @list_rect A (fun _ => P -> Q)).
            all: change (@Thunked.list_case) with (fun A P PNil => @list_case A (fun _ => P) (PNil Datatypes.tt)) in *.
            all: change (@Thunked.option_rect) with (fun A P PS PN => @option_rect A (fun _ => P) PS (PN Datatypes.tt)) in *.
            all: cbv [
                     nat_rect_fbb_b
                       nat_rect_fbb_b_b
                       list_rect_fbb_b
                       list_rect_fbb_b_b
                       list_rect_fbb_b_b_b
                       list_rect_fbb_b_b_b_b
                       list_rect_fbb_b_b_b_b_b
                   ] in *.
            all: cbv [respectful_hetero option_map option_rect zrange_rect list_case].
            all: intros.
            all: destruct_head_hnf' prod.
            all: destruct_head_hnf' option.
            Time all: try solve [ non_arith_t ].
            all: ident.fancy.cbv_fancy_in_all; cbn [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by Crypto.Util.Option.bind ZRange.ident.option.to_literal fst snd] in *.
            all: break_innermost_match; try reflexivity.
            Time all: try solve [ non_arith_t ].
            all: repeat first [ progress subst
                              | progress inversion_prod
                              | progress inversion_option
                              | progress destruct_head'_and
                              | progress cbn [ZRange.type.base.option.is_tighter_than lower upper fst snd Crypto.Util.Option.bind ZRange.type.base.is_tighter_than] in *
                              | progress cbv [Definitions.Z.lnot_modulo Definitions.Z.add_with_carry] in *
                              | handle_lt_le_t_step
                              | simplify_ranges_t_step
                              | discriminate
                              | solve [ auto using ZRange.is_bounded_by_bool_Proper_if_sumbool_union, Z.mod_pos_bound, Z.mod_neg_bound with zarith ]
                              | rewrite ZRange.is_bounded_by_bool_opp
                              | progress autorewrite with zsimplify_const
                              | rewrite Z.le_sub_1_iff
                              | rewrite Z.le_add_1_iff
                              | match goal with
                                | [ H : ?x = ?x |- _ ] => clear H
                                | [ |- andb (is_bounded_by_bool (_ mod ?m) (fst (Operations.ZRange.split_bounds _ ?m)))
                                           (is_bounded_by_bool (_ / ?m) (snd (Operations.ZRange.split_bounds _ ?m))) = true ]
                                  => apply ZRange.is_bounded_by_bool_split_bounds
                                | [ |- is_bounded_by_bool (_ / ?m) (snd (Operations.ZRange.split_bounds _ ?m)) = true ]
                                  => apply ZRange.is_bounded_by_bool_split_bounds_and
                                | [ |- is_bounded_by_bool (_ mod _) r[_ ~> _] = true ] => cbv [is_bounded_by_bool]; rewrite Bool.andb_true_iff
                                | [ H : is_bounded_by_bool ?v ?r1 = true, H' : is_tighter_than_bool ?r1 ?r2 = true |- _ ]
                                  => pose proof (@ZRange.is_bounded_by_of_is_tighter_than r1 r2 H' v H);
                                     clear H H' r1
                                | [ |- context [match (if _ then _ else _) with _ => _ end ] ]
                                  => break_innermost_match
                                | [ |- context[ZRange.constant ?x] ] => unique pose proof (ZRange.is_bounded_by_bool_constant x)
                                | [ |- context[r[?x~>?x]%zrange] ] => unique pose proof (ZRange.is_bounded_by_bool_constant x)
                                | [ |- is_bounded_by_bool (Definitions.Z.ltz _ _) r[0 ~> 1] = true ]
                                  => cbv [Definitions.Z.ltz]; break_innermost_match; cbv
                                end
                              | progress Z.ltb_to_lt
                              | progress rewrite ?Z.mul_split_div, ?Z.mul_split_mod, ?Z.mul_high_div, ?Z.add_get_carry_full_div, ?Z.add_get_carry_full_mod, ?Z.add_with_get_carry_full_div, ?Z.add_with_get_carry_full_mod, ?Z.sub_get_borrow_full_div, ?Z.sub_get_borrow_full_mod, ?Z.sub_with_get_borrow_full_div, ?Z.sub_with_get_borrow_full_mod, ?Z.zselect_correct, ?Z.add_modulo_correct, ?Z.rshi_correct_full, ?Z.truncating_shiftl_correct_land_ones ].
            all: repeat lazymatch goal with
                        | [ |- is_bounded_by_bool (Z.land _ _) (ZRange.land_bounds _ _) = true ]
                          => apply ZRange.is_bounded_by_bool_land_bounds; auto
                        | [ |- is_bounded_by_bool (Z.lor _ _) (ZRange.lor_bounds _ _) = true ]
                          => apply ZRange.is_bounded_by_bool_lor_bounds; auto
                        | [ |- is_bounded_by_bool (if _ then (_ + _ - _)%Z else (_ + _)%Z) (ZRange.union (ZRange.four_corners Z.add _ _) (ZRange.eight_corners _ _ _ _)) = true ]
                          => rewrite ZRange.union_comm; apply ZRange.is_bounded_by_bool_Proper_if_bool_union_dep; intros; Z.ltb_to_lt
                        | [ |- is_bounded_by_bool (?a + ?b - ?c) (ZRange.eight_corners (fun x y z => Z.max 0 (x + y - z)) _ _ _) = true ]
                          => replace (a + b - c)%Z with (Z.max 0 (a + b - c)) by lia
                        | [ Hx : is_bounded_by_bool _ ?x = true, Hy : is_bounded_by_bool _ ?y = true, Hz : is_bounded_by_bool _ ?z = true
                            |- is_bounded_by_bool _ (ZRange.eight_corners ?f ?x ?y ?z) = true ]
                          => apply (fun pf1 pf2 pf3 => @ZRange.monotoneb_eight_corners_gen f pf1 pf2 pf3 _ _ _ _ _ _ Hx Hy Hz); intros; auto with zarith
                        | [ Hx : is_bounded_by_bool _ ?x = true, Hy : is_bounded_by_bool _ ?y = true
                            |- is_bounded_by_bool _ (ZRange.four_corners_and_zero ?f ?x ?y) = true ]
                          => apply (fun pf1 pf2 pf3 pf4 => @ZRange.monotoneb_four_corners_and_zero_gen f pf1 pf2 pf3 pf4 _ _ _ _ Hx Hy); intros; auto with zarith
                        | [ Hx : is_bounded_by_bool _ ?x = true, Hy : is_bounded_by_bool _ ?y = true
                            |- is_bounded_by_bool _ (ZRange.four_corners ?f ?x ?y) = true ]
                          => apply (fun pf1 pf2 => @ZRange.monotoneb_four_corners_gen f pf1 pf2 _ _ _ _ Hx Hy); intros; auto with zarith
                        | [ Hx : is_bounded_by_bool _ ?x = true
                            |- is_bounded_by_bool _ (ZRange.two_corners ?f ?x) = true ]
                          => apply (fun pf => @ZRange.monotoneb_two_corners_gen f pf x _ Hx); intros; auto with zarith
                        | [ Hx : is_bounded_by_bool _ ?x = true
                            |- is_bounded_by_bool _ (ZRange.two_corners_and_zero ?f ?x) = true ]
                          => apply (fun pf1 pf2 => @ZRange.monotoneb_two_corners_and_zero_gen f pf1 pf2 x _ Hx); intros; auto with zarith
                        | [ |- is_bounded_by_bool (if _ then _ else _) (ZRange.four_corners _ _ _) = true ]
                          => apply ZRange.is_bounded_by_bool_Proper_if_bool_union_dep; intros; Z.ltb_to_lt
                        | [ _ : is_bounded_by_bool ?x1 ?r1 = true,
                                _ : is_bounded_by_bool ?x2 ?r2 = true,
                                    H : (?fr ?r1 ?r2 =? r[0 ~> 1])%zrange = true |- is_bounded_by_bool (?f ?x1 ?x2) r[0~>2] = true ]
                          => cut (is_bounded_by_bool (f x1 x2) (fr r1 r2) = true);
                               [ apply ZRange.is_bounded_by_of_is_tighter_than; apply zrange_bl in H; rewrite H; clear
                               | clear H ]
                        | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
                        | [ |- context[Proper _ (Z.mul ?v)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (Z.div ?v)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.mul _ ?v)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.mul ?v _)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.div _ ?v)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.div ?v _)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.shiftr _ ?v)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.shiftr ?v _)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.shiftl _ ?v)] ] => is_var v; destruct v; auto with zarith
                        | [ |- context[Proper _ (fun y => Z.shiftl ?v _)] ] => is_var v; destruct v; auto with zarith
                        | _ => idtac
                        end.
            all: try solve [ cbv [Proper respectful Basics.flip]; constructor; intros; lia ].
            all: try solve [ cbv [Proper respectful Basics.flip]; constructor; intros; autorewrite with zsimplify_const; lia ].
            all: cbv [is_bounded_by_bool ZRange.upper ZRange.lower]; rewrite ?Bool.andb_true_iff, ?Z.leb_le.
            all: try solve [ lia
                           | match goal with
                             | [ |- ((0 <= _ mod _ <= _) /\ (0 <= _ <= _))%Z ]
                               => Z.div_mod_to_quot_rem; nia
                             end
                           | intros; mul_by_halves_t ].
            all: try solve [ non_arith_t; Z.ltb_to_lt; reflexivity ].
            all: try solve [ non_arith_t; try match goal with |- ?x = true => destruct x eqn:? end; reflect_hyps; subst; nia ].
            all: try solve [ cbv [ZRange.ToConstant.four_corners ZRange.ToConstant.Option.four_corners ZRange.ToConstant.Option.apply_to_range ZRange.ToConstant.Option.two_corners ZRange.ToConstant.Option.union option_beq Bool.eqb] in *; non_arith_t; Z.ltb_to_lt; lia ].
            (** For command-line debugging, we display goals that should not remain *)
            all: [ > idtac "WARNING: Remaining goal:"; print_context_and_goal () .. ].
          Qed.

          Variant rect_arg_kind := fin (_ : API.type) | recr.
          Definition ctor_descr := list rect_arg_kind.
          Definition rect_spec := list ctor_descr.
          Definition interp_rect_arg_kind (recrT : API.type) (r : rect_arg_kind) : API.type
            := match r with
               | fin t => t
               | recr => recrT
               end.
          Fixpoint interp_ctor_descr (containerT : API.type) (motive : API.type) (r : ctor_descr) : API.type
            := match r with
               | nil => motive
               | cons (fin t) rs => t -> interp_ctor_descr containerT motive rs
               | cons recr rs => containerT -> motive -> interp_ctor_descr containerT motive rs
               end%etype.
          Fixpoint interp_rect (containerT : API.type) (motive : API.type) (r : rect_spec) : API.type
            := match r with
               | nil => containerT -> motive
               | cons r rs => interp_ctor_descr containerT motive r -> interp_rect containerT motive rs
               end%etype.
          Variant rect_kind := rect_nat | rect_list (t : base.type).

          Definition rect_spec_of_kind (r : rect_kind) : rect_spec
            := match r with
               | rect_nat => [ [] ; [recr] ]
               | rect_list t => [ [] ; [fin (type.base t); recr] ]
               end.
          Definition rect_container_of_kind (r : rect_kind) : base.type
            := match r with
               | rect_nat => base.type.type_base base.type.nat
               | rect_list t => base.type.list t
               end.

          (* TODO: move? *)
          (** N.B. We don't say yes for thunked recursors, which are a bit different in shape *)
          Definition is_rect {t} (idc : ident t) : option { k : rect_kind & { m : _ | t = interp_rect (type.base (rect_container_of_kind k)) m (rect_spec_of_kind k) } }.
          Proof.
            refine match idc with
                   | ident.nat_rect_arrow _ _
                   | ident.eager_nat_rect_arrow _ _
                   | ident.nat_rect_fbb_b _ _ _
                   | ident.nat_rect_fbb_b_b _ _ _ _
                     => Some (existT _ rect_nat _)
                   | ident.list_rect_arrow _ _ _
                   | ident.eager_list_rect_arrow _ _ _
                   | ident.list_rect_fbb_b _ _ _ _
                   | ident.list_rect_fbb_b_b _ _ _ _ _
                   | ident.list_rect_fbb_b_b_b _ _ _ _ _ _
                   | ident.list_rect_fbb_b_b_b_b _ _ _ _ _ _ _
                   | ident.list_rect_fbb_b_b_b_b_b _ _ _ _ _ _ _ _
                     => Some (existT _ (rect_list _) _)
                   | _
                     => None
                   end.
            all: eexists; cbv; reflexivity.
          Defined.

          Lemma rect_interp_rect {t} {idc : ident t} {k} (H : is_rect idc = Some k)
            : match k with
              | existT rect_nat (exist p H)
                => forall z s, let f := (rew [API.interp_type] H in ident.interp idc) in f z s 0 = z /\ forall n, f z s (S n) = s n (f z s n)
              | existT (rect_list _) (exist p H)
                => forall n c, let f := (rew [API.interp_type] H in ident.interp idc) in f n c nil = n /\ forall x xs, f n c (cons x xs) = c x xs (f n c xs)
              end.
          Proof using Type.
            fold (@type.interp) in *.
            destruct idc; cbn in H; inversion_option; subst.
            all: cbn; repeat split.
          Qed.

          Lemma rect_ZRange_interp_rect {t} {idc : ident t} {k} (H : is_rect idc = Some k)
            : match k with
              | existT rect_nat (exist p H)
                => forall z s, let f := (rew [ZRange.type.option.interp] H in ZRange.ident.option.interp assume_cast_truncates idc) in f z s None = ZRange.type.option.None /\ f z s (Some 0) = z /\ forall n, f z s (Some (S n)) = s (Some n) (f z s (Some n))
              | existT (rect_list _) (exist p H)
                => forall n c, let f := (rew [ZRange.type.option.interp] H in ZRange.ident.option.interp assume_cast_truncates idc) in f n c None = ZRange.type.option.None /\ f n c (Some nil) = n /\ forall x xs, f n c (Some (cons x xs)) = c x (Some xs) (f n c (Some xs))
              end.
          Proof using Type.
            fold (@type.interp) in *.
            fold (@ZRange.type.base.option.interp) in *.
            destruct idc; cbn in H; inversion_option; subst.
            all: cbn; repeat split.
          Qed.

          Lemma interp_related_and_Proper {t} (idc : ident t) : interp_is_related_and_Proper idc.
          Proof using Type.
            destruct (type.is_not_higher_order_than 3 t) eqn:Hho;
              [ | destruct (is_rect idc) eqn:Hrect ].
            { apply type.related_hetero_impl_related_hetero_and_Proper_eqv_not_higher_order_than_3.
              all: try apply interp_related.
              all: try apply ident.interp_Proper.
              all: try apply ZRange.ident.option.interp_Proper.
              all: try assumption.
              all: try reflexivity. }
            { apply type.related_hetero_and_Proper_iff_app_curried.
              all: try now intros; hnf.
              repeat split.
              all: try now apply ident.interp_Proper.
              all: try now apply ZRange.ident.option.interp_Proper.
              all: [ > ].
              intros x y Hxy.

              (*pose proof (interp_related idc) as Hir.*)
              pose proof (ident.interp_Proper idc idc eq_refl) as Hip.
              pose proof (ZRange.ident.option.interp_Proper assume_cast_truncates idc idc eq_refl) as Hzip.
              pose proof Hrect as Hrect'.
              apply rect_interp_rect in Hrect.
              apply rect_ZRange_interp_rect in Hrect'.
              fold base.interp in *.
              fold (@type.interp) in *.
              fold (@ZRange.type.base.option.interp) in *.
              fold (@ZRange.type.option.interp) in *.
              clear Hho.
              let k := match goal with H : sigT _ |- _ => H end in
              destruct k as [k [p Ht] ].
              subst t.

              generalize dependent (ident.interp idc).
              generalize dependent (ZRange.ident.option.interp assume_cast_truncates idc).
              clear idc.
              destruct_head' rect_kind.
              all: cbn [eq_rect].
              all: cbn [interp_rect rect_spec_of_kind interp_ctor_descr rect_container_of_kind type.app_curried type.final_codomain ZRange.type.option.interp type.interp type.and_for_each_lhs_of_arrow type.for_each_lhs_of_arrow] in *.
              all: destruct_head'_prod; cbn [fst snd] in *.
              all: intros; split_and.
              all: repeat match goal with
                     | [ H : type.related_hetero_and_Proper _ _ _ _ _ |- _ ]
                       => apply type.related_hetero_and_Proper_iff_app_curried in H;
                          [ | clear H; repeat intro; hnf; reflexivity .. ]
                     end.
              all: destruct_head'_and.
              all: cbn [type.related] in *.
              all: cbv [Proper] in *.
              all: cbn in *.
              all: specialize_by first [ exact tt | exact I ].
              all: destruct_head' option; reflect_hyps; subst.
              all: eliminate_hprop_eq.
              all: match goal with
                   | [ |- ?R (type.app_curried (?f (Some ?n)) ?x) (type.app_curried (?g ?n) ?y) = true ]
                     => revert dependent y; revert dependent x;
                        induction n; intros
                   | [ |- ?R (type.app_curried (?f None) ?x) (type.app_curried (?g ?n) ?y) = true ]
                     => revert dependent y; revert dependent x;
                        induction n; intros
                   | [ |- ?R (type.app_curried (?f (Some ?n')) ?x) (type.app_curried (?g ?n) ?y) = true ]
                     => revert dependent y; revert dependent x;
                        revert dependent n'; induction n; intro n'; destruct n'; intros
                   end.
              all: repeat do_with_hyp' ltac:(fun H => rewrite !H; []).
              all: auto.
              all: repeat match goal with
                     | [ H : forall x y : _ * (_ * (_ * _)), _ |- _ ]
                       => specialize (fun x1 y1 x2 y2 x3 y3 x4 y4 => H (x1, (x2, (x3, x4))) (y1, (y2, (y3, y4))))
                     | [ H : forall x y : _ * _ * _, _ |- _ ]
                       => specialize (fun x1 y1 x2 y2 x3 y3 => H (x1, x2, x3) (y1, y2, y3))
                     | [ H : forall x y : _ * (_ * _), _ |- _ ]
                       => specialize (fun x1 y1 x2 y2 x3 y3 => H (x1, (x2, x3)) (y1, (y2, y3)))
                     end.
              all: cbn [fst snd] in *.
              all: try do_with_exactly_one_hyp ltac:(fun H => apply H).
              all: repeat split; intros; auto.
              all: rewrite ?ZRange.type.option.app_curried_None.
              all: try apply type.base.option.is_bounded_by_None.
              all: rewrite ?type.related_hetero_and_Proper_iff_app_curried by now intros; hnf.
              all: repeat split; intros; cbv [Proper] in *.
              all: auto.
              all: repeat match goal with
                   | [ |- ?x = true ] => destruct x eqn:?; reflect_hyps; congruence
                     end.
              all: repeat do_with_hyp' ltac:(fun H => rewrite !H; []).
              all: reflect_hyps; destruct_head'_False.
              all: cbn [fold_andb_map] in *; rewrite ?Bool.andb_true_iff in *; destruct_head'_and.
              all: auto.
              all: try now repeat do_with_hyp' ltac:(fun H => apply H); repeat intro; subst; auto. }
            { destruct idc.
              all: try (apply Bool.diff_true_false in Hho; exfalso; exact Hho).
              all: try solve [ cbn in Hrect; inversion_option ].
              (** For command-line debugging, we display goals that should not remain *)
              all: [ > idtac "WARNING: Remaining non-rect goal of order > 3:"; print_context_and_goal () .. ]. }
          Time Qed.
        End interp_related.
      End option.
    End ident.
  End ZRange.
End Compilers.
