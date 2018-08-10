Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationPairs.
Require Import Coq.Relations.Relations.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZRange.BasicLemmas.
Require Import Crypto.Util.Sum.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.SplitMinMax.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.AbstractInterpretation.
Require Import Crypto.Experiments.NewPipeline.AbstractInterpretationWf.

Module Compilers.
  Import Language.Compilers.
  Import UnderLets.Compilers.
  Import AbstractInterpretation.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import AbstractInterpretationWf.Compilers.
  Import AbstractInterpretationWf.Compilers.partial.
  Import invert_expr.

  Local Notation related_bounded' b v1 v2
    := (ZRange.type.base.option.is_bounded_by b v1 = true
        /\ ZRange.type.base.option.is_bounded_by b v2 = true
        /\ v1 = v2) (only parsing).
  Local Notation related_bounded
    := (@type.related_hetero3 _ _ _ _ (fun t b v1 v2 => related_bounded' b v1 v2)).

  Module ZRange.
    Module type.
      Module base.
        Module option.
          Lemma is_bounded_by_None t v : ZRange.type.base.option.is_bounded_by (@ZRange.type.base.option.None t) v = true.
          Proof. induction t; cbn; cbv [andb]; break_innermost_match; eauto. Qed.
        End option.
      End base.

      Module option.
        Lemma is_bounded_by_impl_related_hetero t
              (x : ZRange.type.option.interp t) (v : type.interp base.interp t)
        : ZRange.type.option.is_bounded_by x v = true
          -> type.related_hetero (fun t x v => ZRange.type.base.option.is_bounded_by x v = true) x v.
        Proof. induction t; cbn in *; intuition congruence. Qed.
      End option.
    End type.

    Module ident.
      Module option.
        (** First we prove relatedness for some particularly complicated identifiers separately *)
        Section interp_related.
          Context (cast_outside_of_range : zrange -> Z -> Z).

          Local Notation interp_is_related idc
            := (type.related_hetero
                  (fun t st v => ZRange.type.base.option.is_bounded_by st v = true)
                  (ZRange.ident.option.interp idc)
                  (ident.gen_interp cast_outside_of_range idc)).

          Local Ltac z_cast_t :=
            cbn [type.related_hetero ZRange.ident.option.interp ident.interp ident.gen_interp respectful_hetero type.interp ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp ZRange.type.base.option.Some];
            cbv [ZRange.ident.option.interp_Z_cast ident.cast ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by is_tighter_than_bool respectful_hetero is_bounded_by_bool];
            intros; break_innermost_match; trivial;
            rewrite ?Bool.andb_true_iff, ?Bool.andb_false_iff in *; destruct_head'_and; destruct_head'_or; repeat apply conj; Z.ltb_to_lt;
            try reflexivity; try lia.

          Lemma interp_related_Z_cast r : interp_is_related (@ident.Z_cast r).
          Proof. z_cast_t. Qed.

          Lemma interp_related_Z_cast2 r : interp_is_related (@ident.Z_cast2 r).
          Proof. z_cast_t. Qed.

          Lemma interp_related_List_flat_map A B : interp_is_related (@ident.List_flat_map A B).
          Proof.
            cbn; cbv [respectful_hetero]; intros.
            destruct_head' option; cbn in *; [ | reflexivity ].
            break_match; cbn in *; [ | reflexivity ].
            let v := (eval cbv [base.interp ZRange.type.base.option.interp ZRange.type.base.interp] in (@ZRange.type.base.option.interp)) in
            progress change v with (@ZRange.type.base.option.interp) in *.
            progress fold (@base.interp) in *.
            rewrite FoldBool.fold_andb_map_iff in *.
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
                         | rewrite FoldBool.fold_andb_map_iff in *
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
          Proof.
            cbn; cbv [respectful_hetero]; intros.
            destruct_head' option; cbn in *; [ | break_innermost_match; reflexivity ].
            let v := (eval cbv [base.interp ZRange.type.base.option.interp ZRange.type.base.interp] in (@ZRange.type.base.option.interp)) in
            progress change v with (@ZRange.type.base.option.interp) in *.
            progress fold (@base.interp) in *.
            rewrite FoldBool.fold_andb_map_iff in *.
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
                           | [ |- context[Option.bind ?x ?y] ] => destruct x eqn:?
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
                    | [ |- context[Nat.eqb ?a ?b = true] ] => rewrite !Nat.eqb_eq
                    | [ |- context[Z.eqb ?a ?b = true] ] => rewrite !Z.eqb_eq
                    | [ H : context[andb ?a ?b = true] |- _ ] => rewrite !Bool.andb_true_iff in H
                    | [ H : context[Z.leb ?a ?b = true] |- _ ] => rewrite !Z.leb_le in H
                    | [ H : context[Nat.eqb ?a ?b = true] |- _ ] => rewrite !Nat.eqb_eq in H
                    | [ H : context[Z.eqb ?a ?b = true] |- _ ] => rewrite !Z.eqb_eq in H
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
                           | [ H : FoldBool.fold_andb_map _ ?l1 ?l2 = true |- length ?l1 = length ?l2 ]
                             => eapply FoldBool.fold_andb_map_length, H
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
                                omega
                           | [ |- (0 <= 1)%Z ] => clear; omega
                           end
                         | handle_lt_le_t_step_fast
                         | simplify_ranges_t_step_fast
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
                         | progress cbn [ZRange.type.base.option.is_bounded_by is_bounded_by_bool ZRange.type.base.is_bounded_by lower upper fst snd projT1 projT2 bool_eq base.interp base.base_interp Option.bind FoldBool.fold_andb_map negb ZRange.ident.option.to_literal ZRange.type.base.option.None ident.to_fancy invert_Some ident.fancy.interp ident.fancy.interp_with_wordmax fst snd ZRange.type.base.option.interp ZRange.type.base.interp List.combine List.In] in *
                         | progress destruct_head'_bool
                         | solve [ auto with nocore ]
                         | progress fold (@base.interp) in *
                         | let v := (eval cbv [base.interp ZRange.type.base.option.interp ZRange.type.base.interp] in (@ZRange.type.base.option.interp)) in
                           progress change v with (@ZRange.type.base.option.interp) in *
                         | handle_lt_le_t_step
                         | simplify_ranges_t_step
                         | match goal with
                           | [ |- context[andb ?a ?b = true] ] => rewrite !Bool.andb_true_iff
                           | [ H : FoldBool.fold_andb_map _ _ _ = true |- _ ] => rewrite FoldBool.fold_andb_map_iff in H
                           | [ |- FoldBool.fold_andb_map _ _ _ = true ] => rewrite FoldBool.fold_andb_map_iff
                           | [ H : forall (x : option _), _ |- _ ] => pose proof (H None); specialize (fun x => H (Some x))
                           | [ H : forall x y z (w : option _), _ |- _ ] => pose proof (fun x y z => H x y z None); specialize (fun x y z w => H x y z (Some w))
                           | [ H : forall v, _ = v \/ _ -> _ |- _ ] => pose proof (H _ (or_introl eq_refl)); specialize (fun v pf => H v (or_intror pf))
                           | [ |- context[length ?x] ] => tryif is_var x then fail else (progress autorewrite with distr_length)
                           | [ H : List.In _ (List.combine _ _) |- _ ] => apply List.In_nth_error in H
                           | [ H : context[List.nth_error (List.combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                           | [ |- context[List.nth_error (List.combine _ _) _] ] => rewrite nth_error_combine
                           | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map in H
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
                           | [ H : List.nth_error (repeat _ _) _ = Some _ |- _ ] => apply nth_error_repeat in H
                           | [ H : length ?l1 = length ?l2 |- context[length ?l1] ] => rewrite H
                           | [ H : length ?l1 = length ?l2, H' : context[length ?l1] |- _ ] => rewrite H in H'
                           | [ |- context[List.flat_map _ _] ] => rewrite List.flat_map_concat_map, concat_fold_right_app
                           | [ H : S _ = S _ |- _ ] => inversion H; clear H
                           | [ H : List.fold_right (fun x y => x <- x; y <- y; Some _)%option (Some ?init) ?ls = Some ?v |- _]
                             => rewrite OptionList.fold_right_option_seq in H
                           | [ |- and _ _ ] => apply conj
                           end
                         | progress cbv [bool_eq option_map List.nth_default Definitions.Z.bneg is_bounded_by_bool] in *
                         | match goal with
                           | [ |- ?R (nat_rect ?P ?O ?S ?n) (nat_rect ?P' ?O' ?S' ?n) = true ]
                             => is_var n; induction n; cbn [nat_rect];
                                generalize dependent (nat_rect P O S); generalize dependent (nat_rect P' O' S');
                                intros
                           | [ |- ?R (nat_rect ?P ?O ?S ?n ?x) (nat_rect ?P' ?O' ?S' ?n ?y) = true ]
                             => is_var n; is_var x; is_var y;
                                revert dependent x; revert dependent y; induction n; cbn [nat_rect];
                                generalize dependent (nat_rect P O S); generalize dependent (nat_rect P' O' S');
                                intros
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
                           | [ H : length ?ls = length ?ls' |- ?R (list_rect ?P ?N ?C ?ls) (list_rect ?P' ?N' ?C' ?ls') = true ]
                             => is_var ls; is_var ls';
                                let IH := fresh "IH" in
                                revert dependent ls'; induction ls as [|? ls IH]; intros [|? ls']; intros; cbn [list_rect length] in *;
                                [
                                 | exfalso; discriminate | exfalso; discriminate
                                 | specialize (IH ls');
                                   generalize dependent (list_rect P N C); generalize dependent (list_rect P' N' C') ];
                                intros
                           | [ H : forall a b, ?R a b = true -> ?R' (?f a) (?g b) = true |- ?R' (?f _) (?g _) = true ] => apply H; clear H
                           | [ H : forall a b, ?R a b = true -> forall c d, ?R' c d = true -> ?R'' (?f a c) (?g b d) = true |- ?R'' (?f _ _) (?g _ _) = true ]
                             => apply H; clear H
                           | [ H : forall a b, ?R a b = true -> forall c d, ?R' c d = true -> forall e f, ?R'' e f = true -> ?R''' (?F _ _ _) (?G _ _ _) = true |- ?R''' (?F _ _ _) (?G _ _ _) = true ]
                             => apply H; clear H
                           end ].

          Axiom proof_admitted : False.
          Notation admit := (match proof_admitted with end).

          Lemma interp_related {t} (idc : ident t) : interp_is_related idc.
          Proof.
            destruct idc.
            all: lazymatch goal with
                 | [ |- context[ident.Z_cast] ] => apply interp_related_Z_cast
                 | [ |- context[ident.Z_cast2] ] => apply interp_related_Z_cast2
                 | [ |- context[ident.List_flat_map] ] => apply interp_related_List_flat_map
                 | [ |- context[ident.List_partition] ] => apply interp_related_List_partition
                 | _ => idtac
                 end.
            all: cbn [type.related_hetero ZRange.ident.option.interp ident.interp ident.gen_interp respectful_hetero type.interp ZRange.type.base.option.interp ZRange.type.base.interp base.interp base.base_interp ZRange.type.base.option.Some ZRange.ident.option.of_literal].
            all: cbv [respectful_hetero option_map list_case].
            all: intros.
            all: destruct_head_hnf' prod.
            all: destruct_head_hnf' option.
            Time all: try solve [ non_arith_t ].
            all: cbn [ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by Option.bind ZRange.ident.option.to_literal ident.fancy.interp invert_Some ident.to_fancy ident.fancy.interp_with_wordmax] in *.
            all: break_innermost_match; try reflexivity.
            Time all: try solve [ non_arith_t ].
            all: repeat first [ progress subst
                              | progress inversion_prod
                              | progress inversion_option
                              | progress destruct_head'_and
                              | progress cbn [ZRange.type.base.option.is_tighter_than lower upper fst snd Option.bind] in *
                              | progress cbv [Definitions.Z.lnot_modulo Definitions.Z.add_with_carry] in *
                              | handle_lt_le_t_step
                              | simplify_ranges_t_step
                              | discriminate
                              | solve [ auto using ZRange.is_bounded_by_bool_Proper_if_sumbool_union ]
                              | match goal with
                                | [ H : ?x = ?x |- _ ] => clear H
                                end
                              | progress rewrite ?Z.mul_split_div, ?Z.mul_split_mod, ?Z.add_get_carry_full_div, ?Z.add_get_carry_full_mod, ?Z.add_with_get_carry_full_div, ?Z.add_with_get_carry_full_mod, ?Z.sub_get_borrow_full_div, ?Z.sub_get_borrow_full_mod, ?Z.sub_with_get_borrow_full_div, ?Z.sub_with_get_borrow_full_mod, ?Z.zselect_correct, ?Z.add_modulo_correct ].
            all: clear cast_outside_of_range.
            all: repeat match goal with
                        | [ H : ?T |- _ ]
                          => lazymatch T with
                            | Z => clear H
                            | zrange => clear H
                            | _ = true => revert H
                            | _ = false => revert H
                            | _ => fail 10 T
                            end
                        end.
            all: exact admit.
          Qed.
        End interp_related.
      End option.
    End ident.
  End ZRange.
  Module Import partial.
    Import AbstractInterpretation.Compilers.partial.
    Import NewPipeline.UnderLets.Compilers.UnderLets.
    Section with_type.
      Context {base_type : Type}.
      Local Notation type := (type base_type).
      Let type_base (x : base_type) : type := type.base x.
      Local Coercion type_base : base_type >-> type.
      Context {ident : type -> Type}.
      Local Notation Expr := (@expr.Expr base_type ident).
      Context (abstract_domain' base_interp : base_type -> Type)
              (ident_interp : forall t, ident t -> type.interp base_interp t)
              (abstraction_relation' : forall t, abstract_domain' t -> base_interp t -> Prop)
              (bottom' : forall A, abstract_domain' A)
              (bottom'_related : forall t v, abstraction_relation' t (bottom' t) v)
              (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
              (ident_interp_Proper : forall t (idc : ident t), type.related_hetero abstraction_relation' (abstract_interp_ident t idc) (ident_interp t idc))
              (ident_interp_Proper' : forall t, Proper (eq ==> type.eqv) (ident_interp t))
              (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop)
              (abstraction_relation'_Proper : forall t, Proper (abstract_domain'_R t ==> eq ==> Basics.impl) (abstraction_relation' t))
              (abstract_domain'_R_Reflexive : forall t, Reflexive (abstract_domain'_R t)).
      Local Notation abstract_domain := (@abstract_domain base_type abstract_domain').
      Definition abstraction_relation {t} : abstract_domain t -> type.interp base_interp t -> Prop
        := type.related_hetero (@abstraction_relation').
      Local Notation bottom := (@bottom base_type abstract_domain' (@bottom')).
      Local Notation bottom_for_each_lhs_of_arrow := (@bottom_for_each_lhs_of_arrow base_type abstract_domain' (@bottom')).
      Local Notation var := (type.interp base_interp).
      Local Notation expr := (@expr.expr base_type ident).
      Local Notation UnderLets := (@UnderLets base_type ident).
      Local Notation value := (@value base_type ident var abstract_domain').
      Local Notation value_with_lets := (@value_with_lets base_type ident var abstract_domain').
      Local Notation state_of_value := (@state_of_value base_type ident var abstract_domain').
      Context (annotate : forall (is_let_bound : bool) t, abstract_domain' t -> @expr var t -> @UnderLets var (@expr var t))
              (interp_ident : forall t, ident t -> value_with_lets t)
              (ident_extract : forall t, ident t -> abstract_domain t)
              (interp_annotate
               : forall is_let_bound t st e
                   (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e)),
                  expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate is_let_bound t st e))
                  = expr.interp (@ident_interp) e).
      Local Notation eta_expand_with_bound' := (@eta_expand_with_bound' base_type ident _ abstract_domain' annotate bottom').
      Local Notation eval_with_bound' := (@partial.eval_with_bound' base_type ident _ abstract_domain' annotate bottom' interp_ident).
      Local Notation extract' := (@extract' base_type ident abstract_domain' ident_extract).
      Local Notation extract_gen := (@extract_gen base_type ident abstract_domain' ident_extract).
      Local Notation reify := (@reify base_type ident _ abstract_domain' annotate bottom').
      Local Notation reflect := (@reflect base_type ident _ abstract_domain' annotate bottom').
      Local Notation interp := (@interp base_type ident var abstract_domain' annotate bottom' interp_ident).

      Lemma bottom_related t v : @abstraction_relation t bottom v.
      Proof using bottom'_related. cbv [abstraction_relation]; induction t; cbn; cbv [respectful_hetero]; eauto. Qed.

      Lemma bottom_for_each_lhs_of_arrow_related t v : type.and_for_each_lhs_of_arrow (@abstraction_relation) (@bottom_for_each_lhs_of_arrow t) v.
      Proof using bottom'_related. induction t; cbn; eauto using bottom_related. Qed.

      (*
      Local Notation reify1 := (@reify base_type ident var1 abstract_domain' annotate1 bottom').
      Local Notation reify2 := (@reify base_type ident var2 abstract_domain' annotate2 bottom').
      Local Notation reflect1 := (@reflect base_type ident var1 abstract_domain' annotate1 bottom').
      Local Notation reflect2 := (@reflect base_type ident var2 abstract_domain' annotate2 bottom').
      Local Notation interp1 := (@interp base_type ident var1 abstract_domain' annotate1 bottom' interp_ident1).
      Local Notation interp2 := (@interp base_type ident var2 abstract_domain' annotate2 bottom' interp_ident2).
      Local Notation eval_with_bound'1 := (@eval_with_bound' base_type ident var1 abstract_domain' annotate1 bottom' interp_ident1).
      Local Notation eval_with_bound'2 := (@eval_with_bound' base_type ident var2 abstract_domain' annotate2 bottom' interp_ident2).
      Local Notation eval'1 := (@eval' base_type ident var1 abstract_domain' annotate1 bottom' interp_ident1).
      Local Notation eval'2 := (@eval' base_type ident var2 abstract_domain' annotate2 bottom' interp_ident2).
      Local Notation eta_expand_with_bound'1 := (@eta_expand_with_bound' base_type ident var1 abstract_domain' annotate1 bottom').
      Local Notation eta_expand_with_bound'2 := (@eta_expand_with_bound' base_type ident var2 abstract_domain' annotate2 bottom').
*)
(*

      Fixpoint value (t : type)
        := (abstract_domain t
            * match t return Type (* COQBUG(https://github.com/coq/coq/issues/7727) *) with
              | type.base t
                => @expr var t
              | type.arrow s d
                => value s -> UnderLets (value d)
              end)%type.

      Definition value_with_lets (t : type)
        := UnderLets (value t).


      Fixpoint bottom {t} : abstract_domain t
        := match t with
           | type.base t => bottom' t
           | type.arrow s d => fun _ => @bottom d
           end.

      Fixpoint bottom_for_each_lhs_of_arrow {t} : type.for_each_lhs_of_arrow abstract_domain t
        := match t return type.for_each_lhs_of_arrow abstract_domain t with
           | type.base t => tt
           | type.arrow s d => (bottom, @bottom_for_each_lhs_of_arrow d)
           end.

      Definition state_of_value {t} : value t -> abstract_domain t
        := match t return value t -> abstract_domain t with
           | type.base t => fun '(st, v) => st
           | type.arrow s d => fun '(st, v) => st
           end.
 *)

      Fixpoint related_bounded_value {t} : abstract_domain t -> value t -> type.interp base_interp t -> Prop
        := match t return abstract_domain t -> value t -> type.interp base_interp t -> Prop with
           | type.base t
             => fun st '(e_st, e) v
                => abstract_domain'_R t st e_st
                   /\ expr.interp ident_interp e = v
                   /\ abstraction_relation' t st v
           | type.arrow s d
             => fun st '(e_st, e) v
                => (** XXX FIXME: DO WE NEED TO DO ANYTHING WITH e_st? *)
                  forall st_s e_s v_s,
                    @related_bounded_value s st_s e_s v_s
                    -> @related_bounded_value d (st st_s) (UnderLets.interp ident_interp (e e_s)) (v v_s)
           end.
      Definition related_bounded_value_with_lets {t} : abstract_domain t -> value_with_lets t -> type.interp base_interp t -> Prop
        := fun st e v => related_bounded_value st (UnderLets.interp ident_interp e) v.

      Axiom proof_admitted : False.
      Notation admit := (match proof_admitted with end).

      Fixpoint interp_reify
               is_let_bound {t} st e v b_in
               (H : related_bounded_value st e v) {struct t}
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
              type.app_curried (expr.interp ident_interp (UnderLets.interp ident_interp (@reify is_let_bound t e b_in))) arg1
              = type.app_curried v arg2)
          /\ (forall arg1
                     (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1)
                     (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                 abstraction_relation'
                   _
                   (type.app_curried st b_in)
                   (type.app_curried (expr.interp ident_interp (UnderLets.interp ident_interp (@reify is_let_bound t e b_in))) arg1))
      with interp_reflect
             {t} st e v
             (H_val : expr.interp ident_interp e == v)
             (Hst : abstraction_relation st (expr.interp ident_interp e))
             {struct t}
           : related_bounded_value
               st
               (@reflect t e st)
               v.
      Proof using interp_annotate abstraction_relation'_Proper abstract_domain'_R_Reflexive bottom'_related.
        all: destruct t as [t|s d];
          [ clear interp_reify interp_reflect
          | pose proof (fun is_let_bound => interp_reify is_let_bound s) as interp_reify_s;
            pose proof (fun is_let_bound => interp_reify is_let_bound d) as interp_reify_d;
            pose proof (interp_reflect s) as interp_reflect_s;
            pose proof (interp_reflect d) as interp_reflect_d;
            clear interp_reify interp_reflect ].
        all: cbn [reify reflect]; fold (@reify) (@reflect).
        all: repeat first [ reflexivity
                          | progress eta_expand
                          | progress cbn [related_bounded_value UnderLets.interp expr.interp type.final_codomain type.related] in *
                          | progress fold (@type.interp)
                          | progress destruct_head'_and
                          | progress destruct_head_hnf' and
                          | progress destruct_head_hnf' unit
                          | progress split_and
                          | rewrite UnderLets.interp_splice
                          | rewrite UnderLets.interp_to_expr
                          | rewrite interp_annotate
                          | solve [ cbv [Proper respectful Basics.impl] in *; eauto ]
                          | progress (repeat apply conj; intros * )
                          | progress subst
                          | progress cbn [type.app_curried type.and_for_each_lhs_of_arrow] in *
                          | progress intros ].
        replace (state_of_value e_s) with st_s.
        eapply interp_reflect_d.
        all: eauto.
        all: cbn [expr.interp].
        move e at bottom.
        eapply H_val.
        all: cbv [respectful] in *.
        all: cbv [abstraction_relation] in *.
        all: cbn [type.related_hetero] in *.
        2:eapply Hst.
        all: eauto.
        rewrite type.related_iff_app_curried.
        intros.
        eapply H1.
        eauto.
        eauto.
        apply bottom_for_each_lhs_of_arrow_related.
        rewrite type.related_hetero_iff_app_curried.
        intros.
        replace x with (@bottom_for_each_lhs_of_arrow s).
        eapply H2.
        all: eauto using bottom_for_each_lhs_of_arrow_related.
        exact admit.
        exact admit.
        exact admit.
      Qed.
      (*
      Fixpoint reify (is_let_bound : bool) {t} : value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t)
        := match t return value t -> type.for_each_lhs_of_arrow abstract_domain t -> UnderLets (@expr var t) with
           | type.base t
             => fun '(st, v) 'tt
                => annotate is_let_bound t st v
           | type.arrow s d
             => fun '(f_st, f_e) '(sv, dv)
                => Base
                     (λ x , (UnderLets.to_expr
                               (fx <-- f_e (@reflect _ (expr.Var x) sv);
                                  @reify false _ fx dv)))
           end%core%expr
      with reflect {t} : @expr var t -> abstract_domain t -> value t
           := match t return @expr var t -> abstract_domain t -> value t with
              | type.base t
                => fun e st => (st, e)
              | type.arrow s d
                => fun e absf
                   => (absf,
                       (fun v
                        => let stv := state_of_value v in
                           (rv <-- (@reify false s v bottom_for_each_lhs_of_arrow);
                              Base (@reflect d (e @ rv) (absf stv))%expr)))
              end%under_lets.
       *)

      Context (interp_ident_Proper
               : forall t idc,
                  related_bounded_value (ident_extract t idc) (UnderLets.interp ident_interp (interp_ident t idc)) (ident_interp t idc)).

      Lemma interp_interp
            G {t} (e_st e1 e2 : expr t)
            (HG : forall t v1 v2 v3, List.In (existT _ t (v1, v2, v3)) G
                                     -> related_bounded_value_with_lets v1 v2 v3)
            (Hwf : expr.wf3 G e_st e1 e2)
        : related_bounded_value_with_lets
            (extract' e_st)
            (interp e1)
            (expr.interp (@ident_interp) e2).
      Proof using interp_ident_Proper interp_annotate abstraction_relation'_Proper.
        cbv [related_bounded_value_with_lets] in *;
          induction Hwf; cbn [extract' interp expr.interp related_bounded_value UnderLets.interp List.In] in *.
        all: repeat first [ progress intros
                          | progress subst
                          | progress inversion_sigma
                          | progress inversion_prod
                          | progress destruct_head'_and
                          | progress destruct_head'_or
                          | progress eta_expand
                          | progress cbn [UnderLets.interp List.In eq_rect fst snd projT1 projT2] in *
                          | rewrite UnderLets.interp_splice
                          | rewrite interp_annotate
                          | solve [ cbv [Proper respectful Basics.impl] in *; eauto ]
                          | progress specialize_by_assumption
                          | progress cbv [Let_In extract'] in *
                          | progress cbn [reify reflect state_of_value related_bounded_value] in *
                          | match goal with
                            | [ H : _ |- _ ] => tryif constr_eq H HG then fail else (apply H; clear H)
                            end
                          | break_innermost_match_step
                          | apply conj
                          | match goal with
                            | [ H : _ = _ |- _ ] => rewrite H
                            end ].
      Qed.

      (*

      Definition eval_with_bound' {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (e' <-- interp e; reify false e' st).

      Definition eval' {t} (e : @expr value_with_lets t) : expr t
        := eval_with_bound' e bottom_for_each_lhs_of_arrow.

      Definition eta_expand_with_bound' {t} (e : @expr var t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (reify false (reflect e bottom) st).

      Section extract.
        Context (ident_extract : forall t, ident t -> abstract_domain t).

        Definition extract' {t} (e : @expr abstract_domain t) : abstract_domain t
          := expr.interp (@ident_extract) e.

        Definition extract_gen {t} (e : @expr abstract_domain t) (bound : type.for_each_lhs_of_arrow abstract_domain t)
          : abstract_domain' (type.final_codomain t)
          := type.app_curried (extract' e) bound.
      End extract.
    End with_var.



      Section extract.
        Context (ident_extract : forall t, ident t -> abstract_domain t)
        {ident_extract_Proper : forall {t}, Proper (eq ==> abstract_domain_R) (ident_extract t)}.

        Local Notation extract' := (@extract' base_type ident abstract_domain' ident_extract).
        Local Notation extract_gen := (@extract_gen base_type ident abstract_domain' ident_extract).

        Lemma extract'_Proper G
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @abstract_domain_R t v1 v2)
              {t}
          : Proper (expr.wf G ==> abstract_domain_R) (@extract' t).
        Proof using ident_extract_Proper. apply expr.wf_interp_Proper_gen1, HG. Qed.

        Lemma extract_gen_Proper G
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @abstract_domain_R t v1 v2)
              {t}
          : Proper (expr.wf G ==> type.and_for_each_lhs_of_arrow (@abstract_domain_R) ==> abstract_domain'_R (type.final_codomain t)) (@extract_gen t).
        Proof using ident_extract_Proper.
          intros ?? Hwf; cbv [extract_gen respectful abstract_domain_R].
          rewrite <- type.related_iff_app_curried.
          eapply extract'_Proper; eassumption.
        Qed.
      End extract.
 *)
      Lemma interp_eval_with_bound'
            {t} (e_st e1 e2 : expr t)
            (Hwf : expr.wf3 nil e_st e1 e2)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
              type.app_curried (expr.interp ident_interp (eval_with_bound' e1 st)) arg1
              = type.app_curried (expr.interp ident_interp e2) arg2)
          /\ (forall arg1
                     (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1)
                     (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                 abstraction_relation'
                   _
                   (extract_gen e_st st)
                   (type.app_curried (expr.interp ident_interp (eval_with_bound' e1 st)) arg1)).
      Proof using interp_annotate abstraction_relation'_Proper abstract_domain'_R_Reflexive bottom'_related interp_ident_Proper.
        cbv [extract_gen extract' eval_with_bound'].
        split; intros; rewrite UnderLets.interp_to_expr, UnderLets.interp_splice.
        all: eapply interp_reify; eauto.
        all: eapply interp_interp; eauto; wf_t.
      Qed.

      Lemma interp_eta_expand_with_bound'
            {t} (e1 e2 : expr t)
            (Hwf : expr.wf nil e1 e2)
            (b_in : type.for_each_lhs_of_arrow abstract_domain t)
        : forall arg1 arg2
            (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
            (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
          type.app_curried (expr.interp ident_interp (eta_expand_with_bound' e1 b_in)) arg1 = type.app_curried (expr.interp ident_interp e2) arg2.
      Proof using interp_annotate ident_interp_Proper' bottom'_related abstraction_relation'_Proper abstract_domain'_R_Reflexive.
        cbv [eta_expand_with_bound'].
        intros; rewrite UnderLets.interp_to_expr.
        eapply interp_reify; eauto.
        eapply interp_reflect; eauto using bottom_related.
        eapply @expr.wf_interp_Proper_gen; auto using Hwf.
      Qed.

  (*
      Definition eval_with_bound' {t} (e : @expr value_with_lets t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (e' <-- interp e; reify false e' st).

      Definition eval' {t} (e : @expr value_with_lets t) : expr t
        := eval_with_bound' e bottom_for_each_lhs_of_arrow.

      Definition eta_expand_with_bound' {t} (e : @expr var t)
                 (st : type.for_each_lhs_of_arrow abstract_domain t)
        : expr t
        := UnderLets.to_expr (reify false (reflect e bottom) st).
*)
    End with_type.

    Module ident.
      Import defaults.
      Local Notation UnderLets := (@UnderLets base.type ident).
      Section with_type.
        Context (abstract_domain' : base.type -> Type).
        Local Notation abstract_domain := (@abstract_domain base.type abstract_domain').
        Context (annotate_ident : forall t, abstract_domain' t -> option (ident (t -> t)))
                (bottom' : forall A, abstract_domain' A)
                (abstract_interp_ident : forall t, ident t -> type.interp abstract_domain' t)
                (update_literal_with_state : forall A : base.type.base, abstract_domain' A -> base.interp A -> base.interp A)
                (extract_list_state : forall A, abstract_domain' (base.type.list A) -> option (list (abstract_domain' A)))
                (is_annotated_for : forall t t', ident t -> abstract_domain' t' -> bool)
                (is_annotation : forall t, ident t -> bool)
                (abstraction_relation' : forall t, abstract_domain' t -> base.interp t -> Prop)
                (abstract_domain'_R : forall t, abstract_domain' t -> abstract_domain' t -> Prop)
                (abstraction_relation'_Proper : forall t, Proper (abstract_domain'_R t ==> eq ==> Basics.impl) (abstraction_relation' t))
                (abstract_domain'_R_Reflexive : forall t, Reflexive (abstract_domain'_R t))
                (bottom'_related : forall t v, abstraction_relation' t (bottom' t) v)
                (cast_outside_of_range : zrange -> Z -> Z).
        Local Notation abstraction_relation := (@abstraction_relation base.type abstract_domain' base.interp abstraction_relation').
        Local Notation ident_interp := (@ident.gen_interp cast_outside_of_range).
        Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' abstract_domain'_R).
        Context {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                (interp_annotate_ident
                 : forall t st idc,
                    annotate_ident t st = Some idc
                    -> forall v, abstraction_relation' _ st v
                           -> ident_interp idc v = v)
                (interp_update_literal_with_state
                 : forall (t : base.type.base) (st : abstract_domain' t) (v : base.interp t),
                    abstraction_relation' t st v -> update_literal_with_state t st v = v)
                (*is_annotation_abstraction_relation_weaken
                 : forall t st idc v,
                    is_annotation _ idc = true
                    -> abstraction_relation' _ st v
                    -> abstraction_relation' _ (abstract_interp_ident (type.base t -> type.base t)%etype idc st) v*)
                (*interp_annotate_ident_commute
                 : forall t st v cst0 cst1,
                    is_annotation (type.base t -> type.base t) cst0 = true ->
                    annotate_ident t (abstract_interp_ident (type.base t -> type.base t) cst0 st) = Some cst1 ->
                    abstraction_relation' t st (ident_interp cst0 v) -> ident_interp cst1 v = ident_interp cst0 v)*)
                (abstract_interp_ident_Proper'
                 : forall t idc, type.related_hetero (@abstraction_relation') (abstract_interp_ident t idc) (ident_interp idc))
                (extract_list_state_related
                 : forall t st ls v st' v',
                    extract_list_state t st = Some ls
                    -> abstraction_relation' _ st v
                    -> List.In (st', v') (List.combine ls v)
                    -> abstraction_relation' t st' v')
                (extract_list_state_length_good
                 : forall t st ls v,
                    extract_list_state t st = Some ls
                    -> abstraction_relation' _ st v
                    -> length ls = length v).

        Local Notation update_annotation := (@ident.update_annotation _ abstract_domain' annotate_ident is_annotated_for).
        Local Notation annotate_with_ident := (@ident.annotate_with_ident _ abstract_domain' annotate_ident is_annotated_for).
        Local Notation annotate_base := (@ident.annotate_base _ abstract_domain' annotate_ident update_literal_with_state is_annotated_for).
        Local Notation annotate := (@ident.annotate _ abstract_domain' annotate_ident abstract_interp_ident update_literal_with_state extract_list_state is_annotated_for).
        Local Notation interp_ident := (@ident.interp_ident _ abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotated_for).
        Local Notation related_bounded_value := (@related_bounded_value base.type ident abstract_domain' base.interp (@ident_interp) abstraction_relation' abstract_domain'_R).
        Local Notation reify := (@reify base.type ident _ abstract_domain' annotate bottom').
        Local Notation reflect := (@reflect base.type ident _ abstract_domain' annotate bottom').

        Lemma interp_update_annotation t st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e))
          : expr.interp (@ident_interp) (@update_annotation t st e)
            = expr.interp (@ident_interp) e.
        Proof using interp_annotate_ident.
          cbv [update_annotation];
            repeat first [ reflexivity
                         | progress subst
                         | progress eliminate_hprop_eq
                         | progress cbn [expr.interp eq_rect] in *
                         | erewrite interp_annotate_ident by eassumption
                         | progress expr.invert_match
                         | progress type_beq_to_eq
                         | progress rewrite_type_transport_correct
                         | progress break_innermost_match_step ].
        Qed.

        Lemma interp_annotate_with_ident is_let_bound t st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e))
          : expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate_with_ident is_let_bound t st e))
            = expr.interp (@ident_interp) e.
        Proof using interp_annotate_ident.
          cbv [annotate_with_ident]; break_innermost_match; cbn [expr.interp UnderLets.interp];
            apply interp_update_annotation; assumption.
        Qed.

        Lemma interp_annotate_base is_let_bound (t : base.type.base) st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base (base.type.type_base t)) (@ident_interp) e))
          : expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate_base is_let_bound t st e))
            = expr.interp (@ident_interp) e.
        Proof using interp_annotate_ident interp_update_literal_with_state.
          cbv [annotate_base]; break_innermost_match; expr.invert_subst; cbv beta iota in *; subst.
          { cbn [expr.interp UnderLets.interp ident.smart_Literal ident_interp] in *; eauto. }
          { apply interp_annotate_with_ident; assumption. }
        Qed.

        Lemma interp_annotate is_let_bound (t : base.type) st e
              (He : abstraction_relation' t st (expr.interp (t:=type.base t) (@ident_interp) e))
          : expr.interp (@ident_interp) (UnderLets.interp (@ident_interp) (@annotate is_let_bound t st e))
            = expr.interp (@ident_interp) e.
        Proof using interp_update_literal_with_state interp_annotate_ident abstract_interp_ident_Proper' extract_list_state_related extract_list_state_length_good.
          induction t; cbn [annotate]; auto using interp_annotate_base.
          all: repeat first [ reflexivity
                            | progress subst
                            | progress inversion_option
                            | progress inversion_prod
                            | progress destruct_head'_ex
                            | progress destruct_head'_and
                            | progress break_innermost_match
                            | progress break_innermost_match_hyps
                            | progress expr.invert_subst
                            | progress cbn [fst snd UnderLets.interp expr.interp ident_interp Nat.add] in *
                            | rewrite !UnderLets.interp_splice
                            | rewrite !UnderLets.interp_splice_list
                            | rewrite !List.map_map
                            | rewrite expr.interp_reify_list
                            | rewrite nth_error_combine
                            | apply interp_annotate_with_ident; assumption
                            | progress fold (@base.interp) in *
                            | progress intros
                            | pose proof (@extract_list_state_length_good _ _ _ _ ltac:(eassumption) ltac:(eassumption)); clear extract_list_state_length_good
                            | match goal with
                              | [ H : context[expr.interp _ (reify_list _)] |- _ ] => rewrite expr.interp_reify_list in H
                              | [ H : abstraction_relation' (_ * _) _ (_, _) |- _ ]
                                => pose proof (abstract_interp_ident_Proper' _ ident.fst _ _ H);
                                  pose proof (abstract_interp_ident_Proper' _ ident.snd _ _ H);
                                  clear H
                              | [ H : context[_ = _] |- _ = _ ] => rewrite H by assumption
                              | [ |- List.map ?f (List.combine ?l1 ?l2) = List.map ?g ?l2 ]
                                => transitivity (List.map g (List.map (@snd _ _) (List.combine l1 l2)));
                                  [ rewrite List.map_map; apply List.map_ext_in
                                  | rewrite map_snd_combine, List.firstn_all2; [ reflexivity | ] ]
                              | [ Hls : extract_list_state ?t ?st = Some ?ls, He : abstraction_relation' _ ?st ?v |- abstraction_relation' _ _ _ ]
                                => apply (fun st' v' => extract_list_state_related t st ls v st' v' Hls He)
                              | [ H : context[List.nth_error (List.combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                              | [ H : List.In _ (List.combine _ _) |- _ ] => apply List.In_nth_error in H
                              | [ |- List.In _ (List.combine _ _) ] => eapply nth_error_In
                              | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                              | [ H : List.nth_error (List.map _ _) _ = Some _ |- _ ] => apply nth_error_map in H
                              | [ H : List.nth_error _ _ = None |- _ ] => rewrite List.nth_error_None in H
                              | [ H : context[length ?ls] |- _ ] => tryif is_var ls then fail else (progress autorewrite with distr_length in H)
                              | [ |- context[length ?ls] ] => tryif is_var ls then fail else (progress autorewrite with distr_length)
                              | [ H : List.nth_error ?ls ?n = Some _, H' : length ?ls <= ?n |- _ ]
                                => apply nth_error_value_length in H; exfalso; clear -H H'; lia
                              | [ H : List.nth_error ?l ?n = _, H' : List.nth_error ?l ?n' = _ |- _ ]
                                => unify n n'; rewrite H in H'
                              | [ Hls : extract_list_state ?t ?st = Some ?ls, He : abstraction_relation' _ ?st ?v |- _ ]
                                => pose proof (fun st' v' => extract_list_state_related t st ls v st' v' Hls He); clear extract_list_state_related
                              | [ IH : forall st e, _ -> expr.interp _ (UnderLets.interp _ (annotate _ _ _)) = _ |- List.map (fun x => expr.interp _ _) (List.combine _ _) = expr.interp _ _ ]
                                => erewrite List.map_ext_in;
                                   [
                                   | intros; eta_expand; rewrite IH; cbn [expr.interp ident_interp ident.smart_Literal]; [ reflexivity | ] ]
                              | [ H : abstraction_relation' _ ?st (List.map (expr.interp _) ?ls), H' : forall st' v', List.In _ (List.combine _ _) -> abstraction_relation' _ _ _, H'' : List.nth_error ?ls _ = Some ?e |- abstraction_relation' _ _ (expr.interp _ ?e) ]
                                => apply H'
                              | [ H : context[List.nth_error (List.seq _ _) _] |- _ ] => rewrite nth_error_seq in H
                              end
                            | apply Nat.eq_le_incl
                            | rewrite <- List.map_map with (f:=fst), map_fst_combine
                            | rewrite Lists.List.firstn_all2 by distr_length
                            | apply map_nth_default_seq
                            | match goal with
                              | [ H : context[expr.interp _ _ = expr.interp _ _] |- expr.interp _ _ = expr.interp _ _ ] => apply H; clear H
                              | [ H : forall st' v', List.In _ (List.combine _ _) -> abstraction_relation' _ _ _ |- abstraction_relation' _ _ _ ]
                                => apply H; clear H; cbv [List.nth_default]
                              | [ |- None = Some _ ] => exfalso; lia
                              end ].
        Qed.

        Lemma interp_ident_Proper_not_nth_default t idc
          : related_bounded_value (abstract_interp_ident t idc) (UnderLets.interp (@ident_interp) (Base (reflect (expr.Ident idc) (abstract_interp_ident _ idc)))) (ident_interp idc).
        Proof using abstract_domain'_R_Reflexive abstract_interp_ident_Proper' abstraction_relation'_Proper bottom'_related extract_list_state_length_good extract_list_state_related interp_annotate_ident interp_update_literal_with_state.
          cbn [UnderLets.interp].
          eapply interp_reflect;
            try first [ apply ident.gen_interp_Proper
                      | apply abstract_interp_ident_Proper'
                      | apply interp_annotate ];
            eauto.
        Qed.

        Lemma interp_ident_Proper_nth_default T (idc:=@ident.List_nth_default T)
          : related_bounded_value (abstract_interp_ident _ idc) (UnderLets.interp (@ident_interp) (interp_ident idc)) (ident_interp idc).
        Proof using abstract_interp_ident_Proper abstract_interp_ident_Proper' abstraction_relation'_Proper extract_list_state_length_good extract_list_state_related interp_annotate_ident interp_update_literal_with_state.
          subst idc; cbn [interp_ident reify reflect fst snd UnderLets.interp ident_interp related_bounded_value abstract_domain value].
          cbv [abstract_domain]; cbn [type.interp bottom_for_each_lhs_of_arrow state_of_value fst snd].
          repeat first [ progress intros
                       | progress cbn [UnderLets.interp fst snd expr.interp ident_interp] in *
                       | progress destruct_head'_prod
                       | progress destruct_head'_and
                       | progress subst
                       | progress eta_expand
                       | rewrite UnderLets.interp_splice
                       | progress expr.invert_subst
                       | break_innermost_match_step
                       | progress cbn [type.interp base.interp base.base_interp] in *
                       | rewrite interp_annotate
                       | solve [ cbv [Proper respectful Basics.impl] in *; eauto ]
                       | split; [ apply (@abstract_interp_ident_Proper _ (@ident.List_nth_default T) _ eq_refl) | ]
                       | split; [ reflexivity | ]
                       | apply (@abstract_interp_ident_Proper' _ (@ident.List_nth_default T))
                       | apply conj
                       | rewrite map_nth_default_always
                       | match goal with
                         | [ H : context[expr.interp _ (UnderLets.interp _ (annotate _ _ _))] |- _ ]
                           => rewrite interp_annotate in H
                         | [ H : context[expr.interp _ (reify_list _)] |- _ ]
                           => rewrite expr.interp_reify_list in H
                         | [ H : _ = reify_list _ |- _ ] => apply (f_equal (expr.interp (@ident_interp))) in H
                         | [ H : expr.interp _ ?x = _ |- context[expr.interp _ ?x] ] => rewrite H
                         end ].
        Qed.

        Lemma interp_ident_Proper t idc
          : related_bounded_value (abstract_interp_ident t idc) (UnderLets.interp (@ident_interp) (interp_ident idc)) (ident_interp idc).
        Proof.
          pose idc as idc'.
          destruct idc; first [ refine (@interp_ident_Proper_not_nth_default _ idc')
                              | refine (@interp_ident_Proper_nth_default _) ].
        Qed.

        (*Context {annotate_ident_Proper : forall t, Proper (abstract_domain'_R t ==> eq) (annotate_ident t)}
                {abstract_interp_ident_Proper : forall t, Proper (eq ==> @abstract_domain_R t) (abstract_interp_ident t)}
                {bottom'_Proper : forall t, Proper (abstract_domain'_R t) (bottom' t)}
                {update_literal_with_state_Proper : forall t, Proper (abstract_domain'_R (base.type.type_base t) ==> eq ==> eq) (update_literal_with_state t)}
                (extract_list_state_length : forall t v1 v2, abstract_domain'_R _ v1 v2 -> option_map (@length _) (extract_list_state t v1) = option_map (@length _) (extract_list_state t v2))
                (extract_list_state_rel : forall t v1 v2, abstract_domain'_R _ v1 v2 -> forall l1 l2, extract_list_state t v1 = Some l1 -> extract_list_state t v2 = Some l2 -> forall vv1 vv2, List.In (vv1, vv2) (List.combine l1 l2) -> @abstract_domain'_R t vv1 vv2).
         *)
        Local Notation eval_with_bound := (@partial.ident.eval_with_bound _ abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotated_for).
        Local Notation eta_expand_with_bound := (@partial.ident.eta_expand_with_bound _ abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotated_for).
        Local Notation extract := (@ident.extract abstract_domain' abstract_interp_ident).

        Lemma interp_eval_with_bound
              {t} (e_st e1 e2 : expr t)
              (Hwf : expr.wf3 nil e_st e1 e2)
              (st : type.for_each_lhs_of_arrow abstract_domain t)
          : (forall arg1 arg2
                    (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                    (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1),
                type.app_curried (expr.interp (@ident_interp) (eval_with_bound e1 st)) arg1
                = type.app_curried (expr.interp (@ident_interp) e2) arg2)
            /\ (forall arg1
                       (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) st arg1)
                       (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1),
                   abstraction_relation'
                     _
                     (extract e_st st)
                     (type.app_curried (expr.interp (@ident_interp) (eval_with_bound e1 st)) arg1)).
        Proof. cbv [extract eval_with_bound]; apply @interp_eval_with_bound' with (abstract_domain'_R:=abstract_domain'_R); auto using interp_annotate, interp_ident_Proper. Qed.

        Lemma interp_eta_expand_with_bound
              {t} (e1 e2 : expr t)
              (Hwf : expr.wf nil e1 e2)
              (b_in : type.for_each_lhs_of_arrow abstract_domain t)
          : forall arg1 arg2
                   (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                   (Harg1 : type.and_for_each_lhs_of_arrow (@abstraction_relation) b_in arg1),
            type.app_curried (expr.interp (@ident_interp) (eta_expand_with_bound e1 b_in)) arg1 = type.app_curried (expr.interp (@ident_interp) e2) arg2.
        Proof. cbv [partial.ident.eta_expand_with_bound]; eapply interp_eta_expand_with_bound'; eauto using interp_annotate, ident.gen_interp_Proper. Qed.

(*
        Definition eval {t} (e : @expr value_with_lets t) : @expr var t
          := @eval' base.type ident var abstract_domain' annotate bottom' (@interp_ident) t e.


*)
        (*
        Section extract.
          Local Notation extract := (@ident.extract abstract_domain' abstract_interp_ident).

          Lemma extract_Proper G
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @abstract_domain_R t v1 v2)
                {t}
            : Proper (expr.wf G ==> type.and_for_each_lhs_of_arrow (@abstract_domain_R) ==> abstract_domain'_R (type.final_codomain t)) (@extract t).
          Proof using abstract_interp_ident_Proper.
            apply @extract_gen_Proper; eauto.
          Qed.
        End extract.*)
      End with_type.
    End ident.

    Section specialized.
      Import defaults.
      Local Notation abstract_domain' := ZRange.type.base.option.interp (only parsing).
      Local Notation abstract_domain := (@partial.abstract_domain base.type abstract_domain').
      Local Notation abstract_domain'_R t := (@eq (abstract_domain' t)) (only parsing).
      Local Notation abstract_domain_R := (@abstract_domain_R base.type abstract_domain' (fun t => abstract_domain'_R t)).

      Definition abstraction_relation' {t} : abstract_domain' t -> base.interp t -> Prop
        := fun st v => @ZRange.type.base.option.is_bounded_by t st v = true.

      Lemma interp_annotate_ident {t} st idc
            (Hst : @annotate_ident t st = Some idc)
        : forall v, abstraction_relation' st v
               -> (forall cast_outside_of_range,
                     ident.gen_interp cast_outside_of_range idc v = v).
      Proof.
        cbv [annotate_ident Option.bind] in Hst; break_innermost_match_hyps; inversion_option; subst;
          cbv [ident.gen_interp ident.cast abstraction_relation' ZRange.type.base.option.is_bounded_by ZRange.type.base.is_bounded_by is_bounded_by_bool];
          intros; destruct_head'_prod; cbn [fst snd] in *;
            break_innermost_match; Bool.split_andb; try congruence; reflexivity.
      Qed.

      Lemma interp_annotate_ident_Proper {t} st1 st2 (Hst : abstract_domain'_R t st1 st2)
        : @annotate_ident t st1 = @annotate_ident t st2.
      Proof. congruence. Qed.

      Lemma bottom'_bottom {t} : forall v, abstraction_relation' (bottom' t) v.
      Proof.
        cbv [abstraction_relation' bottom']; induction t; cbn; intros; break_innermost_match; cbn; try reflexivity.
        rewrite Bool.andb_true_iff; split; auto.
      Qed.

      Lemma invert_is_annotation t idc
        : is_annotation t idc = true
          -> (exists r, existT _ t idc = existT _ (base.type.Z -> base.type.Z)%etype (ident.Z_cast r))
            \/ (exists r, existT _ t idc = existT _ (base.type.Z * base.type.Z -> base.type.Z * base.type.Z)%etype (ident.Z_cast2 r)).
      Proof. destruct idc; cbn [is_annotation]; try discriminate; eauto. Qed.

      Lemma abstract_interp_ident_related cast_outside_of_range {t} (idc : ident t)
        : type.related_hetero (@abstraction_relation') (@abstract_interp_ident t idc) (@ident.gen_interp cast_outside_of_range _ idc).
      Proof. apply ZRange.ident.option.interp_related. Qed.

      Lemma interp_update_literal_with_state {t : base.type.base} st v
        : @abstraction_relation' t st v -> @update_literal_with_state t st v = v.
      Proof.
        cbv [abstraction_relation' update_literal_with_state update_Z_literal_with_state ZRange.type.base.option.is_bounded_by];
          break_innermost_match; try congruence; reflexivity.
      Qed.

      Lemma extract_list_state_related {t} st v ls
        : @abstraction_relation' _ st v
          -> @extract_list_state t st = Some ls
          -> length ls = length v
            /\ forall st' (v' : base.interp t), List.In (st', v') (List.combine ls v) -> @abstraction_relation' t st' v'.
      Proof.
        cbv [abstraction_relation' extract_list_state]; cbn [ZRange.type.base.option.is_bounded_by].
        intros; subst.
        split.
        { eapply FoldBool.fold_andb_map_length; eassumption. }
        { intros *.
          revert dependent v; induction ls, v; cbn; try tauto.
          rewrite Bool.andb_true_iff.
          intros; destruct_head'_and; destruct_head'_or; inversion_prod; subst; eauto. }
      Qed.

      Lemma Extract_FromFlat_ToFlat' {t} (e : Expr t) (Hwf : Wf e) b_in1 b_in2
            (Hb : type.and_for_each_lhs_of_arrow (fun t => type.eqv) b_in1 b_in2)
        : partial.Extract (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e)) b_in1
          = partial.Extract e b_in2.
      Proof.
        cbv [partial.Extract partial.ident.extract partial.extract_gen partial.extract'].
        revert b_in1 b_in2 Hb.
        rewrite <- (@type.related_iff_app_curried base.type ZRange.type.base.option.interp (fun _ => eq)).
        apply GeneralizeVar.Interp_gen1_FromFlat_ToFlat, Hwf.
      Qed.

      Lemma Extract_FromFlat_ToFlat {t} (e : Expr t) (Hwf : Wf e) b_in
            (Hb : Proper (type.and_for_each_lhs_of_arrow (fun t => type.eqv)) b_in)
        : partial.Extract (GeneralizeVar.FromFlat (GeneralizeVar.ToFlat e)) b_in
          = partial.Extract e b_in.
      Proof. apply Extract_FromFlat_ToFlat'; assumption. Qed.

      (*    Definition eval {var} {t} (e : @expr _ t) : expr t
        := (@partial.ident.eval)
             var abstract_domain' annotate_ident bottom' abstract_interp_ident update_literal_with_state extract_list_state is_annotation t e.
      Definition Eval {t} (e : Expr t) : Expr t
        := fun var => eval (e _).
      Definition Extract {t} (e : Expr t) (bound : type.for_each_lhs_of_arrow abstract_domain t) : abstract_domain' (type.final_codomain t)
        := @partial.ident.extract abstract_domain' abstract_interp_ident t (e _) bound.
       *)

      Local Hint Resolve interp_annotate_ident interp_update_literal_with_state abstract_interp_ident_related.

      Lemma interp_eval_with_bound
            cast_outside_of_range
            {t} (e_st e1 e2 : expr t)
            (Hwf : expr.wf3 nil e_st e1 e2)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
              type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) (eval_with_bound e1 st)) arg1
              = type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) e2) arg2)
          /\ (forall arg1
                     (Harg11 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg1)
                     (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                 abstraction_relation'
                   (extract e_st st)
                   (type.app_curried (expr.interp (@ident.gen_interp cast_outside_of_range) (eval_with_bound e1 st)) arg1)).
      Proof using Type.
        cbv [eval_with_bound]; split;
          [ intros arg1 arg2 Harg12 Harg1
          | intros arg1 Harg11 Harg1 ].
        all: eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1; [ | apply ZRange.type.option.is_bounded_by_impl_related_hetero ].
        all: eapply ident.interp_eval_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom with typeclass_instances.
        all: intros; eapply extract_list_state_related; eassumption.
      Qed.

      Lemma interp_eta_expand_with_bound
            {t} (e1 e2 : expr t)
            (Hwf : expr.wf nil e1 e2)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (interp (partial.eta_expand_with_bound e1 b_in)) arg1 = type.app_curried (interp e2) arg2.
      Proof.
        cbv [partial.eta_expand_with_bound]; intros arg1 arg2 Harg12 Harg1.
        eapply Compilers.type.andb_bool_impl_and_for_each_lhs_of_arrow in Harg1.
        { apply ident.interp_eta_expand_with_bound with (abstraction_relation':=@abstraction_relation') (abstract_domain'_R:=fun t => abstract_domain'_R t); eauto using bottom'_bottom with typeclass_instances.
          all: intros; eapply extract_list_state_related; eassumption. }
        { apply ZRange.type.option.is_bounded_by_impl_related_hetero. }
      Qed.

      Lemma Interp_EvalWithBound
            cast_outside_of_range
            {t} (e : Expr t)
            (Hwf : expr.Wf3 e)
            (st : type.for_each_lhs_of_arrow abstract_domain t)
        : (forall arg1 arg2
                  (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                  (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
              type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (EvalWithBound e st)) arg1
              = type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) e) arg2)
          /\ (forall arg1
                     (Harg11 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg1)
                     (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) st arg1 = true),
                 abstraction_relation'
                   (Extract e st)
                   (type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (EvalWithBound e st)) arg1)).
      Proof using Type. cbv [Extract EvalWithBound]; apply interp_eval_with_bound, Hwf. Qed.

      Lemma Interp_EtaExpandWithBound
            {t} (E : Expr t)
            (Hwf : Wf E)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (Interp (partial.EtaExpandWithBound E b_in)) arg1 = type.app_curried (Interp E) arg2.
      Proof. cbv [partial.EtaExpandWithBound]; apply interp_eta_expand_with_bound, Hwf. Qed.

      Lemma strip_ranges_is_looser t b v
        : @ZRange.type.option.is_bounded_by t b v = true
          -> ZRange.type.option.is_bounded_by (ZRange.type.option.strip_ranges b) v = true.
      Proof.
        induction t as [t|s IHs d IHd]; cbn in *; [ | tauto ].
        induction t; cbn in *; break_innermost_match; cbn in *; rewrite ?Bool.andb_true_iff; try solve [ intuition ]; [].
        repeat match goal with ls : list _ |- _ => revert ls end.
        intros ls1 ls2; revert ls2.
        induction ls1, ls2; cbn in *; rewrite ?Bool.andb_true_iff; solve [ intuition ].
      Qed.

      Lemma andb_strip_ranges_Proper t (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t) arg1
        : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true ->
          type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by)
                                               (type.map_for_each_lhs_of_arrow (@ZRange.type.option.strip_ranges) b_in) arg1 = true.
      Proof.
        induction t as [t|s IHs d IHd]; cbn [type.andb_bool_for_each_lhs_of_arrow type.map_for_each_lhs_of_arrow type.for_each_lhs_of_arrow] in *;
          rewrite ?Bool.andb_true_iff; [ tauto | ].
        destruct_head'_prod; cbn [fst snd]; intros [? ?].
        erewrite IHd by eauto.
        split; [ | reflexivity ].
        apply strip_ranges_is_looser; assumption.
      Qed.

      Lemma Interp_EtaExpandWithListInfoFromBound
            {t} (E : Expr t)
            (Hwf : Wf E)
            (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        : forall arg1 arg2
                 (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
                 (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          type.app_curried (Interp (partial.EtaExpandWithListInfoFromBound E b_in)) arg1 = type.app_curried (Interp E) arg2.
      Proof.
        cbv [partial.EtaExpandWithListInfoFromBound].
        intros; apply Interp_EtaExpandWithBound; trivial.
        apply andb_strip_ranges_Proper; assumption.
      Qed.
    End specialized.
  End partial.
  Import defaults.

  Module Import CheckCasts.
    Module ident.
      Lemma interp_eqv_without_casts t idc
            cast_outside_of_range1 cast_outside_of_range2
            (Hc : partial.is_annotation t idc = false)
      : ident.gen_interp cast_outside_of_range1 idc
        == ident.gen_interp cast_outside_of_range2 idc.
      Proof.
        generalize (@ident.gen_interp_Proper cast_outside_of_range1 t idc idc eq_refl);
          destruct idc; try exact id; cbn in Hc; discriminate.
      Qed.
    End ident.

    Lemma interp_eqv_without_casts
          cast_outside_of_range1 cast_outside_of_range2
          G {t} e1 e2 e3
          (HG : forall t v1 v2 v3, List.In (existT _ t (v1, v2, v3)) G -> v2 == v3)
          (Hwf : expr.wf3 G e1 e2 e3)
          (Hc : @CheckCasts.get_casts t e1 = nil)
    : expr.interp (@ident.gen_interp cast_outside_of_range1) e2
      == expr.interp (@ident.gen_interp cast_outside_of_range2) e3.
    Proof.
      induction Hwf;
        repeat first [ progress cbn [CheckCasts.get_casts] in *
                     | discriminate
                     | match goal with
                       | [ H : (_ ++ _)%list = nil |- _ ] => apply List.app_eq_nil in H
                       end
                     | progress destruct_head'_and
                     | progress break_innermost_match_hyps
                     | progress interp_safe_t
                     | solve [ eauto using ident.interp_eqv_without_casts ] ].
    Qed.

    Lemma Interp_WithoutUnsupportedCasts {t} (e : Expr t)
          (Hc : CheckCasts.GetUnsupportedCasts e = nil)
          (Hwf : expr.Wf3 e)
          cast_outside_of_range1 cast_outside_of_range2
      : expr.Interp (@ident.gen_interp cast_outside_of_range1) e
        == expr.Interp (@ident.gen_interp cast_outside_of_range2) e.
    Proof. eapply interp_eqv_without_casts with (G:=nil); wf_safe_t. Qed.
  End CheckCasts.

  Module RelaxZRange.
    Definition relaxed_cast_outside_of_range
               (relax_zrange : zrange -> option zrange)
               (cast_outside_of_range : zrange -> Z -> Z)
    : zrange -> Z -> Z
      := fun r v
         => match relax_zrange r with
            | Some r' => ident.cast cast_outside_of_range r' v
            | None => cast_outside_of_range r v
            end.

    Module ident.
      Section relax.
        Context (relax_zrange : zrange -> option zrange)
                (cast_outside_of_range : zrange -> Z -> Z)
                (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                         -> relax_zrange r = Some r'
                                         -> is_tighter_than_bool z r' = true).

        Local Notation relaxed_cast_outside_of_range := (@relaxed_cast_outside_of_range relax_zrange cast_outside_of_range).

        Lemma interp_relax {t} (idc : ident t)
          : ident.gen_interp cast_outside_of_range (@RelaxZRange.ident.relax relax_zrange t idc)
            == ident.gen_interp relaxed_cast_outside_of_range idc.
        Proof.
          pose proof (@ident.gen_interp_Proper cast_outside_of_range t idc idc eq_refl) as Hp.
          destruct idc; cbn [type.related] in *; repeat (let x := fresh "x" in intro x; specialize (Hp x));
            repeat first [ assumption
                         | reflexivity
                         | discriminate
                         | congruence
                         | progress subst
                         | progress cbv [relaxed_cast_outside_of_range RelaxZRange.ident.relax Option.bind ident.cast respectful is_tighter_than_bool id] in *
                         | progress cbn [ident.gen_interp type.related type.interp base.interp upper lower] in *
                         | progress destruct_head'_prod
                         | progress specialize_by (exact eq_refl)
                         | break_match_step ltac:(fun x => let h := head x in constr_eq h relax_zrange)
                         | match goal with
                           | [ H : relax_zrange ?r = Some ?r' |- context[Z.leb (lower ?r) ?v] ]
                             => pose proof (fun pf => Hrelax _ _ (Build_zrange v v) pf H); clear H
                           end
                         | break_innermost_match_step ].
        Qed.
      End relax.
    End ident.

    Module expr.
      Section relax.
        Context (relax_zrange : zrange -> option zrange)
                (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                         -> relax_zrange r = Some r'
                                         -> is_tighter_than_bool z r' = true)
                (cast_outside_of_range : zrange -> Z -> Z).

        Local Notation relaxed_cast_outside_of_range := (@relaxed_cast_outside_of_range relax_zrange cast_outside_of_range).

        Lemma interp_relax G {t} (e1 e2 : expr t)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> v1 == v2)
              (Hwf : expr.wf G e1 e2)
          : expr.interp (@ident.gen_interp cast_outside_of_range) (RelaxZRange.expr.relax relax_zrange e1)
            == expr.interp (@ident.gen_interp relaxed_cast_outside_of_range) e2.
        Proof.
          induction Hwf; cbn -[RelaxZRange.ident.relax] in *; interp_safe_t; cbv [option_map] in *;
            break_innermost_match; cbn -[RelaxZRange.ident.relax] in *; interp_safe_t;
              eauto using tt, @ident.interp_relax.
        Qed.

        Lemma Interp_Relax {t} (e : Expr t)
              (Hwf : Wf e)
          : expr.Interp (@ident.gen_interp cast_outside_of_range) (RelaxZRange.expr.Relax relax_zrange e)
            == expr.Interp (@ident.gen_interp relaxed_cast_outside_of_range) e.
        Proof. apply interp_relax with (G:=nil); wf_safe_t. Qed.
      End relax.
    End expr.
  End RelaxZRange.
  Hint Resolve RelaxZRange.expr.Wf_Relax : wf.

  Lemma Interp_PartialEvaluateWithBounds
        cast_outside_of_range
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (PartialEvaluateWithBounds E b_in)) arg1
      = type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) E) arg2.
  Proof.
    cbv [PartialEvaluateWithBounds].
    intros arg1 arg2 Harg12 Harg1.
    assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
      by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
    assert (arg2_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg2)
      by (hnf; etransitivity; [ symmetry; eassumption | eassumption ]).
    rewrite <- (@GeneralizeVar.Interp_gen1_GeneralizeVar _ _ _ _ _ E) by auto with wf.
    eapply Interp_EvalWithBound; eauto with wf.
  Qed.

  Lemma Interp_PartialEvaluateWithBounds_bounded
        cast_outside_of_range
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
        {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R _ _ (fun _ => eq))) b_in}
    : forall arg1
             (Harg11 : Proper (type.and_for_each_lhs_of_arrow (@type.eqv)) arg1)
             (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      ZRange.type.base.option.is_bounded_by
        (partial.Extract E b_in)
        (type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) (PartialEvaluateWithBounds E b_in)) arg1)
      = true.
  Proof.
    cbv [PartialEvaluateWithBounds].
    intros arg1 Harg1.
    rewrite <- Extract_FromFlat_ToFlat by auto with wf.
    eapply Interp_EvalWithBound; eauto with wf.
  Qed.

  Lemma Interp_PartialEvaluateWithListInfoFromBounds
        {t} (E : Expr t)
        (Hwf : Wf E)
        (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
    : forall arg1 arg2
        (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
        (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
      type.app_curried (Interp (PartialEvaluateWithListInfoFromBounds E b_in)) arg1 = type.app_curried (Interp E) arg2.
  Proof.
    cbv [PartialEvaluateWithListInfoFromBounds]; intros arg1 arg2 Harg12 Harg1.
    assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
        by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
    assert (arg2_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg2)
        by (hnf; etransitivity; [ symmetry; eassumption | eassumption ]).
    rewrite <- (@GeneralizeVar.Interp_GeneralizeVar _ E) by auto.
    apply Interp_EtaExpandWithListInfoFromBound; auto with wf.
  Qed.

  Theorem CheckedPartialEvaluateWithBounds_Correct
          (relax_zrange : zrange -> option zrange)
          (Hrelax : forall r r' z, is_tighter_than_bool z r = true
                                   -> relax_zrange r = Some r'
                                   -> is_tighter_than_bool z r' = true)
          {t} (E : Expr t)
          (Hwf : Wf E)
          (b_in : type.for_each_lhs_of_arrow ZRange.type.option.interp t)
          (b_out : ZRange.type.base.option.interp (type.final_codomain t))
          {b_in_Proper : Proper (type.and_for_each_lhs_of_arrow (@abstract_domain_R _ _ (fun _ => eq))) b_in}
          rv (Hrv : CheckedPartialEvaluateWithBounds relax_zrange E b_in b_out = inl rv)
    : (forall arg1 arg2
              (Harg12 : type.and_for_each_lhs_of_arrow (@type.eqv) arg1 arg2)
              (Harg1 : type.andb_bool_for_each_lhs_of_arrow (@ZRange.type.option.is_bounded_by) b_in arg1 = true),
          ZRange.type.base.option.is_bounded_by b_out (type.app_curried (Interp rv) arg1) = true
          /\ forall cast_outside_of_range, type.app_curried (expr.Interp (@ident.gen_interp cast_outside_of_range) rv) arg1
                                           = type.app_curried (Interp E) arg2)
      /\ Wf rv.
  Proof.
    cbv [CheckedPartialEvaluateWithBounds Let_In] in *;
      break_innermost_match_hyps; inversion_sum; subst.
    let H := lazymatch goal with H : _ = nil |- _ => H end in
    pose proof (@Interp_WithoutUnsupportedCasts _ _ H ltac:(solve [ auto with wf ])) as H'; clear H;
      assert (forall cast_outside_of_range1 cast_outside_of_range2,
                 expr.Interp (@ident.gen_interp cast_outside_of_range1) E == expr.Interp (@ident.gen_interp cast_outside_of_range2) E)
      by (intros c1 c2; specialize (H' c1 c2);
          rewrite !@GeneralizeVar.Interp_gen1_FromFlat_ToFlat in H' by eauto with wf typeclass_instances;
          assumption).
    clear H'.
    split.
    { intros arg1 arg2 Harg12 Harg1.
      assert (arg1_Proper : Proper (type.and_for_each_lhs_of_arrow (@type.related base.type base.interp (fun _ => eq))) arg1)
        by (hnf; etransitivity; [ eassumption | symmetry; eassumption ]).
      split.
      all: repeat first [ rewrite !@GeneralizeVar.Interp_gen1_FromFlat_ToFlat by eauto with wf typeclass_instances
                        | rewrite <- Extract_FromFlat_ToFlat by auto; apply Interp_PartialEvaluateWithBounds_bounded; auto
                        | rewrite Extract_FromFlat_ToFlat by auto with wf
                        | progress intros
                        | progress cbv [ident.interp]
                        | rewrite RelaxZRange.expr.Interp_Relax; eauto
                        | eapply ZRange.type.base.option.is_tighter_than_is_bounded_by; [ eassumption | ]
                        | solve [ eauto with wf ]
                        | erewrite !Interp_PartialEvaluateWithBounds
                        | apply type.app_curried_Proper
                        | apply expr.Wf_Interp_Proper_gen
                        | progress intros ]. }
    { auto with wf. }
  Qed.
End Compilers.
