Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Language.
Require Import Crypto.LanguageInversion.
Require Import Crypto.LanguageWf.
Require Import Crypto.UnderLetsProofs.
Require Import Crypto.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Rewriter.
Require Import Crypto.RewriterWf1.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.ForallIn.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import GENERATEDIdentifiersWithoutTypesProofs.Compilers.
  Import Rewriter.Compilers.
  Import RewriterWf1.Compilers.
  Import expr.Notations.
  Import RewriterWf1.Compilers.RewriteRules.
  Import defaults.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    Lemma nbe_rewrite_head_eq : @nbe_rewrite_head = @nbe_rewrite_head0.
    Proof. reflexivity. Qed.

    Lemma fancy_rewrite_head_eq
      : (fun var do_again => @fancy_rewrite_head var)
        = @fancy_rewrite_head0.
    Proof. reflexivity. Qed.

    Lemma arith_rewrite_head_eq max_const_val : (fun var do_again => @arith_rewrite_head max_const_val var) = (fun var => @arith_rewrite_head0 var max_const_val).
    Proof. reflexivity. Qed.

    Lemma fancy_with_casts_rewrite_head_eq invert_low invert_high value_range flag_range
      : (fun var do_again => @fancy_with_casts_rewrite_head invert_low invert_high value_range flag_range var)
        = (fun var => @fancy_with_casts_rewrite_head0 var invert_low invert_high value_range flag_range).
    Proof. reflexivity. Qed.

    Lemma arith_with_casts_rewrite_head_eq : @arith_with_casts_rewrite_head = @arith_with_casts_rewrite_head0.
    Proof. reflexivity. Qed.

    Lemma strip_literal_casts_rewrite_head_eq : (fun var do_again => @strip_literal_casts_rewrite_head var) = @strip_literal_casts_rewrite_head0.
    Proof. reflexivity. Qed.

    Lemma nbe_all_rewrite_rules_eq : @nbe_all_rewrite_rules = @nbe_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma fancy_all_rewrite_rules_eq : @fancy_all_rewrite_rules = @fancy_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma arith_all_rewrite_rules_eq : @arith_all_rewrite_rules = @arith_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma fancy_with_casts_all_rewrite_rules_eq : @fancy_with_casts_all_rewrite_rules = @fancy_with_casts_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma arith_with_casts_all_rewrite_rules_eq : @arith_with_casts_all_rewrite_rules = @arith_with_casts_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma strip_literal_casts_all_rewrite_rules_eq : @strip_literal_casts_all_rewrite_rules = @strip_literal_casts_rewrite_rules.
    Proof. reflexivity. Qed.

    Section good.
      Context {var1 var2 : type -> Type}.

      Local Notation rewrite_rules_goodT := (@Compile.rewrite_rules_goodT ident pattern.ident (@pattern.ident.arg_types) var1 var2).

      Lemma wf_rlist_rect_gen
            {ivar1 ivar2 A P}
            Q
            N1 N2 C1 C2 ls1 ls2 G
            (Hwf : expr.wf G ls1 ls2)
            (HN : UnderLets.wf Q G N1 N2)
            (HC : forall G' x xs y ys rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> expr.wf G x y
                -> expr.wf G (reify_list xs) (reify_list ys)
                -> Q G' rec1 rec2
                -> UnderLets.wf Q G' (C1 x xs rec1) (C2 y ys rec2))
        : option_eq (UnderLets.wf Q G)
                    (@rlist_rect var1 A P ivar1 N1 C1 ls1)
                    (@rlist_rect var2 A P ivar2 N2 C2 ls2).
      Proof using Type.
        cbv [rlist_rect].
        cbv [Compile.option_bind' Option.bind].
        break_innermost_match.
        all: repeat first [ match goal with
                            | [ H : invert_expr.reflect_list ?v = Some _, H' : invert_expr.reflect_list ?v' = None |- _ ]
                              => first [ erewrite <- expr.wf_reflect_list in H' by eassumption
                                      | erewrite -> expr.wf_reflect_list in H' by eassumption ];
                                exfalso; clear -H H'; congruence
                            | [ |- UnderLets.wf _ _ _ _ ] => constructor
                            end
                          | progress expr.invert_subst
                          | progress cbn [sequence_return option_eq]
                          | assumption
                          | reflexivity
                          | apply @UnderLets.wf_splice with (P:=fun G' => expr.wf G')
                          | progress intros ].
        lazymatch goal with
        | [ H : expr.wf _ (reify_list ?l) (reify_list ?l') |- _ ]
          => revert dependent l'; intro l2; revert dependent l; intro l1
        end.
        revert l2; induction l1 as [|l1 ls1 IHls1], l2; cbn [list_rect];
          rewrite ?expr.reify_list_cons, ?expr.reify_list_nil;
          intros; expr.inversion_wf_constr; [ assumption | ].
        all: repeat first [ match goal with
                            | [ H : invert_expr.reflect_list ?v = Some _, H' : invert_expr.reflect_list ?v' = None |- _ ]
                              => first [ erewrite <- expr.wf_reflect_list in H' by eassumption
                                      | erewrite -> expr.wf_reflect_list in H' by eassumption ];
                                exfalso; clear -H H'; congruence
                            | [ |- UnderLets.wf _ _ _ _ ] => constructor
                            end
                          | progress expr.invert_subst
                          | progress cbn [sequence_return option_eq]
                          | assumption
                          | reflexivity
                          | solve [ auto ]
                          | progress subst
                          | apply @UnderLets.wf_splice with (P:=Q)
                          | progress intros
                          | wf_safe_t_step
                          | progress type.inversion_type
                          | progress expr.inversion_wf_constr ].
      Qed.
      Lemma wf_rlist_rect {A P}
            N1 N2 C1 C2 ls1 ls2 G
            (Hwf : expr.wf G ls1 ls2)
            (HN : UnderLets.wf (fun G' => expr.wf G') G N1 N2)
            (HC : forall G' x xs y ys rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> expr.wf G x y
                -> expr.wf G (reify_list xs) (reify_list ys)
                -> expr.wf G' rec1 rec2
                -> UnderLets.wf (fun G'' => expr.wf G'') G' (C1 x xs rec1) (C2 y ys rec2))
        : option_eq (UnderLets.wf (fun G' => expr.wf G') G)
                    (@rlist_rect var1 A P var1 N1 C1 ls1)
                    (@rlist_rect var2 A P var2 N2 C2 ls2).
      Proof using Type. apply wf_rlist_rect_gen; assumption. Qed.
      Lemma wf_rlist_rectv {A P}
            N1 N2 C1 C2 ls1 ls2 G
            (Hwf : expr.wf G ls1 ls2)
            (HN : UnderLets.wf (fun G' v1 v2
                                => exists G'',
                                    (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                                    /\ expr.wf G'' v1 v2) G N1 N2)
            (HC : forall G' x xs y ys rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> expr.wf G x y
                -> expr.wf G (reify_list xs) (reify_list ys)
                -> (exists G'', (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                                /\ expr.wf G'' rec1 rec2)
                -> UnderLets.wf (fun G' v1 v2
                                 => exists G'',
                                     (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                                     /\ expr.wf G'' v1 v2)
                                G' (C1 x xs rec1) (C2 y ys rec2))
        : option_eq (UnderLets.wf
                       (fun G' v1 v2
                        => exists G'',
                            (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                            /\ expr.wf G'' v1 v2)
                       G)
                    (@rlist_rect var1 A P (@Compile.value _ ident var1) N1 C1 ls1)
                    (@rlist_rect var2 A P (@Compile.value _ ident var2) N2 C2 ls2).
      Proof using Type. apply wf_rlist_rect_gen; assumption. Qed.

      Lemma wf_list_rect {T A}
            G N1 N2 C1 C2 ls1 ls2
            (HN : Compile.wf_value G N1 N2)
            (HC : forall G' x1 x2 xs1 xs2 rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> Compile.wf_value G x1 x2
                -> List.Forall2 (Compile.wf_value G) xs1 xs2
                -> Compile.wf_value G' rec1 rec2
                -> Compile.wf_value G' (C1 x1 xs1 rec1) (C2 x2 xs2 rec2))
            (Hls : List.Forall2 (Compile.wf_value G) ls1 ls2)
        : Compile.wf_value
            G
            (list_rect (fun _ : list (@Compile.value base.type ident var1 (type.base T))
                        => @Compile.value base.type ident var1 A)
                       N1 C1 ls1)
            (list_rect (fun _ : list (@Compile.value base.type ident var2 (type.base T))
                        => @Compile.value base.type ident var2 A)
                       N2 C2 ls2).
      Proof. induction Hls; cbn [list_rect]; try eapply HC; eauto using (ex_intro _ nil). Qed.

      Lemma wf_nat_rect {A}
            G O1 O2 S1 S2 n
            (HO : Compile.wf_value_with_lets G O1 O2)
            (HS : forall G' n rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> Compile.wf_value_with_lets G' rec1 rec2
                -> Compile.wf_value_with_lets G' (S1 n rec1) (S2 n rec2))
        : Compile.wf_value_with_lets
            G
            (nat_rect (fun _ => @Compile.value_with_lets base.type ident var1 A) O1 S1 n)
            (nat_rect (fun _ => @Compile.value_with_lets base.type ident var2 A) O2 S2 n).
      Proof. induction n; cbn [nat_rect]; try eapply HS; eauto using (ex_intro _ nil). Qed.

      Local Ltac start_good :=
        apply Compile.rewrite_rules_goodT_by_curried;
        split; [ reflexivity | ];
        lazymatch goal with
        | [ |- forall x p x' p', In (@existT ?A ?P x p, @existT ?A' ?P' x' p') ?ls -> @?Q x x' p p' ]
          => apply (@forall_In_pair_existT A A' P P' Q ls); cbn [projT1 projT2 fst snd]; cbv [id]
        end;
        (exists eq_refl);
        cbn [eq_rect];
        cbv [Compile.wf_deep_rewrite_ruleTP_gen Compile.wf_rewrite_rule_data_curried Compile.rew_replacement Compile.rew_should_do_again Compile.rew_with_opt Compile.rew_under_lets Compile.wf_with_unif_rewrite_ruleTP_gen_curried Compile.wf_with_unification_resultT pattern.pattern_of_anypattern pattern.type_of_anypattern Compile.wf_maybe_under_lets_expr Compile.wf_maybe_do_again_expr Compile.wf_with_unification_resultT pattern.type.under_forall_vars_relation Compile.with_unification_resultT' pattern.collect_vars pattern.type.collect_vars pattern.base.collect_vars PositiveSet.empty PositiveSet.elements Compile.under_type_of_list_relation_cps pattern.ident.arg_types pattern.type.subst_default pattern.base.subst_default pattern.base.lookup_default PositiveSet.rev PositiveMap.empty Compile.under_with_unification_resultT_relation_hetero Compile.under_with_unification_resultT'_relation_hetero Compile.maybe_option_eq];
        cbn [List.map List.fold_right PositiveSet.union PositiveSet.xelements List.rev List.app projT1 projT2 list_rect PositiveSet.add PositiveSet.rev PositiveSet.rev_append PositiveMap.add PositiveMap.find orb];
        repeat first [ progress intros
                     | match goal with
                       | [ |- { pf : ?x = ?x | _ } ] => (exists eq_refl)
                       end
                     | progress cbn [eq_rect] in * ].

      Local Ltac fin_wf :=
        repeat first [ progress intros
                     | match goal with
                       | [ |- expr.wf _ (_ @ _) (_ @ _) ] => constructor
                       | [ |- expr.wf _ (#_) (#_) ] => constructor
                       | [ |- expr.wf _ ($_) ($_) ] => constructor
                       | [ |- expr.wf _ (expr.Abs _) (expr.Abs _) ] => constructor; intros
                       | [ H : @List.In ?T _ ?ls |- _ ] => is_evar ls; unify ls (@nil T); cbn [List.In] in H
                       | [ |- List.In ?v ?ls ] => is_evar ls; instantiate (1:=cons v _)
                       end
                     | progress subst
                     | progress destruct_head'_or
                     | progress destruct_head'_False
                     | progress inversion_sigma
                     | progress inversion_prod
                     | assumption
                     | esplit; revgoals; solve [ fin_wf ]
                     | econstructor; solve [ fin_wf ]
                     | progress cbn [List.In fst snd eq_rect] in * ].

      Local Ltac handle_reified_rewrite_rules :=
        repeat
          first [ match goal with
                  | [ |- option_eq _ ?x ?y ]
                    => lazymatch x with Some _ => idtac | None => idtac end;
                       lazymatch y with Some _ => idtac | None => idtac end;
                       progress cbn [option_eq]
                  | [ |- UnderLets.wf _ _ (Reify.expr_value_to_rewrite_rule_replacement ?rii1 ?sda _) (Reify.expr_value_to_rewrite_rule_replacement ?rii2 ?sda _) ]
                    => apply (fun H => @Reify.wf_expr_value_to_rewrite_rule_replacement _ _ _ rii1 rii2 H sda); intros
                  | [ |- option_eq _ (Compile.reflect_ident_iota _) (Compile.reflect_ident_iota _) ]
                    => apply Reify.wf_reflect_ident_iota
                  | [ |- ?x = ?x ] => reflexivity
                  end
                | break_innermost_match_step
                | progress cbv [Compile.wf_maybe_do_again_expr] in *
                | progress fin_wf ].

      Local Ltac handle_extra_nbe :=
        repeat first [ match goal with
                       | [ |- expr.wf _ (reify_list _) (reify_list _) ] => rewrite expr.wf_reify_list
                       | [ |- List.Forall2 _ ?x ?x ] => rewrite Forall2_Forall; cbv [Proper]
                       | [ |- List.Forall2 _ (List.map _ _) (List.map _ _) ] => rewrite Forall2_map_map_iff
                       | [ |- List.Forall _ (seq _ _) ] => rewrite Forall_seq
                       end
                     | progress intros
                     | progress fin_wf ].

      Lemma nbe_rewrite_rules_good
        : rewrite_rules_goodT nbe_rewrite_rules nbe_rewrite_rules.
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules; handle_extra_nbe.
      Qed.

      Local Ltac handle_extra_arith_rules :=
        repeat first [ progress cbv [rwhenl option_eq SubstVarLike.is_var_fst_snd_pair_opp_cast]
                     | break_innermost_match_step
                     | match goal with
                       | [ Hwf : Compile.wf_value _ ?x _, H : context[SubstVarLike.is_recursively_var_or_ident _ ?x] |- _ ] => erewrite SubstVarLike.wfT_is_recursively_var_or_ident in H by exact Hwf
                       end
                     | congruence
                     | progress fin_wf ].

      Lemma arith_rewrite_rules_good max_const
        : rewrite_rules_goodT (arith_rewrite_rules max_const) (arith_rewrite_rules max_const).
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules; handle_extra_arith_rules.
      Qed.

      Lemma arith_with_casts_rewrite_rules_good
        : rewrite_rules_goodT arith_with_casts_rewrite_rules arith_with_casts_rewrite_rules.
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Qed.

      Lemma strip_literal_casts_rewrite_rules_good
        : rewrite_rules_goodT strip_literal_casts_rewrite_rules strip_literal_casts_rewrite_rules.
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Qed.

      Lemma fancy_rewrite_rules_good
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_goodT fancy_rewrite_rules fancy_rewrite_rules.
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Qed.

      Lemma fancy_with_casts_rewrite_rules_good
            (invert_low invert_high : Z -> Z -> option Z)
            (value_range flag_range : ZRange.zrange)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_goodT (fancy_with_casts_rewrite_rules invert_low invert_high value_range flag_range) (fancy_with_casts_rewrite_rules invert_low invert_high value_range flag_range).
      Proof using Type.
        Time start_good.
        Time all: handle_reified_rewrite_rules.
      Qed.
    End good.
  End RewriteRules.
End Compilers.
