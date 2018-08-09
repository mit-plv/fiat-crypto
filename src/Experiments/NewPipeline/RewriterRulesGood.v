Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Experiments.NewPipeline.Language.
Require Import Crypto.Experiments.NewPipeline.LanguageInversion.
Require Import Crypto.Experiments.NewPipeline.LanguageWf.
Require Import Crypto.Experiments.NewPipeline.UnderLetsProofs.
Require Import Crypto.Experiments.NewPipeline.GENERATEDIdentifiersWithoutTypesProofs.
Require Import Crypto.Experiments.NewPipeline.Rewriter.
Require Import Crypto.Experiments.NewPipeline.RewriterWf1.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Import ListNotations. Local Open Scope list_scope.
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

    Lemma fancy_rewrite_head_eq invert_low invert_high
      : (fun var do_again => @fancy_rewrite_head invert_low invert_high var)
        = (fun var => @fancy_rewrite_head0 var invert_low invert_high).
    Proof. reflexivity. Qed.

    Lemma arith_rewrite_head_eq max_const_val : @arith_rewrite_head max_const_val = (fun var => @arith_rewrite_head0 var max_const_val).
    Proof. reflexivity. Qed.

    Lemma nbe_all_rewrite_rules_eq : @nbe_all_rewrite_rules = @nbe_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma fancy_all_rewrite_rules_eq : @fancy_all_rewrite_rules = @fancy_rewrite_rules.
    Proof. reflexivity. Qed.

    Lemma arith_all_rewrite_rules_eq : @arith_all_rewrite_rules = @arith_rewrite_rules.
    Proof. reflexivity. Qed.

    Section good.
      Context {var1 var2 : type -> Type}.

      Local Notation rewrite_rules_goodT := (@Compile.rewrite_rules_goodT ident pattern.ident pattern.ident.arg_types var1 var2).

      Lemma rlist_rect_cps_id {var} A P {ivar} N_case C_case ls T k
        : @rlist_rect var A P ivar N_case C_case ls T k = k (@rlist_rect var A P ivar N_case C_case ls _ id).
      Proof.
        cbv [rlist_rect id Compile.option_bind']; rewrite !expr.reflect_list_cps_id.
        destruct (invert_expr.reflect_list ls) eqn:?; cbn [Option.bind Option.sequence_return]; reflexivity.
      Qed.
      Lemma rlist_rect_cast_cps_id {var} A A' P {ivar} N_case C_case ls T k
        : @rlist_rect_cast var A A' P ivar N_case C_case ls T k = k (@rlist_rect_cast var A A' P ivar N_case C_case ls _ id).
      Proof.
        cbv [rlist_rect_cast Compile.castbe Compile.castb id Compile.option_bind']; rewrite_type_transport_correct;
          break_innermost_match; type_beq_to_eq; subst; cbn [eq_rect Option.bind Option.sequence_return]; [ | reflexivity ].
        apply rlist_rect_cps_id.
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
        : option_eq (UnderLets.wf (fun G' => Compile.wf_anyexpr G' (type.base P)) G)
                    (@rlist_rect var1 A P var1 N1 C1 ls1 _ id)
                    (@rlist_rect var2 A P var2 N2 C2 ls2 _ id).
      Proof.
        cbv [rlist_rect].
        rewrite !expr.reflect_list_cps_id; cbv [id].
        cbv [Compile.option_bind' Option.bind].
        break_innermost_match.
        all: repeat first [ match goal with
                            | [ H : invert_expr.reflect_list ?v = Some _, H' : invert_expr.reflect_list ?v' = None |- _ ]
                              => first [ erewrite <- expr.wf_reflect_list in H' by eassumption
                                      | erewrite -> expr.wf_reflect_list in H' by eassumption ];
                                exfalso; clear -H H'; congruence
                            | [ |- UnderLets.wf _ _ _ _ ] => constructor
                            | [ |- Compile.wf_anyexpr _ _ _ _ ] => constructor
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
                          | apply @UnderLets.wf_splice with (P:=fun G' => expr.wf G')
                          | progress intros
                          | wf_safe_t_step
                          | progress type.inversion_type
                          | progress expr.inversion_wf_constr ].
      Qed.

      Lemma wf_rlist_rect_cast {A A' P}
            N1 N2 C1 C2 ls1 ls2 G
            (Hwf : expr.wf G ls1 ls2)
            (HN : UnderLets.wf (fun G' x1 x2 => Compile.wf_anyexpr G' (type.base P) (AnyExpr.wrap x1) (AnyExpr.wrap x2)) G N1 N2)
            (HC : forall G' x xs y ys rec1 rec2,
                (exists seg, G' = (seg ++ G)%list)
                -> expr.wf G x y
                -> expr.wf G (reify_list xs) (reify_list ys)
                -> expr.wf G' rec1 rec2
                -> UnderLets.wf (fun G'' => expr.wf G'') G' (C1 x xs rec1) (C2 y ys rec2))
        : option_eq (UnderLets.wf (fun G' => Compile.wf_anyexpr G' (type.base P)) G)
                    (@rlist_rect_cast var1 A A' P var1 N1 C1 ls1 _ id)
                    (@rlist_rect_cast var2 A A' P var2 N2 C2 ls2 _ id).
      Proof.
        cbv [rlist_rect_cast].
        cbv [Compile.castbe Compile.castb id Compile.option_bind' Option.bind sequence_return]; rewrite_type_transport_correct; break_innermost_match;
          type_beq_to_eq; subst; [ | reflexivity ].
        apply wf_rlist_rect; auto.
        eapply UnderLets.wf_Proper_list_impl; [ | | eassumption ]; trivial; cbn; intros ? ? ? H.
        inversion H; inversion_sigma; type.inversion_type; subst; assumption.
      Qed.

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
                        => exists (pf1 : AnyExpr.anyexpr_ty v1 = P) (pf2 : AnyExpr.anyexpr_ty v2 = P) G'',
                            (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                            /\ expr.wf G''
                                       (rew [fun t : base.type => expr t] pf1 in AnyExpr.unwrap v1)
                                       (rew [fun t : base.type => expr t] pf2 in AnyExpr.unwrap v2))
                       G)
                    (@rlist_rect var1 A P (@Compile.value _ ident var1) N1 C1 ls1 _ id)
                    (@rlist_rect var2 A P (@Compile.value _ ident var2) N2 C2 ls2 _ id).
      Proof.
        cbv [rlist_rect].
        rewrite !expr.reflect_list_cps_id; cbv [id].
        cbv [Compile.option_bind' Option.bind].
        break_innermost_match.
        all: repeat first [ match goal with
                            | [ H : invert_expr.reflect_list ?v = Some _, H' : invert_expr.reflect_list ?v' = None |- _ ]
                              => first [ erewrite <- expr.wf_reflect_list in H' by eassumption
                                       | erewrite -> expr.wf_reflect_list in H' by eassumption ];
                                 exfalso; clear -H H'; congruence
                            | [ |- UnderLets.wf _ _ _ _ ] => constructor
                            | [ |- Compile.wf_anyexpr _ _ _ _ ] => constructor
                            end
                          | progress expr.invert_subst
                          | progress cbn [sequence_return option_eq]
                          | assumption
                          | reflexivity
                          | (exists eq_refl)
                          | apply @UnderLets.wf_splice with (P:=fun G' v1 v2
                                                                => exists G'',
                                                                    (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                                                                    /\ expr.wf G'' v1 v2)
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
                          | progress cbn [sequence_return option_eq AnyExpr.anyexpr_ty eq_rect]
                          | (exists eq_refl)
                          | assumption
                          | reflexivity
                          | solve [ auto ]
                          | progress subst
                          | apply @UnderLets.wf_splice with (P:=fun G' v1 v2
                                                                => exists G'',
                                                                    (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                                                                    /\ expr.wf G'' v1 v2)
                          | progress intros
                          | wf_safe_t_step
                          | progress type.inversion_type
                          | progress expr.inversion_wf_constr ].
      Qed.

      Lemma wf_rlist_rect_castv {A A' P}
            N1 N2 C1 C2 ls1 ls2 G
            (Hwf : expr.wf G ls1 ls2)
            (HN : UnderLets.wf (fun G' x1 x2
                                => exists G'',
                                    (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                                    /\ Compile.wf_anyexpr G'' (type.base P) (AnyExpr.wrap x1) (AnyExpr.wrap x2)) G N1 N2)
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
                        => exists (pf1 : AnyExpr.anyexpr_ty v1 = P) (pf2 : AnyExpr.anyexpr_ty v2 = P) G'',
                            (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G'' -> Compile.wf_value G' v1' v2')
                            /\ expr.wf G''
                                       (rew [fun t : base.type => expr t] pf1 in AnyExpr.unwrap v1)
                                       (rew [fun t : base.type => expr t] pf2 in AnyExpr.unwrap v2))
                       G)
                    (@rlist_rect_cast var1 A A' P (@Compile.value _ ident var1) N1 C1 ls1 _ id)
                    (@rlist_rect_cast var2 A A' P (@Compile.value _ ident var2) N2 C2 ls2 _ id).
      Proof.
        cbv [rlist_rect_cast].
        cbv [Compile.castbe Compile.castb id Compile.option_bind' Option.bind sequence_return]; rewrite_type_transport_correct; break_innermost_match;
          type_beq_to_eq; subst; [ | reflexivity ].
        apply wf_rlist_rectv; auto.
        eapply UnderLets.wf_Proper_list_impl; [ | | eassumption ]; trivial; cbn; intros ? ? ? H.
        repeat let x := fresh in intro x; specialize (H x).
        destruct H as [? [H0 H1] ].
        inversion H1; inversion_sigma; type.inversion_type; subst; eauto.
      Qed.


      Lemma wf_nat_rect {A}
            G O1 O2 S1 S2 n
            (HO : UnderLets.wf (fun G' => expr.wf G') G O1 O2)
            (HS : forall n rec1 rec2,
                UnderLets.wf (fun G' => expr.wf G') G rec1 rec2
                -> UnderLets.wf (fun G' => expr.wf G') G (S1 n rec1) (S2 n rec2))
        : UnderLets.wf (fun G' => expr.wf G') G
                       (nat_rect (fun _ => UnderLets.UnderLets base.type ident var1 (expr (type.base A))) O1 S1 n)
                       (nat_rect (fun _ => UnderLets.UnderLets base.type ident var2 (expr (type.base A))) O2 S2 n).
      Proof. induction n; cbn [nat_rect]; auto. Qed.

      Lemma wf_nat_rect_arrow {A B}
            G O1 O2 S1 S2 n
            (HO : Compile.wf_value G O1 O2)
            (HS : forall n rec1 rec2,
                Compile.wf_value G rec1 rec2
                -> Compile.wf_value G (S1 n rec1) (S2 n rec2))
        : Compile.wf_value
            G
            (nat_rect (fun _ => @Compile.value base.type ident var1 (type.base A -> type.base B)) O1 S1 n)
            (nat_rect (fun _ => @Compile.value base.type ident var2 (type.base A -> type.base B)) O2 S2 n).
      Proof. induction n; cbn [nat_rect]; auto. Qed.

      (** TODO: MOVE ME? *)
      Lemma fold_right_impl_Proper {A} {P Q : A -> Prop} ls (concl1 concl2 : Prop)
            (Hconcl : concl1 -> concl2)
            (HPQ : forall a, In a ls -> Q a -> P a)
        : fold_right (fun a (concl : Prop) => P a -> concl) concl1 ls
          -> fold_right (fun a (concl : Prop) => Q a -> concl) concl2 ls.
      Proof. induction ls as [|x xs IHxs]; cbn [fold_right In] in *; intuition. Qed.

      Lemma forall_In_existT {A P} {Q : forall a : A, P a -> Prop} ls
        : fold_right
            (fun xp (concl : Prop)
             => Q (projT1 xp) (projT2 xp) -> concl)
            (forall x p, In (@existT A P x p) ls -> Q x p)
            ls.
      Proof.
        induction ls as [|x xs IHxs]; cbn [fold_right In]; intros;
          destruct_head' False; destruct_head'_or.
        eapply fold_right_impl_Proper; [ | | refine IHxs ]; intuition (subst; eauto).
      Qed.

      Local Ltac start_cps_id :=
        lazymatch goal with
        | [ |- forall x p, In (@existT ?A ?P x p) ?ls -> @?Q x p ]
          => apply (@forall_In_existT A P Q ls); cbn [projT1 projT2]; cbv [id]
        end;
        try reflexivity.

      Local Ltac cps_id_step :=
        first [ reflexivity
              | progress intros
              | progress destruct_head' False
              | progress subst
              | progress inversion_option
              | progress cbn [Compile.value' UnderLets.splice eq_rect projT1 projT2 Option.bind Option.sequence Option.sequence_return] in *
              | progress destruct_head'_sigT
              | progress destruct_head'_prod
              | progress destruct_head'_unit
              | progress cbv [id Compile.binding_dataT pattern.ident.arg_types Compile.ptype_interp Compile.ptype_interp_cps Compile.pbase_type_interp_cps Compile.value Compile.app_binding_data Compile.app_ptype_interp_cps Compile.app_pbase_type_interp_cps Compile.lift_with_bindings Compile.lift_ptype_interp_cps Compile.lift_pbase_type_interp_cps cpsbind cpscall cpsreturn cps_option_bind type_base rwhen] in *
              | progress type_beq_to_eq
              | progress rewrite_type_transport_correct
              | break_match_step ltac:(fun v => match type of v with sumbool _ _ => idtac end)
              | progress cbv [Compile.option_bind' Compile.castbe Compile.castb Compile.castv] in *
              | progress break_innermost_match
              | rewrite !expr.reflect_list_cps_id
              | match goal with
                | [ |- context[@rlist_rect_cast ?var ?A ?A' ?P ?ivar ?N_case ?C_case ?ls ?T ?k] ]
                  => (tryif (let __ := constr:(eq_refl : k = (fun x => x)) in idtac)
                       then fail
                       else rewrite (@rlist_rect_cast_cps_id var A A' P ivar N_case C_case ls T k))
                | [ |- context[@rlist_rect ?var ?A ?P ?ivar ?N_case ?C_case ?ls ?T ?k] ]
                  => (tryif (let __ := constr:(eq_refl : k = (fun x => x)) in idtac)
                       then fail
                       else rewrite (@rlist_rect_cps_id var A P ivar N_case C_case ls T k))
                end
              | progress cbv [Option.bind] in *
              | break_match_step ltac:(fun _ => idtac) ].

      Local Ltac cps_id_t := start_cps_id; repeat cps_id_step.

      Lemma nbe_cps_id {var}
        : forall p r, In (existT _ p r) (@nbe_rewrite_rules var)
                      -> forall v T k, r v T k = k (r v _ id).
      Proof. Time cps_id_t. Time Qed.

      Lemma arith_cps_id max_const {var}
        : forall p r, In (existT _ p r) (@arith_rewrite_rules var max_const)
                 -> forall v T k, r v T k = k (r v _ id).
      Proof. Time cps_id_t. Time Qed.

      Lemma fancy_cps_id invert_low invert_high {var}
        : forall p r, In (existT _ p r) (@fancy_rewrite_rules var invert_low invert_high)
                 -> forall v T k, r v T k = k (r v _ id).
      Proof. Time cps_id_t. Time Qed.

      (** TODO: MOVE ME? *)
      Lemma forall_In_pair_existT {A A' P P'} {Q : forall (a : A) (a' : A'), P a -> P' a' -> Prop} ls
        : fold_right
            (fun xp_x'p' (concl : Prop)
             => Q (projT1 (fst xp_x'p')) (projT1 (snd xp_x'p')) (projT2 (fst xp_x'p')) (projT2 (snd xp_x'p')) -> concl)
            (forall x p x' p', In (@existT A P x p, @existT A' P' x' p') ls -> Q x x' p p')
            ls.
      Proof.
        induction ls as [|x xs IHxs]; cbn [fold_right In]; intros;
          destruct_head' False; destruct_head'_prod; destruct_head'_or; intros.
        eapply fold_right_impl_Proper; [ | | refine IHxs ]; intuition (inversion_prod; subst; eauto).
      Qed.

      Local Ltac start_good cps_id rewrite_rules :=
        split; [ reflexivity | ];
        repeat apply conj; try solve [ eapply cps_id ]; [];
        lazymatch goal with
        | [ |- forall x p x' p', In (@existT ?A ?P x p, @existT ?A' ?P' x' p') ?ls -> @?Q x x' p p' ]
          => apply (@forall_In_pair_existT A A' P P' Q ls); cbn [projT1 projT2 fst snd]; cbv [id]
        end;
        intros; (split; [ reflexivity | ]).

      Local Ltac good_t_step :=
        first [ progress subst
              | progress cbn [eq_rect Compile.value' option_eq projT1 projT2 fst snd base.interp In combine Option.bind Option.sequence Option.sequence_return UnderLets.splice] in *
              | progress destruct_head'_unit
              | progress destruct_head'_sigT
              | progress destruct_head'_prod
              | progress eliminate_hprop_eq
              | progress destruct_head'_and
              | progress destruct_head'_sig
              | progress inversion_option
              | progress destruct_head'_ex
              | progress cbn [Compile.binding_dataT pattern.ident.arg_types] in *
              | progress cbn [Compile.wf_binding_dataT Compile.wf_ptype_interp_cps Compile.wf_pbase_type_interp_cps fst snd projT1 projT2] in *
              | progress intros
              | progress cbv [Compile.ptype_interp Compile.ptype_interp_cps Compile.pbase_type_interp_cps id] in *
              | progress cbv [Compile.wf_ptype_interp_id] in *
              | progress cbv [id Compile.binding_dataT pattern.ident.arg_types Compile.ptype_interp Compile.ptype_interp_cps Compile.pbase_type_interp_cps Compile.value Compile.app_binding_data Compile.app_ptype_interp_cps Compile.app_pbase_type_interp_cps Compile.lift_with_bindings Compile.lift_ptype_interp_cps Compile.lift_pbase_type_interp_cps cpsbind cpscall cpsreturn cps_option_bind type_base Compile.wf_binding_dataT Compile.wf_ptype_interp_id Compile.wf_ptype_interp_cps Compile.wf_pbase_type_interp_cps ident.smart_Literal rwhen AnyExpr.unwrap nth_default SubstVarLike.is_var_fst_snd_pair_opp] in *
              | progress cbv [Compile.option_bind' Compile.castbe Compile.castb Compile.castv] in *
              | progress type_beq_to_eq
              | progress type.inversion_type
              | progress rewrite_type_transport_correct
              | progress specialize_by exact eq_refl
              | break_innermost_match_step
              | wf_safe_t_step
              | rewrite !expr.reflect_list_cps_id
              | congruence
              | match goal with
                | [ H : nth_error ?l1 ?n = Some _, H' : nth_error ?l2 ?n = None |- _ ]
                  => let H0 := fresh in
                    assert (H0 : length l1 = length l2) by congruence;
                    apply nth_error_error_length in H';
                    apply nth_error_value_length in H;
                    exfalso; clear -H0 H H'; lia
                | [ |- expr.wf _ (reify_list _) (reify_list _) ] => rewrite expr.wf_reify_list
                | [ |- context[length ?ls] ] => tryif is_var ls then fail else (progress autorewrite with distr_length)
                | [ H : context[length ?ls] |- _ ] => tryif is_var ls then fail else (progress autorewrite with distr_length in H)
                | [ |- @ex (_ = _) _ ] => (exists eq_refl)
                | [ |- ex _ ] => eexists
                | [ |- UnderLets.wf _ _ _ _ ] => constructor
                | [ |- UnderLets.wf _ _ (UnderLets.splice _ _) (UnderLets.splice _ _) ]
                  => eapply UnderLets.wf_splice; [ eapply UnderLets.wf_Proper_list; [ | | solve [ repeat good_t_step ] ] | ]
                | [ |- UnderLets.wf _ _ (UnderLets.splice _ _) (UnderLets.splice _ _) ] => eapply UnderLets.wf_splice
                | [ |- UnderLets.wf _ _ (UnderLets.splice_list _ _) (UnderLets.splice_list _ _) ]
                  => apply @UnderLets.wf_splice_list_no_order with (P:=fun G' => expr.wf G')
                | [ |- Compile.wf_anyexpr _ _ _ _ ] => constructor
                | [ |- context[@rlist_rect_cast ?var ?A ?A' ?P ?ivar ?N_case ?C_case ?ls ?T ?k] ]
                  => (tryif (let __ := constr:(eq_refl : k = (fun x => x)) in idtac)
                      then fail
                      else rewrite (@rlist_rect_cast_cps_id var A A' P ivar N_case C_case ls T k))
                | [ |- context[@rlist_rect ?var ?A ?P ?ivar ?N_case ?C_case ?ls ?T ?k] ]
                  => (tryif (let __ := constr:(eq_refl : k = (fun x => x)) in idtac)
                      then fail
                      else rewrite (@rlist_rect_cps_id var A P ivar N_case C_case ls T k))
                | [ |- ?x = ?x /\ _ ] => split; [ reflexivity | ]
                | [ |- context[invert_expr.reflect_list ?v] ] => destruct (invert_expr.reflect_list v) eqn:?
                | [ H : invert_expr.reflect_list ?v = Some _, H' : invert_expr.reflect_list ?v' = None |- _ ]
                  => first [ erewrite <- expr.wf_reflect_list in H' by eassumption
                          | erewrite -> expr.wf_reflect_list in H' by eassumption ];
                    exfalso; clear -H H'; congruence
                | [ H : Compile.wf_value _ (reify_list _) (reify_list _) |- _ ]
                  => hnf in H; rewrite expr.wf_reify_list in H
                | [ H : length ?l = length ?l' |- context[length ?l] ] => rewrite H
                | [ H : context[combine (firstn ?n _) (firstn ?n _)] |- _ ] => rewrite <- firstn_combine in H
                | [ H : context[combine (skipn ?n _) (skipn ?n _)] |- _ ] => rewrite <- skipn_combine in H
                | [ H : context[In _ (firstn _ _)] |- _ ] => solve [ eauto using In_firstn ]
                | [ H : context[In _ (skipn _ _)] |- _ ] => solve [ eauto using In_skipn ]
                | [ H : context[combine (repeat _ _) (repeat _ _)] |- _ ] => rewrite combine_repeat in H
                | [ H : context[combine (Lists.List.repeat _ _) (Lists.List.repeat _ _)] |- _ ] => rewrite combine_repeat in H
                | [ H : In _ (repeat _ _) |- _ ] => apply repeat_spec in H
                | [ H : In _ (Lists.List.repeat _ _) |- _ ] => apply repeat_spec in H
                | [ H : context[combine (rev ?l1) (rev ?l2)] |- _ ] => rewrite (@combine_rev_rev_samelength _ _ l1 l2) in H by congruence
                | [ H : In _ (rev _) |- _ ] => rewrite <- in_rev in H
                | [ H : forall e1' e2', In (e1', e2') (combine ?l1 ?l2) -> _, H1 : nth_error ?l1 ?n = Some ?e1, H2 : nth_error ?l2 ?n = Some ?e2 |- _ ]
                  => specialize (fun pf => H e1 e2 (@nth_error_In _ _ n _ pf))
                | [ H : context[nth_error (combine _ _) _] |- _ ] => rewrite nth_error_combine in H
                | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                | [ H : context[combine (map _ _) (map _ _)] |- _ ] => rewrite combine_map_map in H
                | [ H : context[nth_error (update_nth _ _ _) _] |- _ ] => rewrite nth_update_nth in H
                | [ H : nth_error (map _ _) _ = Some _ |- _ ] => apply nth_error_map in H
                | [ H : In _ (map _ _) |- _ ] => rewrite in_map_iff in H
                | [ H : In _ (combine _ _) |- _ ] => apply In_nth_error_value in H
                | [ |- expr.wf ?G (fold_right _ _ (map _ (seq ?a ?b))) (fold_right _ _ (map _ (seq ?a ?b))) ]
                  => induction (seq a b); cbn [fold_right map]
                | [ Hwf : Compile.wf_value _ ?x _, H : context[SubstVarLike.is_recursively_var_or_ident _ ?x] |- _ ] => erewrite SubstVarLike.wfT_is_recursively_var_or_ident in H by exact Hwf
                | [ |- UnderLets.wf _ _ (nat_rect _ _ _ _) (nat_rect _ _ _ _) ] => apply wf_nat_rect
                | [ |- UnderLets.wf _ _ (nat_rect _ _ _ _ _) (nat_rect _ _ _ _ _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply wf_nat_rect_arrow; [ | | reflexivity | ]; cycle 1 ]; revgoals; hnf
                | [ H : Compile.wf_value _ ?e1 ?e2 |- UnderLets.wf _ _ (?e1 _) (?e2 _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H; [ reflexivity | ] ]; revgoals
                | [ H : Compile.wf_value _ ?e1 ?e2 |- UnderLets.wf _ _ (?e1 _ _) (?e2 _ _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H; [ reflexivity | | reflexivity | ] ]; revgoals
                | [ H : Compile.wf_value _ ?e1 ?e2 |- UnderLets.wf _ _ (?e1 _ _ _) (?e2 _ _ _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H; [ reflexivity | | reflexivity | | reflexivity | ]; cycle 1 ]; revgoals
                | [ H : Compile.wf_value _ ?e1 ?e2 |- Compile.wf_value' _ (?e1 _) (?e2 _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H; [ reflexivity | ] ]; revgoals
                | [ H : Compile.wf_value _ ?e1 ?e2 |- Compile.wf_value' _ (?e1 _ _) (?e2 _ _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H; [ reflexivity | | reflexivity | ] ]; revgoals
                | [ H : Compile.wf_value _ ?e1 ?e2 |- Compile.wf_value' _ (?e1 _ _ _) (?e2 _ _ _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H; [ reflexivity | | reflexivity | | reflexivity | ]; cycle 1 ]; revgoals
                | [ |- Compile.wf_value _ (fun _ => _) (fun _ => _) ] => hnf
                | [ H : Compile.wf_value _ ?f ?g |- UnderLets.wf _ _ (?f _) (?g _) ] => eapply UnderLets.wf_Proper_list; [ | | eapply H; solve [ eauto ] ]; solve [ repeat good_t_step ]
                | [ H : Compile.wf_value _ ?f ?g |- UnderLets.wf _ _ (?f _ _) (?g _ _) ] => eapply UnderLets.wf_Proper_list; [ | | eapply H; solve [ eauto ] ]; solve [ repeat good_t_step ]
                | [ H : Compile.wf_value _ ?f ?g |- UnderLets.wf _ _ (?f _ _ _) (?g _ _ _) ] => eapply UnderLets.wf_Proper_list; [ | | eapply H; solve [ eauto ] ]; solve [ repeat good_t_step ]
                | [ H : Compile.wf_value ?G ?e1 ?e2 |- UnderLets.wf _ ?G (?e1 _) (?e2 _) ] => eapply (H nil)
                | [ |- Compile.wf_anyexpr _ _ _ _ ] => constructor
                | [ H : Compile.wf_value ?G ?ls1 ?ls2, H1 : rlist_rect_cast ?N1 ?C1 ?ls1 _ (fun x => x) = _, H2 : rlist_rect_cast ?N2 ?C2 ?ls2 _ (fun y => y) = _ |- _ ]
                  => let H' := fresh in
                    pose proof (@wf_rlist_rect_cast _ _ _ N1 N2 C1 C2 ls1 ls2 G H) as H'; cbv [id Compile.value] in H', H1, H2; rewrite H1, H2 in H';
                    clear H1 H2;
                    first [ apply H'
                          | refine ((fun pf : Some _ = None => _) _); [ inversion_option | apply H' ] ]
                | [ H : Compile.wf_value ?G ?ls1 ?ls2, H1 : rlist_rect_cast ?N1 ?C1 ?ls1 _ (fun x => x) = _, H2 : rlist_rect_cast ?N2 ?C2 ?ls2 _ (fun y => y) = _ |- _ ]
                  => let H' := fresh in
                    pose proof (@wf_rlist_rect_castv _ _ _ N1 N2 C1 C2 ls1 ls2 G H) as H'; cbv [id Compile.value] in H', H1, H2; rewrite H1, H2 in H';
                    clear H1 H2;
                    first [ apply H'
                          | refine ((fun pf : Some _ = None => _) _); [ inversion_option | apply H' ] ]
                | [ H : Compile.wf_value ?G ?ls1 ?ls2, H1 : rlist_rect ?N1 ?C1 ?ls1 _ (fun x => x) = _, H2 : rlist_rect ?N2 ?C2 ?ls2 _ (fun y => y) = _ |- _ ]
                  => let H' := fresh in
                    pose proof (@wf_rlist_rect _ _ N1 N2 C1 C2 ls1 ls2 G H) as H'; cbv [id Compile.value] in H', H1, H2; rewrite H1, H2 in H';
                    clear H1 H2;
                    first [ apply H'
                          | refine ((fun pf : Some _ = None => _) _); [ inversion_option | apply H' ] ]
                | [ H : Compile.wf_value ?G ?ls1 ?ls2, H1 : rlist_rect ?N1 ?C1 ?ls1 _ (fun x => x) = _, H2 : rlist_rect ?N2 ?C2 ?ls2 _ (fun y => y) = _ |- _ ]
                  => let H' := fresh in
                    pose proof (@wf_rlist_rectv _ _ N1 N2 C1 C2 ls1 ls2 G H) as H'; cbv [id Compile.value] in H', H1, H2; rewrite H1, H2 in H';
                    clear H1 H2;
                    first [ apply H'
                          | refine ((fun pf : Some _ = None => _) _); [ inversion_option | apply H' ] ]
                | [ H : ?R ?G ?a ?b |- expr.wf ?G ?a ?b ]
                  => is_evar R; revert H; instantiate (1:=fun G' => expr.wf G'); solve [ auto ]
                | [ H : expr.wf ?G ?a ?b |- ?R ?G ?a ?b ]
                  => is_evar R; instantiate (1:=fun G' => expr.wf G'); solve [ auto ]
                | [ |- (forall t v1 v2, In _ _ -> _) /\ expr.wf _ _ _ ] => apply conj; revgoals
                | [ |- (forall t v1 v2, In _ _ -> _) /\ Compile.wf_anyexpr _ _ _ _ ] => apply conj; revgoals
                | [ H : expr.wf _ ?x ?y |- Compile.wf_value _ ?x ?y ] => hnf
                | [ |- Compile.wf_value _ ?x ?y ] => eapply Compile.wf_value'_Proper_list; [ | solve [ cbv [Compile.wf_value] in *; eauto ] ]; solve [ wf_t ]
                | [ |- In ?x ?ls ] => is_evar ls; refine (or_introl eq_refl : In x (x :: _)); shelve
                | [ |- or (_ = _) ?G ] => first [ left; reflexivity | has_evar G; right ]
                | [ H : @In ?A _ ?ls |- _ ] => is_evar ls; unify ls (@nil A); cbn [In] in H
                end
              | progress expr.invert_subst
              | solve [ wf_t ]
              | break_match_hyps_step ltac:(fun v => let h := head v in constr_eq h (@nth_error))
              | break_match_hyps_step ltac:(fun v => match v with Nat.eq_dec _ _ => idtac end)
              | progress cbv [option_map] in * ].

      Lemma nbe_rewrite_rules_good
        : rewrite_rules_goodT nbe_rewrite_rules nbe_rewrite_rules.
      Proof.
        Time start_good (@nbe_cps_id) (@nbe_rewrite_rules).
        Time all: repeat repeat good_t_step.
      Qed.

      Lemma arith_rewrite_rules_good max_const
        : rewrite_rules_goodT (arith_rewrite_rules max_const) (arith_rewrite_rules max_const).
      Proof.
        Time start_good (@arith_cps_id) (@arith_rewrite_rules).
        Time all: repeat good_t_step.
      Qed.

      Lemma fancy_rewrite_rules_good
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_goodT (fancy_rewrite_rules invert_low invert_high) (fancy_rewrite_rules invert_low invert_high).
      Proof.
        Time start_good (@fancy_cps_id) (@fancy_rewrite_rules).
        Time all: repeat good_t_step.
        all: cbv [Option.bind].
        Time all: repeat good_t_step.
      Time Qed.
    End good.
  End RewriteRules.
End Compilers.
