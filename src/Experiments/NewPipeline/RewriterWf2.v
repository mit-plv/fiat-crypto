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
  Import defaults.
  Import RewriterWf1.Compilers.RewriteRules.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    Module Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.
      Import RewriterWf1.Compilers.RewriteRules.Compile.

      Section with_type.
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {ident : type.type base.type -> Type}
                (eta_ident_cps : forall {T : type.type base.type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : type.type pattern.base.type -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)
                (type_vars_of_pident : forall t, pident t -> list (type.type pattern.base.type))

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type.type base.type)
                (raw_pident_to_typed : forall (pidc : raw_pident) (args : full_types pidc), ident (type_of_raw_pident pidc args))
                (raw_pident_is_simple : raw_pident -> bool)
                (pident_unify_unknown_correct
                 : forall t t' idc idc', pident_unify_unknown t t' idc idc' = pident_unify t t' idc idc')
                (invert_bind_args_unknown_correct
                 : forall t idc pidc, invert_bind_args_unknown t idc pidc = invert_bind_args t idc pidc)
                (eta_ident_cps_correct : forall T t idc f, @eta_ident_cps T t idc f = f _ idc)
                (raw_pident_to_typed_invert_bind_args_type
                 : forall t idc p f, invert_bind_args t idc p = Some f -> t = type_of_raw_pident p f)
                (raw_pident_to_typed_invert_bind_args
                 : forall t idc p f (pf : invert_bind_args t idc p = Some f),
                    raw_pident_to_typed p f = rew [ident] raw_pident_to_typed_invert_bind_args_type t idc p f pf in idc)
        (*(raw_pident_bl : forall p q, raw_pident_beq p q = true -> p = q)
                (raw_pident_lb : forall p q, p = q -> raw_pident_beq p q = true)*).
        Local Notation type := (type.type base.type).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation expr := (@expr.expr base.type ident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value' := (@value' base.type ident).
        Local Notation value := (@value base.type ident).
        Local Notation value_with_lets := (@value_with_lets base.type ident).
        Local Notation Base_value := (@Base_value base.type ident).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base.type ident).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base.type ident).
        Local Notation reify := (@reify ident).
        Local Notation reflect := (@reflect ident).
        Local Notation rawexpr := (@rawexpr ident).
        Local Notation eval_decision_tree var := (@eval_decision_tree ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation reveal_rawexpr e := (@reveal_rawexpr_cps ident _ e _ id).

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Context (reify_and_let_binds_base_cps1 : forall (t : base.type), @expr var1 t -> forall T, (@expr var1 t -> @UnderLets var1 T) -> @UnderLets var1 T)
                  (reify_and_let_binds_base_cps2 : forall (t : base.type), @expr var2 t -> forall T, (@expr var2 t -> @UnderLets var2 T) -> @UnderLets var2 T)
                  (wf_reify_and_let_binds_base_cps
                   : forall G (t : base.type) x1 x2 T1 T2 P
                            (Hx : expr.wf G x1 x2)
                            (e1 : expr t -> @UnderLets var1 T1) (e2 : expr t -> @UnderLets var2 T2)
                            (He : forall x1 x2 G' seg, (G' = (seg ++ G)%list) -> expr.wf G' x1 x2 -> UnderLets.wf P G' (e1 x1) (e2 x2)),
                      UnderLets.wf P G (reify_and_let_binds_base_cps1 t x1 T1 e1) (reify_and_let_binds_base_cps2 t x2 T2 e2)).

          Local Notation wf_value' := (@wf_value' base.type ident var1 var2).
          Local Notation wf_value := (@wf_value base.type ident var1 var2).
          Local Notation wf_value_with_lets := (@wf_value_with_lets base.type ident var1 var2).
          Local Notation reify_and_let_binds_cps1 := (@reify_and_let_binds_cps ident var1 reify_and_let_binds_base_cps1).
          Local Notation reify_and_let_binds_cps2 := (@reify_and_let_binds_cps ident var2 reify_and_let_binds_base_cps2).
          Local Notation rewrite_rulesT1 := (@rewrite_rulesT ident var1 pident pident_arg_types type_vars_of_pident).
          Local Notation rewrite_rulesT2 := (@rewrite_rulesT ident var2 pident pident_arg_types type_vars_of_pident).
          Local Notation eval_rewrite_rules1 := (@eval_rewrite_rules ident var1 pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
          Local Notation eval_rewrite_rules2 := (@eval_rewrite_rules ident var2 pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
          Local Notation with_unification_resultT'1 := (@with_unification_resultT' ident var1 pident pident_arg_types).
          Local Notation with_unification_resultT'2 := (@with_unification_resultT' ident var2 pident pident_arg_types).
          Local Notation with_unification_resultT1 := (@with_unification_resultT ident var1 pident pident_arg_types type_vars_of_pident).
          Local Notation with_unification_resultT2 := (@with_unification_resultT ident var2 pident pident_arg_types type_vars_of_pident).
          Local Notation rewrite_rule_data1 := (@rewrite_rule_data ident var1 pident pident_arg_types type_vars_of_pident).
          Local Notation rewrite_rule_data2 := (@rewrite_rule_data ident var2 pident pident_arg_types type_vars_of_pident).
          Local Notation with_unif_rewrite_ruleTP_gen1 := (@with_unif_rewrite_ruleTP_gen ident var1 pident pident_arg_types type_vars_of_pident).
          Local Notation with_unif_rewrite_ruleTP_gen2 := (@with_unif_rewrite_ruleTP_gen ident var2 pident pident_arg_types type_vars_of_pident).
          Local Notation wf_rawexpr := (@wf_rawexpr ident var1 var2).
          (** TODO: Move Me up *)
          Local Notation unify_pattern'1 := (@unify_pattern' ident var1 pident pident_arg_types pident_unify pident_unify_unknown).
          Local Notation unify_pattern'2 := (@unify_pattern' ident var2 pident pident_arg_types pident_unify pident_unify_unknown).
          Local Notation unify_pattern1 := (@unify_pattern ident var1 pident pident_arg_types pident_unify pident_unify_unknown type_vars_of_pident).
          Local Notation unify_pattern2 := (@unify_pattern ident var2 pident pident_arg_types pident_unify pident_unify_unknown type_vars_of_pident).
          Local Notation wf_with_unification_resultT' := (@wf_with_unification_resultT' ident pident pident_arg_types var1 var2).
          Local Notation wf_with_unification_resultT := (@wf_with_unification_resultT ident pident pident_arg_types type_vars_of_pident var1 var2).
          Local Notation wf_with_unif_rewrite_ruleTP_gen := (@wf_with_unif_rewrite_ruleTP_gen ident pident pident_arg_types type_vars_of_pident var1 var2).
          Local Notation wf_deep_rewrite_ruleTP_gen := (@wf_deep_rewrite_ruleTP_gen ident var1 var2).

          (* Because [proj1] and [proj2] in the stdlib are opaque *)
          Local Notation proj1 x := (let (a, b) := x in a).
          Local Notation proj2 x := (let (a, b) := x in b).

          Lemma wf_unify_pattern'
                (G : list { t : _ & (var1 t * var2 t)%type })
                {t1 t2 t'} {p1 : pattern t1} {p2 : pattern t2} {evm1 evm2 : EvarMap} {re1 re2 e1 e2} {K1 K2}
                (PK : K1 (pattern.type.subst_default t1 evm1) -> K2 (pattern.type.subst_default t2 evm2) -> Prop)
                {T1 T2}
                (PT : T1 -> T2 -> Prop)
                {v1 v2}
                {cont1 : K1 _ -> option T1}
                {cont2 : K2 _ -> option T2}
                (He : @wf_rawexpr G t' re1 e1 re2 e2)
                (Hv : @wf_with_unification_resultT' G t1 t2 p1 p2 evm1 evm2 _ _ PK v1 v2)
                (HT : forall v1 v2, PK v1 v2 -> option_eq PT (cont1 v1) (cont2 v2))
            : option_eq
                PT
                (@unify_pattern'1 t1 re1 p1 evm1 K1 v1 T1 cont1)
                (@unify_pattern'2 t2 re2 p2 evm2 K2 v2 T2 cont2).
          Proof using pident_unify_unknown_correct.
            revert dependent p2; intro p2; revert dependent re1; revert dependent re2; revert t' e1 e2; revert dependent evm1; revert dependent evm2; revert dependent K1; revert dependent K2; revert t2 p2.
            induction p1, p2; intros; cbn [unify_pattern'].
            all: repeat first [ progress cbn [with_unification_resultT' wf_with_unification_resultT' Option.bind eq_rect eq_sigT eq_sigT_uncurried eq_existT_uncurried] in *
                              | progress cbv [option_bind'] in *
                              | assumption
                              | reflexivity
                              | exfalso; assumption
                              | progress subst
                              | progress destruct_head'_sig
                              | progress inversion_sigma
                              | progress rewrite_type_transport_correct
                              | progress type_beq_to_eq
                              | match goal with
                                | [ H : @wf_rawexpr ?G ?t ?re1 ?e1 ?re2 ?e2 |- context[match ?re1 with _ => _ end] ]
                                  => is_var t; is_var re1; is_var e1; is_var re2; is_var e2; is_var G;
                                     destruct H
                                end
                              | rewrite !pident_unify_unknown_correct
                              | break_innermost_match_step
                              | match goal with
                                | [ |- context[rew ?pf in _] ]
                                  => is_var pf;
                                     lazymatch type of pf with
                                     | type_of_rawexpr _ = ?t
                                       => let t' := fresh "t" in
                                          remember t as t' eqn:? in *; destruct pf
                                     end
                                | [ H : forall v1 v2, ?PK v1 v2 -> option_eq ?PT (?f1 v1) (?f2 v2) |- option_eq ?PT (?f1 _) (?f2 _) ]
                                  => is_var PT; is_var PK; apply H; clear dependent PT
                                | [ H : forall v1 v2, wf_value _ _ _ -> ?PK (?f1 v1) (?f2 v2) |- ?PK (?f1 _) (?f2 _) ]
                                  => is_var PK; apply H; clear dependent PK
                                | [ He : wf_rawexpr ?G ?re1 _ ?re2 _
                                    |- wf_value ?G (rew ?pf in value_of_rawexpr ?re1) (value_of_rawexpr ?re2) ]
                                  => apply (wf_value_of_wf_rawexpr_gen (pf2:=eq_refl) He)
                                | [ H : wf_rawexpr _ _ _ _ _ |- _ ]
                                  => progress (try (unique pose proof (proj1 (eq_type_of_rawexpr_of_wf H)));
                                               try (unique pose proof (proj2 (eq_type_of_rawexpr_of_wf H))))
                                | [ H : ?t1 <> ?t2 |- _ ]
                                  => exfalso; apply H; congruence
                                end
                              | solve [ eauto ]
                              | progress cbv [Option.bind] in *
                              | apply related_app_type_of_list_of_forall2_type_of_list_cps ].
          Qed.

          Lemma wf_unify_pattern'_id
                (G : list { t : _ & (var1 t * var2 t)%type })
                {t1 t2 t'} {p1 : pattern t1} {p2 : pattern t2} {evm1 evm2 : EvarMap} {re1 re2 e1 e2} {K1 K2}
                (PK : K1 (pattern.type.subst_default t1 evm1) -> K2 (pattern.type.subst_default t2 evm2) -> Prop)
                {v1 v2}
                (He : @wf_rawexpr G t' re1 e1 re2 e2)
                (Hv : @wf_with_unification_resultT' G t1 t2 p1 p2 evm1 evm2 _ _ PK v1 v2)
            : option_eq
                PK
                (@unify_pattern'1 t1 re1 p1 evm1 K1 v1 _ (@Some _))
                (@unify_pattern'2 t2 re2 p2 evm2 K2 v2 _ (@Some _)).
          Proof using pident_unify_unknown_correct.
            eapply wf_unify_pattern'; try eassumption; eauto.
          Qed.

          Lemma wf_unify_pattern
                (G : list { t : _ & (var1 t * var2 t)%type })
                {t t'} {p : pattern t} {re1 re2 e1 e2} {K1 K2}
                (PK : forall t, K1 t -> K2 t -> Prop)
                {T1 T2}
                (PT : T1 -> T2 -> Prop)
                {v1 v2}
                {cont1 : K1 _ -> option T1}
                {cont2 : K2 _ -> option T2}
                (He : @wf_rawexpr G t' re1 e1 re2 e2)
                (Hv : @wf_with_unification_resultT G t p _ _ (fun evm => PK _) v1 v2)
                (HT : forall t v1 v2 pf1 pf2, PK t (rew [K1] pf1 in v1) (rew [K2] pf2 in v2) -> option_eq PT (cont1 v1) (cont2 v2))
            : option_eq
                PT
                (@unify_pattern1 t re1 p K1 v1 T1 cont1)
                (@unify_pattern2 t re2 p K2 v2 T2 cont2).
          Proof using pident_unify_unknown_correct.
            cbv [unify_pattern].
            erewrite wf_unify_types_cps by eassumption.
            repeat (rewrite unify_types_cps_id; set (unify_types _ _ _ id)).
            repeat match goal with v := unify_types _ _ _ id |- _ => subst v end.
            cbv [Compile.wf_with_unification_resultT] in *.
            revert dependent cont2; revert dependent cont1.
            let lem := constr:(eq_type_of_rawexpr_of_wf ltac:(eassumption)) in
            rewrite (proj1 lem), (proj2 lem).
            intros; specialize (fun v1 v2 => HT _ v1 v2 eq_refl eq_refl); cbn [eq_rect] in *.
            repeat first [ progress subst
                         | progress intros
                         | progress cbv beta in *
                         | match goal with
                           | [ |- ?R ?x ?x ] => reflexivity
                           | [ |- option_eq ?RB (Option.bind ?a ?b) (Option.bind ?a' ?b') ]
                             => eapply Option.bind_Proper_option_eq_hetero
                           | [ |- option_eq _ (pattern.type.app_forall_vars _ _) (pattern.type.app_forall_vars _ _) ]
                             => refine (pattern.type.app_forall_vars_under_forall_vars_relation _)
                           | [ |- option_eq _ (@unify_pattern'1 _ _ _ _ _ _ _ _) (@unify_pattern'2 _ _ _ _ _ _ _ _) ]
                             => eapply wf_unify_pattern'
                           | [ H1 : forall v1 v2, ?PK _ v1 v2 -> option_eq ?PT (?f1 v1) (?f2 v2),
                                 H2 : ?RA ?a1 ?a2
                                 |- option_eq ?PT (?f1 (?a1 _)) (?f2 (?a2 _)) ]
                             => eapply H1; refine H2
                           end
                         | eassumption
                         | progress rewrite_type_transport_correct ].
            (* We separate this into two separate [repeat first] statements because we need to unify evars across goals before proceeding here *)
            repeat first [ reflexivity
                         | exfalso; assumption
                         | progress subst
                         | progress cbn [eq_rect Option.bind option_eq] in *
                         | progress type_beq_to_eq
                         | assumption
                         | progress break_match ].
          Qed.

          Lemma wf_unify_pattern_id
                (G : list { t : _ & (var1 t * var2 t)%type })
                {t t'} {p : pattern t} {re1 re2 e1 e2} {K1 K2}
                (PK : forall t1 t2, K1 t1 -> K2 t2 -> Prop)
                {v1 v2}
                (He : @wf_rawexpr G t' re1 e1 re2 e2)
                (Hv : @wf_with_unification_resultT G t p _ _ (fun evm => PK _ _) v1 v2)
            : option_eq
                (PK _ _)
                (@unify_pattern1 t re1 p K1 v1 _ (@Some _))
                (@unify_pattern2 t re2 p K2 v2 _ (@Some _)).
          Proof using pident_unify_unknown_correct.
            eapply wf_unify_pattern with (PK:=fun t => PK t t); try eassumption.
            intros ? ? ? pf1 pf2; destruct pf1, pf2; cbn; trivial.
          Qed.

          Lemma wf_normalize_deep_rewrite_rule
                {G}
                {t}
                {should_do_again1 with_opt1 under_lets1 is_cps1}
                {should_do_again2 with_opt2 under_lets2 is_cps2}
                {r1 r2}
                (Hwf : @wf_deep_rewrite_ruleTP_gen G t should_do_again1 with_opt1 under_lets1 is_cps1 should_do_again2 with_opt2 under_lets2 is_cps2 r1 r2)
            : option_eq
                (UnderLets.wf (fun G' => wf_maybe_do_again_expr G') G)
                (normalize_deep_rewrite_rule r1 _ id) (normalize_deep_rewrite_rule r2 _ id).
          Proof using Type.
            clear -Hwf.
            all: destruct_head'_bool.
            all: cbv [normalize_deep_rewrite_rule wf_deep_rewrite_ruleTP_gen deep_rewrite_ruleTP_gen] in *.
            all: destruct_head'_and.
            all: repeat first [ assumption
                              | exfalso; assumption
                              | progress cbv [Option.bind option_eq wf_maybe_under_lets_expr] in *
                              | progress inversion_option
                              | progress subst
                              | match goal with
                                | [ |- ?x = ?x ] => reflexivity
                                | [ H : forall T K, ?f T K = @?v T K, H' : context[?f ?T' ?K'] |- _ ]
                                  => lazymatch v with
                                     | context[f]
                                       => lazymatch K' with
                                          | id => fail
                                          | @Some _ => fail
                                          | _ => idtac
                                          end
                                     | _ => idtac
                                     end;
                                     rewrite (H T' K') in H'
                                | [ H : forall T K, ?f T K = @?v T K |- context[?f ?T' ?K'] ]
                                  => lazymatch v with
                                     | context[f]
                                       => lazymatch K' with
                                          | id => fail
                                          | @Some _ => fail
                                          | _ => idtac
                                          end
                                     | _ => idtac
                                     end;
                                     rewrite (H T' K')
                                | [ H : context[id ?x] |- _ ] => change (id x) with x in H
                                | [ |- context[id ?x] ] => change (id x) with x
                                | [ |- UnderLets.wf _ _ _ _ ] => constructor
                                end
                              | break_innermost_match_step
                              | break_innermost_match_hyps_step ].
          Qed.

          Local Ltac fin_handle_list :=
            destruct_head' iff;
            destruct_head'_and;
            cbn [length] in *;
            try solve [ destruct_head'_or;
                        exfalso;
                        repeat match goal with
                               | [ H : ?T, H' : ?T |- _ ] => clear H'
                               | [ H : ?T |- _ ]
                                 => lazymatch type of H with
                                    | _ = _ :> nat => fail
                                    | (_ <= _)%nat => fail
                                    | (_ < _)%nat => fail
                                    | ~_ = _ :> nat => fail
                                    | ~(_ <= _)%nat => fail
                                    | ~(_ < _)%nat => fail
                                    | _ => clear H
                                    end
                               | [ H : context[length ?ls] |- _ ]
                                 => generalize dependent (length ls); intros
                               | _ => progress subst
                               | _ => lia
                               end ].

          Local Ltac handle_nth_error :=
            repeat match goal with
                   | [ H : nth_error _ _ = None |- _ ] => rewrite nth_error_None in H
                   | [ H : nth_error _ _ = Some _ |- _ ] => unique pose proof (@nth_error_value_length _ _ _ _ H)
                   end;
            fin_handle_list.

          Local Ltac handle_swap_list :=
            repeat match goal with
                   | [ H : swap_list _ _ _ = None |- _ ] => rewrite swap_list_None_iff in H
                   | [ H : swap_list _ _ _ = Some _ |- _ ] => unique pose proof (@swap_list_Some_length _ _ _ _ _ H)
                   end;
            fin_handle_list.

          Fixpoint eval_decision_tree_cont_None_ext
                {var} {T ctx d cont}
                (Hcont : forall x y, cont x y = None)
                {struct d}
            : @eval_decision_tree var T ctx d cont = None.
          Proof using Type.
            clear -Hcont eval_decision_tree_cont_None_ext.
            specialize (fun d ctx => @eval_decision_tree_cont_None_ext var T ctx d).
            destruct d; cbn [eval_decision_tree]; intros; try (clear eval_decision_tree_cont_None_ext; tauto).
            { let d := match goal with d : decision_tree |- _ => d end in
              specialize (eval_decision_tree_cont_None_ext d).
              rewrite !Hcont, !eval_decision_tree_cont_None_ext by assumption.
              break_innermost_match; reflexivity. }
            { let d := match goal with d : decision_tree |- _ => d end in
              pose proof (eval_decision_tree_cont_None_ext d) as IHd.
              let d := match goal with d : option decision_tree |- _ => d end in
              pose proof (match d as d' return match d' with Some _ => _ | None => True end with
                          | Some d => eval_decision_tree_cont_None_ext d
                          | None => I
                          end) as IHapp_case.
              all: destruct ctx; try (clear eval_decision_tree_cont_None_ext; (tauto || congruence)); [].
              all: lazymatch goal with
                   | [ |- match ?d with
                          | TryLeaf _ _ => (?res ;; ?ev)%option
                          | _ => _
                          end = None ]
                     => cut (res = None /\ ev = None);
                          [ clear eval_decision_tree_cont_None_ext;
                            let H1 := fresh in
                            let H2 := fresh in
                            intros [H1 H2]; rewrite H1, H2; destruct d; reflexivity
                          | ]
                   end.
              all: split; [ | clear eval_decision_tree_cont_None_ext; eapply IHd; eassumption ].
              (** We use the trick that [induction] inside [Fixpoint]
                  gives us nested [fix]es that pass the guarded
                  checker, as long as we're careful about how we do
                  things *)
              let icases := match goal with d : list (_ * decision_tree) |- _ => d end in
              induction icases as [|icase icases IHicases];
                [ | pose proof (eval_decision_tree_cont_None_ext (snd icase)) as IHicase ];
                clear eval_decision_tree_cont_None_ext.
              (** now we can stop being super-careful about [destruct]
                  ordering because, if we're [Guarded] here (which we
                  are), then we cannot break guardedness from this
                  point on, because we've cleared the bare fixpoint
                  after specializing it to valid arguments *)
              2: revert IHicases.
              all: repeat (rewrite reveal_rawexpr_cps_id; set (reveal_rawexpr _)).
              all: repeat match goal with H := reveal_rawexpr _ |- _ => subst H end.
              all: repeat first [ progress cbn [fold_right Option.sequence Option.sequence_return fst snd] in *
                                | progress subst
                                | reflexivity
                                | rewrite IHd
                                | rewrite IHapp_case
                                | rewrite IHicase
                                | break_innermost_match_step
                                | progress intros
                                | solve [ auto ]
                                | progress break_match
                                | progress cbv [Option.bind option_bind'] in * ]. }
            { let d := match goal with d : decision_tree |- _ => d end in
              specialize (eval_decision_tree_cont_None_ext d); rename eval_decision_tree_cont_None_ext into IHd.
              repeat first [ break_innermost_match_step
                           | rewrite IHd
                           | solve [ auto ]
                           | progress intros ]. }
          Qed.

          Lemma eval_decision_tree_cont_None {var} {T ctx d}
            : @eval_decision_tree var T ctx d (fun _ _ => None) = None.
          Proof using Type. apply eval_decision_tree_cont_None_ext; reflexivity. Qed.

          Fixpoint wf_eval_decision_tree' {T1 T2} G d (P : option T1 -> option T2 -> Prop) (HPNone : P None None) {struct d}
            : forall (ctx1 : list (@rawexpr var1))
                     (ctx2 : list (@rawexpr var2))
                     (ctxe : list { t : type & @expr var1 t * @expr var2 t }%type)
                     (Hctx1 : length ctx1 = length ctxe)
                     (Hctx2 : length ctx2 = length ctxe)
                     (Hwf : forall t re1 e1 re2 e2,
                         List.In ((re1, re2), existT _ t (e1, e2)) (List.combine (List.combine ctx1 ctx2) ctxe)
                         -> @wf_rawexpr G t re1 e1 re2 e2)
                     cont1 cont2
                     (Hcont : forall n ls1 ls2,
                         length ls1 = length ctxe
                         -> length ls2 = length ctxe
                         -> (forall t re1 e1 re2 e2,
                                List.In ((re1, re2), existT _ t (e1, e2)) (List.combine (List.combine ls1 ls2) ctxe)
                                -> @wf_rawexpr G t re1 e1 re2 e2)
                         -> (cont1 n ls1 = None <-> cont2 n ls2 = None)
                            /\ P (cont1 n ls1) (cont2 n ls2)),
              ((@eval_decision_tree var1 T1 ctx1 d cont1) = None <-> (@eval_decision_tree var2 T2 ctx2 d cont2) = None)
              /\ P (@eval_decision_tree var1 T1 ctx1 d cont1) (@eval_decision_tree var2 T2 ctx2 d cont2).
          Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct.
            clear -HPNone raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct wf_eval_decision_tree'.
            specialize (fun d => wf_eval_decision_tree' T1 T2 G d P HPNone).
            destruct d; cbn [eval_decision_tree]; intros; try (clear wf_eval_decision_tree'; tauto).
            { let d := match goal with d : decision_tree |- _ => d end in
              specialize (wf_eval_decision_tree' d).
              cbv [Option.sequence Option.bind Option.sequence_return];
                break_innermost_match;
                specialize_all_ways;
                handle_swap_list;
                repeat first [ assumption
                             | match goal with
                               | [ H : ?T, H' : ?T |- _ ] => clear H'
                               end
                             | progress inversion_option
                             | progress destruct_head'_and
                             | progress destruct_head' iff
                             | progress specialize_by_assumption
                             | progress cbn [length] in *
                             | match goal with
                               | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                               | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                               | [ H : length ?x = length ?y, H' : context[length ?x] |- _ ] => rewrite H in H'
                               | [ H : S _ = S _ |- _ ] => inversion H; clear H
                               | [ H : S _ = length ?ls |- _ ] => is_var ls; destruct ls; cbn [length] in H; inversion H; clear H
                               end
                             | congruence
                             | apply conj
                             | progress intros
                             | progress destruct_head'_or ]. }
            { let d := match goal with d : decision_tree |- _ => d end in
              pose proof (wf_eval_decision_tree' d) as IHd.
              let d := match goal with d : option decision_tree |- _ => d end in
              pose proof (match d as d' return match d' with Some _ => _ | None => True end with
                          | Some d => wf_eval_decision_tree' d
                          | None => I
                          end) as IHapp_case.
              all: destruct ctx1, ctx2; cbn [length] in *; try (clear wf_eval_decision_tree'; (tauto || congruence)); [].
              all: lazymatch goal with
                   | [ |- _
                          /\ ?P match ?d with
                                | TryLeaf _ _ => (?res1 ;; ?ev1)%option
                                | _ => _
                                end
                              match ?d with
                              | TryLeaf _ _ => (?res2 ;; ?ev2)%option
                              | _ => _
                              end ]
                     => cut (((res1 = None <-> res2 = None) /\ P res1 res2) /\ ((ev1 = None <-> ev2 = None) /\ P ev1 ev2));
                          [ clear wf_eval_decision_tree';
                            intro; destruct_head'_and; destruct_head' iff;
                            destruct d; destruct res1 eqn:?, res2 eqn:?; cbn [Option.sequence];
                            solve [ intuition (congruence || eauto) ] | ]
                   end.
              all: split; [ | clear wf_eval_decision_tree'; eapply IHd; eassumption ].
              (** We use the trick that [induction] inside [Fixpoint]
                  gives us nested [fix]es that pass the guarded
                  checker, as long as we're careful about how we do
                  things *)
              let icases := match goal with d : list (_ * decision_tree) |- _ => d end in
              induction icases as [|icase icases IHicases];
                [ | pose proof (wf_eval_decision_tree' (snd icase)) as IHicase ];
                clear wf_eval_decision_tree'.
              (** now we can stop being super-careful about [destruct]
                  ordering because, if we're [Guarded] here (which we
                  are), then we cannot break guardedness from this
                  point on, because we've cleared the bare fixpoint
                  after specializing it to valid arguments *)
              2: revert IHicases.
              all: repeat (rewrite reveal_rawexpr_cps_id; set (reveal_rawexpr _)).
              all: repeat match goal with H := reveal_rawexpr _ |- _ => subst H end.
              all:repeat first [ match goal with
                                 | [ H : S _ = S _ |- _ ] => inversion H; clear H
                                 | [ H : S _ = length ?ls |- _ ] => is_var ls; destruct ls; cbn [length] in H; inversion H; clear H
                                 | [ H : forall t re1 e1 re2 e2, _ = _ \/ _ -> _ |- _ ]
                                   => pose proof (H _ _ _ _ _ (or_introl eq_refl));
                                      specialize (fun t re1 e1 re2 e2 pf => H t re1 e1 re2 e2 (or_intror pf))
                                 | [ H : wf_rawexpr ?G ?r ?e ?r' ?e' |- context[reveal_rawexpr ?r] ]
                                   => apply wf_reveal_rawexpr in H; revert H;
                                      generalize (reveal_rawexpr r) (reveal_rawexpr r'); clear r r'; intros r r' H; destruct H
                                 | [ H1 : length ?ctx1 = length ?ctxe', H2 : length ?ctx2 = length ?ctxe', H1' : wf_rawexpr _ ?f1 ?f1e ?f2 ?f2e, H2' : wf_rawexpr _ ?x1 ?x1e ?x2 ?x2e
                                     |- _ /\ ?P (@eval_decision_tree _ _ (?f1 :: ?x1 :: ?ctx1) _ _)
                                              (@eval_decision_tree _ _ (?f2 :: ?x2 :: ?ctx2) _ _) ]
                                   => apply IHapp_case with (ctxe:=existT _ _ (f1e, f2e) :: existT _ _ (x1e, x2e) :: ctxe'); clear IHapp_case
                                 | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                                 | [ H : ?x = ?x |- _ ] => clear H
                                 | [ |- context [raw_pident_to_typed_invert_bind_args_type ?t ?idc ?p ?f ?pf] ]
                                   => generalize (raw_pident_is_simple p) (type_of_raw_pident p f) (raw_pident_to_typed_invert_bind_args_type t idc p f pf); clear p f pf; intros; subst
                                 end
                               | tauto
                               | progress subst
                               | progress cbn [length combine List.In fold_right fst snd projT1 projT2 eq_rect Option.sequence Option.sequence_return eq_rect] in *
                               | progress inversion_sigma
                               | progress inversion_prod
                               | progress destruct_head'_sigT
                               | progress destruct_head'_prod
                               | progress destruct_head'_and
                               | progress destruct_head' iff; progress specialize_by (exact eq_refl)
                               | congruence
                               | match goal with
                                 | [ |- context[invert_bind_args_unknown] ]
                                   => rewrite !invert_bind_args_unknown_correct
                                 | [ H : context[invert_bind_args_unknown] |- _ ]
                                   => rewrite !invert_bind_args_unknown_correct in H
                                 end
                               | rewrite !eval_decision_tree_cont_None
                               | break_innermost_match_step
                               | progress intros
                               | progress destruct_head'_or
                               | solve [ auto ]
                               | match goal with
                                 | [ |- wf_rawexpr _ _ _ _ _ ] => constructor
                                 | [ H : context[(_ = None <-> _ = None) /\ ?P _ _] |- (_ = None <-> _ = None) /\ ?P _ _ ]
                                   => apply H
                                 | [ H : fold_right _ None ?ls = None, H' : fold_right _ None ?ls = Some None |- _ ]
                                   => exfalso; clear -H H'; is_var ls; destruct ls; cbn [fold_right] in H, H'; break_match_hyps; congruence
                                 end
                               | progress break_match
                               | progress cbv [option_bind' Option.bind]
                               | unshelve erewrite raw_pident_to_typed_invert_bind_args; [ shelve | shelve | eassumption | ]
                               | match goal with
                                 | [ |- _ /\ ?P (Option.sequence ?x ?y) (Option.sequence ?x' ?y') ]
                                   => cut ((x = None <-> x' = None) /\ P x x');
                                      [ destruct x, x'; cbn [Option.sequence]; solve [ intuition congruence ] | ]
                                 | [ H1 : length ?ctx1 = length ?ctxe', H2 : length ?ctx2 = length ?ctxe'
                                     |- _ /\ ?P (@eval_decision_tree _ _ ?ctx1 _ _) (@eval_decision_tree _ _ ?ctx2 _ _) ]
                                   => apply IHicase with (ctxe := ctxe'); auto
                                 end ]. }
            { let d := match goal with d : decision_tree |- _ => d end in
              specialize (wf_eval_decision_tree' d); rename wf_eval_decision_tree' into IHd.
              break_innermost_match; handle_swap_list; try tauto; [].
              lazymatch goal with
              | [ H : swap_list ?i ?j _ = _ |- _ ] => destruct (swap_list i j ctxe) as [ctxe'|] eqn:?
              end; handle_swap_list; [].
              eapply IHd with (ctxe:=ctxe'); clear IHd; try congruence;
                [ | intros; break_innermost_match; handle_swap_list; apply Hcont; try congruence; [] ]; clear Hcont.
              all: intros ? ? ? ? ? HIn.
              1: eapply Hwf; clear Hwf.
              2: lazymatch goal with
                 | [ H : context[List.In _ (combine _ ctxe') -> wf_rawexpr _ _ _ _ _] |- _ ] => apply H; clear H
                 end.
              all: apply In_nth_error_value in HIn; destruct HIn as [n' HIn].
              all: lazymatch goal with
                   | [ H : swap_list ?i ?j _ = _ |- _ ]
                     => apply nth_error_In with (n:=if Nat.eq_dec i n' then j else if Nat.eq_dec j n' then i else n')
                   end.
              all: repeat first [ reflexivity
                                | match goal with
                                  | [ H : context[nth_error (combine _ _) _] |- _ ] => rewrite !nth_error_combine in H
                                  | [ |- context[nth_error (combine _ _) _] ] => rewrite !nth_error_combine
                                  | [ H : swap_list _ _ ?ls = Some ?ls', H' : context[nth_error ?ls' ?k] |- _ ]
                                    => rewrite (nth_error_swap_list H) in H'
                                  | [ H : nth_error ?ls ?k = _, H' : context[nth_error ?ls ?k] |- _ ] => rewrite H in H'
                                  end
                                | progress subst
                                | progress inversion_option
                                | progress inversion_prod
                                | congruence
                                | progress handle_nth_error
                                | break_innermost_match_step
                                | break_innermost_match_hyps_step ]. }
          Qed.

          Lemma wf_eval_decision_tree {T1 T2} G d (P : option T1 -> option T2 -> Prop) (HPNone : P None None)
            : forall (ctx1 : list (@rawexpr var1))
                     (ctx2 : list (@rawexpr var2))
                     (ctxe : list { t : type & @expr var1 t * @expr var2 t }%type)
                     (Hctx1 : length ctx1 = length ctxe)
                     (Hctx2 : length ctx2 = length ctxe)
                     (Hwf : forall t re1 e1 re2 e2,
                         List.In ((re1, re2), existT _ t (e1, e2)) (List.combine (List.combine ctx1 ctx2) ctxe)
                         -> @wf_rawexpr G t re1 e1 re2 e2)
                     cont1 cont2
                     (Hcont : forall n ls1 ls2,
                         length ls1 = length ctxe
                         -> length ls2 = length ctxe
                         -> (forall t re1 e1 re2 e2,
                                List.In ((re1, re2), existT _ t (e1, e2)) (List.combine (List.combine ls1 ls2) ctxe)
                                -> @wf_rawexpr G t re1 e1 re2 e2)
                         -> (cont1 n ls1 = None <-> cont2 n ls2 = None)
                            /\ P (cont1 n ls1) (cont2 n ls2)),
              P (@eval_decision_tree var1 T1 ctx1 d cont1) (@eval_decision_tree var2 T2 ctx2 d cont2).
          Proof using raw_pident_to_typed_invert_bind_args invert_bind_args_unknown_correct. intros; eapply wf_eval_decision_tree'; eassumption. Qed.


          Local Ltac do_eq_type_of_rawexpr_of_wf :=
            repeat first [ match goal with
                           | [ |- context[rew [fun t => UnderLets ?var (@?P t)] ?pf in UnderLets.Base ?v] ]
                             => rewrite <- (fun x y p => @Equality.ap_transport _ P (fun t => UnderLets var (P t)) x y p (fun _ => UnderLets.Base))
                           | [ |- UnderLets.wf _ _ _ _ ] => constructor
                           | [ |- (?x = ?x <-> ?y = ?y) /\ _ ] => split; [ tauto | ]
                           end
                         | apply wf_expr_of_wf_rawexpr' ].
          Local Ltac solve_eq_type_of_rawexpr_of_wf := solve [ do_eq_type_of_rawexpr_of_wf ].

          Local Ltac gen_do_eq_type_of_rawexpr_of_wf :=
            match goal with
            | [ |- context[eq_type_of_rawexpr_of_wf ?Hwf] ]
              => let H' := fresh in
                 pose proof (wf_expr_of_wf_rawexpr Hwf) as H';
                 rewrite <- (proj1 (eq_expr_of_rawexpr_of_wf Hwf)),  <- (proj2 (eq_expr_of_rawexpr_of_wf Hwf)) in H';
                 destruct Hwf; cbn in H'; cbn [eq_type_of_rawexpr_of_wf eq_rect expr_of_rawexpr type_of_rawexpr]
            end.

          (* move me? *)
          Local Lemma ap_transport_splice {var T}
                (A B : T -> Type)
                (x y : T) (p : x = y)
                (v : @UnderLets var (A x)) (f : A x -> @UnderLets var (B x))
            : (rew [fun t => @UnderLets var (B t)] p in UnderLets.splice v f)
              = UnderLets.splice (rew [fun t => @UnderLets var (A t)] p in v)
                                 (fun v => rew [fun t => @UnderLets var (B t)] p in f (rew [A] (eq_sym p) in v)).
          Proof. case p; reflexivity. Defined.

          Local Lemma ap_transport_Base {var T}
                (A : T -> Type)
                (x y : T) (p : x = y)
                (v : A x)
            : (rew [fun t => @UnderLets var (A t)] p in UnderLets.Base v)
              = UnderLets.Base (rew [A] p in v).
          Proof. case p; reflexivity. Defined.

          Local Notation rewrite_rules_goodT := (@rewrite_rules_goodT ident pident pident_arg_types type_vars_of_pident var1 var2).
          Local Notation wf_rewrite_rule_data := (@wf_rewrite_rule_data ident pident pident_arg_types type_vars_of_pident var1 var2).
          Local Notation wf_reflect := (@wf_reflect ident var1 var2).
          Local Notation wf_reify := (@wf_reify ident var1 var2).

          Local Ltac fin_t_common_step :=
            first [ match goal with
                    | [ |- (Some _ = None <-> Some _ = None) /\ _ ] => split; [ clear; solve [ intuition congruence ] | ]
                    | [ |- (?x = ?x <-> ?y = ?y) /\ _ ] => split; [ clear; intuition congruence | ]
                    end ].
          Local Ltac handle_lists_of_rewrite_rules :=
            repeat first [ match goal with
                           | [ Hrew : length _ = length _, H : nth_error _ _ = None, H' : nth_error _ _ = Some _ |- _ ]
                             => exfalso; rewrite nth_error_None in H;
                                apply nth_error_value_length in H';
                                clear -Hrew H H'; try lia
                           | [ H : O = S _ |- _ ] => exfalso; clear -H; congruence
                           | [ H : S _ = O |- _ ] => exfalso; clear -H; congruence
                           end
                         | progress cbv [rewrite_ruleT] in * (* so the nth_error rewrite lines up *)
                         | progress cbn [List.length List.combine List.In Option.bind] in *
                         | match goal with
                           | [ H : S _ = S _ |- _ ] => inversion H; clear H
                           | [ H : length ?ls = O |- _ ] => is_var ls; destruct ls; [ | exfalso; clear -H ]
                           | [ H : length ?ls = S _ |- _ ] => is_var ls; destruct ls; [ exfalso; clear -H | ]
                           | [ H : ?x = ?x |- _ ] => clear H
                           | [ H : forall a b c d e, _ = _ \/ False -> _ |- _ ] => specialize (H _ _ _ _ _ (or_introl eq_refl))
                           | [ |- context[@nth_error ?A ?ls ?n] ] => destruct (@nth_error A ls n) eqn:?
                           | [ H : forall a b c d, In _ _ -> _, H' : nth_error _ ?n = Some _ |- _ ]
                             => specialize (fun a b c d pf => H a b c d (@nth_error_In _ _ n _ pf))
                           | [ H : forall a b, In _ _ -> _, H' : nth_error _ ?n = Some _ |- _ ]
                             => specialize (fun a b pf => H a b (@nth_error_In _ _ n _ pf))
                           | [ H : context[nth_error (combine ?l1 ?l2) ?n] |- _ ]
                             => rewrite (@nth_error_combine _ _ n) in H
                           | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                           | [ H : forall a b c d, Some _ = Some _ -> _ |- _ ] => specialize (H _ _ _ _ eq_refl)
                           | [ H : forall a b, Some _ = Some _ -> _ |- _ ] => specialize (H _ _ eq_refl)
                           end
                         | progress intros
                         | progress destruct_head'_sigT
                         | fin_t_common_step ].
          Local Ltac cleanup_after_lists_step :=
            first [ progress subst
                  | progress destruct_head'_sig
                  | progress cbn [eq_rect] in * ].
          Local Ltac clear_lists_of_rewrite_rules :=
            match goal with
            | [ H : length ?ls1 = length ?ls2, H' : nth_error ?ls1 ?n = Some _, H'' : nth_error ?ls2 ?n = Some _ |- _ ]
              => clear ls1 ls2 n H H' H''
            end;
            repeat cleanup_after_lists_step.

          Local Ltac try_solve_by_type_of_rawexpr_eqn :=
            match goal with H : _ <> _ |- _ => idtac end;
            exfalso;
            repeat match goal with
                   | [ H : ?T |- _ ]
                     => lazymatch T with
                        | _ = _ :> type.type _ => fail
                        | _ <> _ => fail
                        | _ => clear H
                        end
                   | [ H : context[type_of_rawexpr ?r] |- _ ]
                     => generalize dependent (type_of_rawexpr r); clear r; intros
                   | [ H : ?x = ?y |- _ ] => subst x || subst y
                   end;
            try congruence.

          Lemma wf_eval_rewrite_rules
                (do_again1 : forall t : base.type, @expr.expr base.type ident (@value var1) t -> @UnderLets var1 (@expr var1 t))
                (do_again2 : forall t : base.type, @expr.expr base.type ident (@value var2) t -> @UnderLets var2 (@expr var2 t))
                (wf_do_again : forall G (t : base.type) e1 e2,
                    (exists G', (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> Compile.wf_value G v1 v2) /\ expr.wf G' e1 e2)
                    -> UnderLets.wf (fun G' => expr.wf G') G (@do_again1 t e1) (@do_again2 t e2))
                (d : @decision_tree raw_pident)
                (rew1 : rewrite_rulesT1) (rew2 : rewrite_rulesT2)
                (Hrew : rewrite_rules_goodT rew1 rew2)
                (re1 : @rawexpr var1) (re2 : @rawexpr var2)
                {t} G e1 e2
                (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : UnderLets.wf
                (fun G' => expr.wf G')
                G
                (rew [fun t => @UnderLets var1 (expr t)] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in (eval_rewrite_rules1 do_again1 d rew1 re1))
                (rew [fun t => @UnderLets var2 (expr t)] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in (eval_rewrite_rules2 do_again2 d rew2 re2)).
          Proof using invert_bind_args_unknown_correct pident_unify_unknown_correct raw_pident_to_typed_invert_bind_args.
            cbv [eval_rewrite_rules Option.sequence_return rewrite_with_rule].
            cbv [rewrite_rules_goodT] in Hrew.
            eapply wf_eval_decision_tree with (ctxe:=[existT _ t (e1, e2)]);
              cbn [length combine];
              try solve [ reflexivity
                        | cbn [combine In]; wf_t; tauto ].
            all: split_and.
            Time all: repeat first [ progress do_eq_type_of_rawexpr_of_wf
                                   | handle_lists_of_rewrite_rules ].
            clear_lists_of_rewrite_rules.
            Time all: repeat first [ fin_t_common_step
                                   | match goal with
                                     | [ H : wf_rawexpr ?G _ _ _ _, H' : forall G', wf_rewrite_rule_data G' _ _ |- _ ] => specialize (H' G)
                                     | [ |- context[rew [fun t => @UnderLets ?varp (@?P t)] ?pf in (@UnderLets.splice ?base_type ?ident ?var ?A ?B ?a ?b)] ]
                                       => rewrite (@ap_transport_splice varp _ (fun _ => _) P _ _ pf a b
                                                   : (rew [fun t => @UnderLets varp (P t)] pf in (@UnderLets.splice base_type ident var A B a b)) = _)
                                     | [ |- context[rew [fun t => @UnderLets ?varp (@?P t)] ?pf in (@UnderLets.Base ?base_type ?ident ?var ?T ?a)] ]
                                       => rewrite ap_transport_Base
                                     | [ |- True ] => exact I
                                     end
                                   | progress cbv [wf_rewrite_rule_data wf_with_unif_rewrite_ruleTP_gen option_bind' normalize_deep_rewrite_rule_cps_id_hypsT] in *
                                   | lazymatch goal with
                                     | [ |- (@unify_pattern1 ?t ?re1 ?p ?K1 ?v1 ?T1 ?cont1 = None
                                             <-> @unify_pattern2 ?t ?re2 ?p ?K2 ?v2 ?T2 ?cont2 = None)
                                            /\ _ ]
                                       => let H := fresh in
                                          pose proof (fun PK PT => @wf_unify_pattern _ t _ p re1 re2 _ _ K1 K2 PK T1 T2 PT v1 v2 cont1 cont2 ltac:(eassumption)) as H;
                                            specialize (fun PK pf PT => H PK PT pf);
                                            cbv beta in *;
                                            (* grumble grumble dependent type hacking *)
                                            lazymatch type of H with
                                            | forall PK, wf_with_unification_resultT ?G (fun evm : ?EVM => PK (?t evm)) ?v1 ?v2 -> _
                                              => lazymatch goal with
                                                 | [ H0 : wf_with_unification_resultT G (fun evm : EVM => ?PK') v1 v2 |- _ ]
                                                   => let PK'' := fresh in
                                                      let PK'
                                                          := constr:(
                                                               fun evm : EVM
                                                               => match PK' with
                                                                  | PK''
                                                                    => ltac:(
                                                                         let PK' := (eval cbv delta [PK''] in PK'') in
                                                                         let PK' := match (eval pattern (t evm) in PK') with ?PK' _ => PK' end in
                                                                         exact PK'
                                                                       )
                                                                  end) in
                                                      let PK' := lazymatch PK' with (fun _ => ?f) => f end in
                                                      specialize (H PK' H0)
                                                 end
                                            end;
                                            (* end grumbling *)
                                            (*rewrite unify_pattern_cps_id with (var:=var1), unify_pattern_cps_id with (var:=var2) in H |- *;*)
                                            (destruct (@unify_pattern1 t re1 p K1 v1 T1 cont1) eqn:?,
                                                      (@unify_pattern2 t re2 p K2 v2 T2 cont2) eqn:?);
                                            cbn [Option.bind option_eq pattern.type_of_anypattern pattern.pattern_of_anypattern] in H |- *;
                                            [ split; [ clear; split | apply H; clear H ]
                                            | refine ((fun pf => _) _); [ exfalso | eapply (H (fun _ _ => True)) ]; [ (assumption || discriminate) | clear H ]..
                                            | ]
                                     | [ H : wf_deep_rewrite_ruleTP_gen _ _ _ |- option_eq ?R (normalize_deep_rewrite_rule _ _ (fun x => x)) (normalize_deep_rewrite_rule _ _ (fun y => y)) ]
                                       => exact (wf_normalize_deep_rewrite_rule H)
                                     | [ |- option_eq _ (normalize_deep_rewrite_rule _ _ _) (normalize_deep_rewrite_rule _ _ _) ]
                                       => rewrite @normalize_deep_rewrite_rule_cps_id with (var:=var1), @normalize_deep_rewrite_rule_cps_id with (var:=var2)
                                     | [ |- ?x = ?x ] => reflexivity
                                     end
                                   | progress intros
                                   | progress cbn [Option.bind option_eq eq_rect eq_sym eq_trans] in *
                                   | progress inversion_option
                                   | progress subst
                                   | match goal with
                                     | [ |- UnderLets.wf _ _ _ _ ] => constructor
                                     | [ |- expr.wf _ (rew _ in expr_of_rawexpr _) (rew _ in expr_of_rawexpr _) ]
                                       => apply wf_expr_of_wf_rawexpr'
                                     | [ H : wf_deep_rewrite_ruleTP_gen _ _ _ |- option_eq ?R (normalize_deep_rewrite_rule _ _ (fun x => x)) (normalize_deep_rewrite_rule _ _ (fun y => y)) ]
                                       => exact (wf_normalize_deep_rewrite_rule H)
                                     | [ H : wf_deep_rewrite_ruleTP_gen _ _ _ |- (match ?b with true => _ | false => _ end) _ ]
                                       => clear -H;
                                            solve [
                                                destruct_head' (@rewrite_ruleTP);
                                                  repeat first [ exact I
                                                               | exfalso; assumption
                                                               | progress cbn [Compile.rew_should_do_again Compile.rew_under_lets Compile.rew_is_cps Compile.rew_with_opt Compile.rew_replacement] in *
                                                               | progress destruct_head'_bool
                                                               | progress cbv [wf_deep_rewrite_ruleTP_gen] in *
                                                               | progress destruct_head'_and
                                                               | solve [ auto ]
                                                               | progress destruct_head' (@eq) ]
                                              ]
                                     end
                                   | progress cbv [type.try_transport_cps(* type.try_make_transport_cps*)]
                                   | lazymatch goal with
                                     | [ |- context[type.try_make_transport_cps] ]
                                       => progress rewrite_type_transport_correct
                                     | [ |- context[base.try_make_transport_cps] ]
                                       => progress rewrite_type_transport_correct
                                     end
                                   | match goal with
                                     | [ |- context[match Sumbool.sumbool_of_bool ?b with _ => _ end] ]
                                       => destruct (Sumbool.sumbool_of_bool b)
                                     | [ H : wf_rawexpr _ _ _ _ _ |- _ ]
                                       => let lem1 := constr:(proj1 (eq_type_of_rawexpr_of_wf H)) in
                                          let lem2 := constr:(proj2 (eq_type_of_rawexpr_of_wf H)) in
                                          progress (lazymatch type of lem1 with
                                                    | ?x = ?x => idtac
                                                    | _ => try (unique pose proof lem1)
                                                    end;
                                                      lazymatch type of lem2 with
                                                      | ?x = ?x => idtac
                                                      | _ => try (unique pose proof lem2)
                                                      end)
                                     | [ |- context[Option.bind _ (fun _ => None)] ] => rewrite !Option.bind_zero_r
                                     end
                                   | progress type_beq_to_eq
                                   | solve [ try_solve_by_type_of_rawexpr_eqn ]
                                   | match goal with
                                     | [ H : unify_pattern1 _ _ _ _ _ = _ |- _ ] => clear H
                                     | [ H : unify_pattern2 _ _ _ _ _ = _ |- _ ] => clear H
                                     | [ H : ?x = ?x |- _ ] => clear H
                                     | [ |- option_eq _ (Option.bind _ _) (Option.bind _ _) ]
                                       => repeat match goal with
                                                 | [ H : type_of_rawexpr _ = type_of_rawexpr _ |- _ ]
                                                   => lazymatch goal with
                                                      | [ |- context[H] ] => destruct H
                                                      | [ H' : context[H] |- _ ] => destruct H
                                                      end
                                                 end;
                                            eapply Option.bind_Proper_option_eq_hetero
                                     | [ |- context[rew ?pf in _] ]
                                       => lazymatch pf with
                                          | context[eq_type_of_rawexpr_of_wf] => destruct pf
                                          end
                                     | [ |- UnderLets.wf _ _ (UnderLets.splice _ _) (UnderLets.splice _ _) ]
                                       => eapply UnderLets.wf_splice; [ eauto | ]; revgoals
                                     | [ H : ?T |- _ ] => has_evar T; solve [ unshelve refine H ]
                                     end ].
            (* Now we solve the final goal about [maybe_do_again] *)
            repeat first [ progress destruct_head'_False
                         | progress type.inversion_type
                         | progress eliminate_hprop_eq
                         | break_innermost_match_step
                         | progress cbv [id] in *
                         | match goal with
                           | [ H : wf_maybe_do_again_expr _ ?v _ |- context[?v] ] => clear -H wf_do_again; cbv [wf_maybe_do_again_expr maybe_do_again] in *
                           | [ |- UnderLets.wf _ _ _ _ ] => constructor
                           end
                         | progress destruct_head (@rewrite_ruleTP)
                         | solve [ eauto ] ].
          Qed.

          Section with_do_again.
            Context (dtree : @decision_tree raw_pident)
                    (rew1 : rewrite_rulesT1)
                    (rew2 : rewrite_rulesT2)
                    (Hrew : rewrite_rules_goodT rew1 rew2)
                    (do_again1 : forall t : base.type, @expr.expr base.type ident (@value var1) t -> @UnderLets var1 (@expr var1 t))
                    (do_again2 : forall t : base.type, @expr.expr base.type ident (@value var2) t -> @UnderLets var2 (@expr var2 t))
                    (wf_do_again : forall G G' (t : base.type) e1 e2,
                        (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> Compile.wf_value G v1 v2)
                        -> expr.wf G' e1 e2
                        -> UnderLets.wf (fun G' => expr.wf G') G (@do_again1 t e1) (@do_again2 t e2)).

            Local Notation assemble_identifier_rewriters' var := (@assemble_identifier_rewriters' ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple dtree).
            Local Notation assemble_identifier_rewriters var := (@assemble_identifier_rewriters ident var eta_ident_cps pident pident_arg_types pident_unify pident_unify_unknown raw_pident type_vars_of_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple dtree).

            Lemma wf_assemble_identifier_rewriters' G t re1 e1 re2 e2
                  K1 K2
                  (He : @wf_rawexpr G t re1 e1 re2 e2)
                  (HK1 : forall P v, K1 P v = rew [P] (proj1 (eq_type_of_rawexpr_of_wf He)) in v)
                  (HK2 : forall P v, K2 P v = rew [P] (proj2 (eq_type_of_rawexpr_of_wf He)) in v)
              : wf_value_with_lets
                  G
                  (@assemble_identifier_rewriters' var1 rew1 do_again1 t re1 K1)
                  (@assemble_identifier_rewriters' var2 rew2 do_again2 t re2 K2).
            Proof.
              revert dependent G; revert dependent re1; revert dependent re2; induction t as [t|s IHs d IHd];
                intros; cbn [assemble_identifier_rewriters'].
              { rewrite HK1, HK2; apply wf_eval_rewrite_rules; try assumption.
                intros; destruct_head'_ex; destruct_head'_and; eauto. }
              { hnf; intros; subst.
                unshelve eapply IHd; cbn [type_of_rawexpr]; [ shelve | shelve | constructor | cbn; reflexivity | cbn; reflexivity ].
                all: rewrite ?HK1, ?HK2.
                { erewrite (proj1 (eq_expr_of_rawexpr_of_wf He)), (proj2 (eq_expr_of_rawexpr_of_wf He)).
                  eapply wf_rawexpr_Proper_list; [ | eassumption ]; wf_t. }
                { cbv [rValueOrExpr2]; break_innermost_match; constructor;
                  try apply wf_reify;
                  (eapply wf_value'_Proper_list; [ | eassumption ]); wf_t. } }
            Qed.

            Lemma wf_assemble_identifier_rewriters G t (idc : ident t)
              : wf_value_with_lets
                  G
                  (@assemble_identifier_rewriters var1 rew1 do_again1 t idc)
                  (@assemble_identifier_rewriters var2 rew2 do_again2 t idc).
            Proof.
              cbv [assemble_identifier_rewriters]; rewrite !eta_ident_cps_correct.
              unshelve eapply wf_assemble_identifier_rewriters'; [ shelve | shelve | constructor | | ]; reflexivity.
            Qed.
          End with_do_again.
        End with_var2.
      End with_type.

      Section full_with_var2.
        Context {var1 var2 : type.type base.type -> Type}.
        Local Notation expr := (@expr.expr base.type ident).
        Local Notation value := (@Compile.value base.type ident).
        Local Notation value_with_lets := (@Compile.value_with_lets base.type ident).
        Local Notation UnderLets := (UnderLets.UnderLets base.type ident).
        Local Notation reflect := (@Compile.reflect ident).
        Section with_rewrite_head.
          Context (rewrite_head1 : forall t (idc : ident t), @value_with_lets var1 t)
                  (rewrite_head2 : forall t (idc : ident t), @value_with_lets var2 t)
                  (wf_rewrite_head : forall G t (idc1 idc2 : ident t),
                      idc1 = idc2 -> wf_value_with_lets G (rewrite_head1 t idc1) (rewrite_head2 t idc2)).

          Local Notation rewrite_bottomup1 := (@rewrite_bottomup var1 rewrite_head1).
          Local Notation rewrite_bottomup2 := (@rewrite_bottomup var2 rewrite_head2).

          Lemma wf_rewrite_bottomup G G' {t} e1 e2 (Hwf : expr.wf G e1 e2)
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2)
            : wf_value_with_lets G' (@rewrite_bottomup1 t e1) (@rewrite_bottomup2 t e2).
          Proof.
            revert dependent G'; induction Hwf; intros; cbn [rewrite_bottomup].
            all: repeat first [ reflexivity
                              | solve [ eauto ]
                              | apply wf_rewrite_head
                              | apply wf_Base_value
                              | apply wf_splice_value_with_lets
                              | apply wf_splice_under_lets_with_value
                              | apply wf_reify_and_let_binds_cps
                              | apply UnderLets.wf_reify_and_let_binds_base_cps
                              | apply wf_reflect
                              | progress subst
                              | progress destruct_head'_ex
                              | progress cbv [wf_value_with_lets wf_value] in *
                              | progress cbn [wf_value' fst snd] in *
                              | progress intros
                              | wf_safe_t_step
                              | eapply wf_value'_Proper_list; [ | solve [ eauto ] ]
                              | match goal with
                                | [ |- UnderLets.wf _ _ _ _ ] => constructor
                                | [ H : _ |- _ ] => apply H; clear H
                                end ].
          Qed.
        End with_rewrite_head.

        Local Notation nbe var := (@rewrite_bottomup var (fun t idc => reflect (expr.Ident idc))).

        Lemma wf_nbe G G' {t} e1 e2
              (Hwf : expr.wf G e1 e2)
              (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2)
          : wf_value_with_lets G' (@nbe var1 t e1) (@nbe var2 t e2).
        Proof.
          eapply wf_rewrite_bottomup; try eassumption.
          intros; subst; eapply wf_reflect; wf_t.
        Qed.

        Section with_rewrite_head2.
          Context (rewrite_head1 : forall (do_again : forall t : base.type, @expr (@value var1) (type.base t) -> @UnderLets var1 (@expr var1 (type.base t)))
                                          t (idc : ident t), @value_with_lets var1 t)
                  (rewrite_head2 : forall (do_again : forall t : base.type, @expr (@value var2) (type.base t) -> @UnderLets var2 (@expr var2 (type.base t)))
                                          t (idc : ident t), @value_with_lets var2 t)
                  (wf_rewrite_head
                   : forall
                      do_again1
                      do_again2
                      (wf_do_again
                       : forall G' G (t : base.type) e1 e2
                                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
                          expr.wf G e1 e2
                          -> UnderLets.wf (fun G' => expr.wf G') G' (do_again1 t e1) (do_again2 t e2))
                      G t (idc1 idc2 : ident t),
                      idc1 = idc2 -> wf_value_with_lets G (rewrite_head1 do_again1 t idc1) (rewrite_head2 do_again2 t idc2)).

          Lemma wf_repeat_rewrite fuel
            : forall {t} G G' e1 e2
                     (Hwf : expr.wf G e1 e2)
                     (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
              wf_value_with_lets G' (@repeat_rewrite var1 rewrite_head1 fuel t e1) (@repeat_rewrite var2 rewrite_head2 fuel t e2).
          Proof.
            induction fuel as [|fuel IHfuel]; intros; cbn [repeat_rewrite]; eapply wf_rewrite_bottomup; try eassumption;
              apply wf_rewrite_head; intros; [ eapply wf_nbe with (t:=type.base _) | eapply IHfuel with (t:=type.base _) ];
                eassumption.
          Qed.

          Lemma wf_rewrite fuel
            : forall {t} G G' e1 e2
                     (Hwf : expr.wf G e1 e2)
                     (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
              expr.wf G' (@rewrite var1 rewrite_head1 fuel t e1) (@rewrite var2 rewrite_head2 fuel t e2).
          Proof. intros; eapply wf_reify, wf_repeat_rewrite; eassumption. Qed.
        End with_rewrite_head2.
      End full_with_var2.

      Theorem Wf_Rewrite
              (rewrite_head
               : forall var
                        (do_again : forall t : base.type, @expr (@value base.type ident var) (type.base t) -> @UnderLets.UnderLets base.type ident var (@expr var (type.base t)))
                        t (idc : ident t), @value_with_lets base.type ident var t)
              (wf_rewrite_head
               : forall
                  var1 var2
                  do_again1
                  do_again2
                  (wf_do_again
                   : forall G G' (t : base.type) e1 e2,
                      (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> Compile.wf_value G v1 v2)
                      -> expr.wf G' e1 e2
                      -> UnderLets.wf (fun G' => expr.wf G') G (do_again1 t e1) (do_again2 t e2))
                  t (idc : ident t),
                  wf_value_with_lets nil (rewrite_head var1 do_again1 t idc) (rewrite_head var2 do_again2 t idc))
              fuel {t} (e : Expr t) (Hwf : Wf e)
        : Wf (@Rewrite rewrite_head fuel t e).
      Proof.
        intros var1 var2; cbv [Rewrite]; eapply wf_rewrite with (G:=nil); [ | apply Hwf | wf_t ].
        intros; subst; eapply wf_value'_Proper_list; [ | eapply wf_rewrite_head ]; wf_t.
      Qed.
    End Compile.
  End RewriteRules.
End Compilers.
