Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.UnderLetsProofs.
Require Import Crypto.Language.IdentifiersLibrary.
Require Import Crypto.Language.IdentifiersLibraryProofs.
Require Import Crypto.Rewriter.Rewriter.
Require Import Crypto.Rewriter.ProofsCommon.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.CPSId.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Sigma.Related.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.Reflect.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import IdentifiersLibrary.Compilers.
  Import IdentifiersLibraryProofs.Compilers.
  Import Rewriter.Compilers.
  Import Rewriter.ProofsCommon.Compilers.
  Import expr.Notations.
  Import Rewriter.ProofsCommon.Compilers.RewriteRules.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    Module Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.
      Import Rewriter.ProofsCommon.Compilers.RewriteRules.Compile.

      Section with_type.
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation pbase_type := (pattern.base.type base).
        Local Notation type := (type.type base_type).
        Local Notation ptype := (type.type pbase_type).
        Local Notation type_of_list
          := (fold_right (fun a b => prod a b) unit).
        Local Notation type_of_list_cps
          := (fold_right (fun a K => a -> K)).
        Context {base_beq : base -> base -> bool}
                {reflect_base_beq : reflect_rel (@eq base) base_beq}
                {try_make_transport_base_cps : type.try_make_transport_cpsT base}
                {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}
                {ident : type -> Type}
                (eta_ident_cps : forall {T : type -> Type} {t} (idc : ident t)
                                        (f : forall t', ident t' -> T t'),
                    T t)
                {pident : ptype -> Type}
                (pident_arg_types : forall t, pident t -> list Type)
                (pident_unify pident_unify_unknown : forall t t' (idc : pident t) (idc' : ident t'), option (type_of_list (pident_arg_types t idc)))
                {raw_pident : Type}
                (strip_types : forall t, pident t -> raw_pident)
                (raw_pident_beq : raw_pident -> raw_pident -> bool)

                (full_types : raw_pident -> Type)
                (invert_bind_args invert_bind_args_unknown : forall t (idc : ident t) (pidc : raw_pident), option (full_types pidc))
                (type_of_raw_pident : forall (pidc : raw_pident), full_types pidc -> type)
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
                    raw_pident_to_typed p f = rew [ident] raw_pident_to_typed_invert_bind_args_type t idc p f pf in idc).
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation expr := (@expr.expr base_type ident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident).
        Local Notation value' := (@value' base_type ident).
        Local Notation value := (@value base_type ident).
        Local Notation value_with_lets := (@value_with_lets base_type ident).
        Local Notation Base_value := (@Base_value base_type ident).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base_type ident).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base_type ident).
        Local Notation reify := (@reify base ident).
        Local Notation reflect := (@reflect base ident).
        Local Notation rawexpr := (@rawexpr base ident).
        Local Notation eval_decision_tree var := (@eval_decision_tree base ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation reveal_rawexpr e := (@reveal_rawexpr_cps base ident _ e _ id).

        Let type_base (x : base) : @base.type base := base.type.type_base x.
        Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base' : base.type >-> type.type.
        Local Coercion type_base : base >-> base.type.

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Context (reify_and_let_binds_base_cps1 : forall (t : base_type), @expr var1 t -> forall T, (@expr var1 t -> @UnderLets var1 T) -> @UnderLets var1 T)
                  (reify_and_let_binds_base_cps2 : forall (t : base_type), @expr var2 t -> forall T, (@expr var2 t -> @UnderLets var2 T) -> @UnderLets var2 T)
                  (wf_reify_and_let_binds_base_cps
                   : forall G (t : base_type) x1 x2 T1 T2 P
                            (Hx : expr.wf G x1 x2)
                            (e1 : expr t -> @UnderLets var1 T1) (e2 : expr t -> @UnderLets var2 T2)
                            (He : forall x1 x2 G' seg, (G' = (seg ++ G)%list) -> expr.wf G' x1 x2 -> UnderLets.wf P G' (e1 x1) (e2 x2)),
                      UnderLets.wf P G (reify_and_let_binds_base_cps1 t x1 T1 e1) (reify_and_let_binds_base_cps2 t x2 T2 e2)).

          Local Notation wf_value' := (@wf_value' base_type ident var1 var2).
          Local Notation wf_value := (@wf_value base_type ident var1 var2).
          Local Notation wf_value_with_lets := (@wf_value_with_lets base_type ident var1 var2).
          Local Notation reify_and_let_binds_cps1 := (@reify_and_let_binds_cps base ident var1 reify_and_let_binds_base_cps1).
          Local Notation reify_and_let_binds_cps2 := (@reify_and_let_binds_cps base ident var2 reify_and_let_binds_base_cps2).
          Local Notation rewrite_rulesT1 := (@rewrite_rulesT base ident var1 pident pident_arg_types).
          Local Notation rewrite_rulesT2 := (@rewrite_rulesT base ident var2 pident pident_arg_types).
          Local Notation eval_rewrite_rules1 := (@eval_rewrite_rules base try_make_transport_base_cps base_beq ident var1 pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
          Local Notation eval_rewrite_rules2 := (@eval_rewrite_rules base try_make_transport_base_cps base_beq ident var2 pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
          Local Notation rewrite_rule_data1 := (@rewrite_rule_data base ident var1 pident pident_arg_types).
          Local Notation rewrite_rule_data2 := (@rewrite_rule_data base ident var2 pident pident_arg_types).
          Local Notation with_unif_rewrite_ruleTP_gen1 := (@with_unif_rewrite_ruleTP_gen base ident var1 pident pident_arg_types).
          Local Notation with_unif_rewrite_ruleTP_gen2 := (@with_unif_rewrite_ruleTP_gen base ident var2 pident pident_arg_types).
          Local Notation wf_rawexpr := (@wf_rawexpr base ident var1 var2).
          (** TODO: Move Me up *)
          Local Notation unify_pattern'1 := (@unify_pattern' base try_make_transport_base_cps ident var1 pident pident_arg_types pident_unify pident_unify_unknown).
          Local Notation unify_pattern'2 := (@unify_pattern' base try_make_transport_base_cps ident var2 pident pident_arg_types pident_unify pident_unify_unknown).
          Local Notation unify_pattern1 := (@unify_pattern base try_make_transport_base_cps base_beq ident var1 pident pident_arg_types pident_unify pident_unify_unknown).
          Local Notation unify_pattern2 := (@unify_pattern base try_make_transport_base_cps base_beq ident var2 pident pident_arg_types pident_unify pident_unify_unknown).
          Local Notation wf_unification_resultT' := (@wf_unification_resultT' base ident pident pident_arg_types var1 var2).
          Local Notation wf_unification_resultT := (@wf_unification_resultT base ident pident pident_arg_types var1 var2).
          Local Notation wf_with_unification_resultT := (@wf_with_unification_resultT base ident pident pident_arg_types var1 var2).
          Local Notation wf_with_unif_rewrite_ruleTP_gen := (@wf_with_unif_rewrite_ruleTP_gen base try_make_transport_base_cps ident pident pident_arg_types var1 var2).
          Local Notation wf_deep_rewrite_ruleTP_gen := (@wf_deep_rewrite_ruleTP_gen base ident var1 var2).
          Local Notation app_with_unification_resultT_cps1 := (@app_with_unification_resultT_cps base try_make_transport_base_cps pident pident_arg_types (@value var1)).
          Local Notation app_with_unification_resultT_cps2 := (@app_with_unification_resultT_cps base try_make_transport_base_cps pident pident_arg_types (@value var2)).
          Local Notation wf_app_with_unification_resultT := (@wf_app_with_unification_resultT base base_beq reflect_base_beq try_make_transport_base_cps try_make_transport_base_cps_correct ident pident pident_arg_types var1 var2).

          (* Because [proj1] and [proj2] in the stdlib are opaque *)
          Local Notation proj1 x := (let (a, b) := x in a).
          Local Notation proj2 x := (let (a, b) := x in b).

          Lemma wf_unify_pattern'
                {G : list { t : _ & (var1 t * var2 t)%type }}
                {t t'} {p : pattern t} {evm : EvarMap} {re1 re2 e1 e2}
                (He : @wf_rawexpr G t' re1 e1 re2 e2)
            : option_eq
                (wf_unification_resultT' G)
                (@unify_pattern'1 _ re1 p evm _ (@Some _))
                (@unify_pattern'2 _ re2 p evm _ (@Some _)).
          Proof using try_make_transport_base_cps_correct.
            revert t' e1 e2 re1 re2 He; induction p; intros; cbn [unify_pattern'].
            all: repeat first [ progress cbn [Option.bind eq_rect option_eq] in *
                              | assumption
                              | reflexivity
                              | exfalso; assumption
                              | progress subst
                              | progress rewrite_type_transport_correct
                              | progress type_beq_to_eq
                              | progress inversion_option
                              | match goal with
                                | [ H : @wf_rawexpr ?G ?t ?re1 ?e1 ?re2 ?e2 |- context[match ?re1 with _ => _ end] ]
                                  => is_var t; is_var re1; is_var e1; is_var re2; is_var e2; is_var G;
                                     destruct H
                                end
                              | break_innermost_match_step
                              | progress cps_id'_with_option unify_pattern'_cps_id
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
                                | [ He : wf_rawexpr ?G ?re1 _ ?re2 _
                                    |- wf_unification_resultT' ?G (rew ?pf in value_of_rawexpr ?re1) (rew ?pf2 in value_of_rawexpr ?re2) ]
                                  => apply (wf_value_of_wf_rawexpr_gen He)
                                | [ H : wf_rawexpr _ _ _ _ _ |- _ ]
                                  => progress (try (unique pose proof (proj1 (eq_type_of_rawexpr_of_wf H)));
                                               try (unique pose proof (proj2 (eq_type_of_rawexpr_of_wf H))))
                                | [ H : ?t1 <> ?t2 |- _ ]
                                  => exfalso; apply H; congruence
                                | [ |- context[(rew [?P] ?pf in ?f) ?v] ]
                                  => lazymatch P with
                                     | fun x : ?A => forall y : @?B x, @?C x y
                                       => replace ((rew [P] pf in f) v) with (rew [fun x : A => C x v] pf in f v)
                                         by (case pf; reflexivity)
                                     end
                                | [ H : (forall t e1 e2 re1 re2, wf_rawexpr _ _ _ _ _ -> option_eq _ (unify_pattern'1 re1 ?p1 ?evm _ (@Some _)) _)
                                    |- context[unify_pattern'1 ?re1' ?p1 ?evm _ (@Some _)] ]
                                  => specialize (H _ _ _ re1' _ ltac:(eassumption))
                                | [ H : option_eq ?R ?x ?y |- _ ]
                                  => destruct x eqn:?, y eqn:?; cbv [option_eq] in H
                                | [ |- wf_unification_resultT' _ (_, _) (_, _) ] => split; assumption
                                end
                              | progress cbv [Option.bind] in * ].
          Qed.

          Lemma wf_unify_pattern
                {G : list { t : _ & (var1 t * var2 t)%type }}
                {t t'} {p : pattern t} {re1 re2 e1 e2}
                (He : @wf_rawexpr G t' re1 e1 re2 e2)
            : option_eq
                (wf_unification_resultT G)
                (@unify_pattern1 t re1 p _ (@Some _))
                (@unify_pattern2 t re2 p _ (@Some _)).
          Proof using try_make_transport_base_cps_correct.
            cbv [unify_pattern wf_unification_resultT].
            cps_id'_with_option unify_types_cps_id.
            rewrite <- (wf_unify_types He).
            cbv [Option.bind]; break_innermost_match_step; [ | reflexivity ].
            cps_id'_with_option unify_pattern'_cps_id.
            pose proof (@wf_unify_pattern' G t t' p ltac:(assumption) re1 re2 e1 e2 He) as H'.
            match goal with
            | [ H : option_eq ?R ?x ?y |- _ ]
              => destruct x eqn:?, y eqn:?; cbv [option_eq] in H
            end; try solve [ reflexivity | inversion_option | exfalso; assumption ];
              cbn [Option.bind option_eq].
            cbv [related_unification_resultT related_sigT_by_eq]; exists eq_refl.
            cbn [eq_rect projT1 projT2].
            assumption.
          Qed.

          Lemma wf_normalize_deep_rewrite_rule
                {G}
                {t}
                {should_do_again1 with_opt1 under_lets1}
                {should_do_again2 with_opt2 under_lets2}
                {r1 r2}
                (Hwf : @wf_deep_rewrite_ruleTP_gen G t should_do_again1 with_opt1 under_lets1 should_do_again2 with_opt2 under_lets2 r1 r2)
            : option_eq
                (UnderLets.wf (fun G' => wf_maybe_do_again_expr G') G)
                (normalize_deep_rewrite_rule r1) (normalize_deep_rewrite_rule r2).
          Proof using Type.
            clear -Hwf.
            all: destruct_head'_bool.
            all: cbv [normalize_deep_rewrite_rule wf_deep_rewrite_ruleTP_gen deep_rewrite_ruleTP_gen maybe_option_eq] in *.
            all: destruct_head'_and.
            all: repeat first [ assumption
                              | exfalso; assumption
                              | progress cbv [Option.bind option_eq wf_maybe_under_lets_expr] in *
                              | progress inversion_option
                              | match goal with
                                | [ |- ?x = ?x ] => reflexivity
                                | [ |- UnderLets.wf _ _ _ _ ] => constructor
                                end
                              | break_innermost_match_step ].
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
          Proof using Type. case p; reflexivity. Defined.

          Local Lemma ap_transport_Base {var T}
                (A : T -> Type)
                (x y : T) (p : x = y)
                (v : A x)
            : (rew [fun t => @UnderLets var (A t)] p in UnderLets.Base v)
              = UnderLets.Base (rew [A] p in v).
          Proof using Type. case p; reflexivity. Defined.

          Local Notation rewrite_rules_goodT := (@rewrite_rules_goodT base try_make_transport_base_cps ident pident pident_arg_types var1 var2).
          Local Notation wf_rewrite_rule_data := (@wf_rewrite_rule_data base try_make_transport_base_cps ident pident pident_arg_types var1 var2).
          Local Notation wf_reflect := (@wf_reflect base ident var1 var2).
          Local Notation wf_reify := (@wf_reify base ident var1 var2).

          Local Lemma Some_neq_None_helper {A B x y} : @Some A x = None <-> @Some B y = None.
          Proof using Type. clear; intuition congruence. Qed.

          Local Ltac fin_t_common_step :=
            first [ match goal with
                    | [ |- (Some _ = None <-> Some _ = None) /\ _ ] => split; [ exact Some_neq_None_helper | ]
                    | [ |- (?x = ?x <-> ?y = ?y) /\ _ ] => split; [ clear; split; reflexivity | ]
                    | [ |- (Some _ = None <-> None = None) /\ _ ] => exfalso
                    | [ |- (None = None <-> Some _ = None) /\ _ ] => exfalso
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
                   | [ H : ?x <> ?x |- False ] => apply H, eq_refl
                   | [ H : ?x = ?y, H' : ?x <> ?y |- False ] => apply H', H
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
                (do_again1 : forall t : base_type, @expr.expr base_type ident (@value var1) t -> @UnderLets var1 (@expr var1 t))
                (do_again2 : forall t : base_type, @expr.expr base_type ident (@value var2) t -> @UnderLets var2 (@expr var2 t))
                (wf_do_again : forall G (t : base_type) e1 e2,
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
          Proof using invert_bind_args_unknown_correct pident_unify_unknown_correct raw_pident_to_typed_invert_bind_args try_make_transport_base_cps_correct.
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
                                     | [ H : False |- _ ] => exfalso; exact H
                                     end
                                   | progress subst
                                   | progress cbn [Option.bind option_eq projT1 projT2 eq_rect eq_sym eq_trans] in *
                                   | progress inversion_option
                                   | progress destruct_head'_sigT
                                   | progress destruct_head'_sig
                                   | progress cbv [wf_rewrite_rule_data wf_with_unif_rewrite_ruleTP_gen option_bind' related_sigT_by_eq] in *
                                   | progress intros
                                   | match goal with
                                     | [ H : wf_rawexpr _ ?r _ _ _ |- context[unify_pattern1 ?r ?pv _ (@Some _)] ]
                                       => let H' := fresh in
                                          pose proof (wf_unify_pattern (p:=pv) H) as H';
                                            lazymatch type of H' with
                                            | option_eq _ ?x ?y => destruct x eqn:?, y eqn:?; cbv [option_eq] in H'
                                            end
                                     | [ H : wf_deep_rewrite_ruleTP_gen _ ?r1 ?r2
                                         |- context[normalize_deep_rewrite_rule ?r1] ]
                                       => let H' := fresh in
                                          pose proof (wf_normalize_deep_rewrite_rule H) as H';
                                            lazymatch type of H' with
                                            | option_eq _ ?x ?y => destruct x eqn:?, y eqn:?; cbv [option_eq] in H'
                                            end
                                     | [ H : (forall x y, wf_unification_resultT _ x y -> option_eq _ (app_with_unification_resultT_cps1 ?r1 x _ (@Some _)) (app_with_unification_resultT_cps2 ?r2 y _ (@Some _))),
                                             H' : wf_unification_resultT _ ?xv ?yv
                                         |- context[app_with_unification_resultT_cps1 ?r1 ?xv _ (@Some _)] ]
                                       => specialize (H _ _ H')
                                     | [ H : option_eq _ ?x ?y |- _ ] => destruct x eqn:?, y eqn:?; cbv [option_eq] in H
                                     | [ |- UnderLets.wf _ _ _ _ ] => constructor
                                     | [ |- expr.wf _ (rew _ in expr_of_rawexpr _) (rew _ in expr_of_rawexpr _) ]
                                       => apply wf_expr_of_wf_rawexpr'
                                     end
                                   | progress cps_id'_with_option unify_pattern_cps_id
                                   | progress cps_id'_with_option app_with_unification_resultT_cps_id
                                   | lazymatch goal with
                                     | [ |- context[type.try_make_transport_cps] ]
                                       => progress rewrite_type_transport_correct
                                     | [ |- context[base.try_make_transport_cps] ]
                                       => progress rewrite_type_transport_correct
                                     end
                                   | progress type_beq_to_eq
                                   | break_match_step ltac:(fun v => match v with Sumbool.sumbool_of_bool _ => idtac end)
                                   | match goal with
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
                                     end
                                   | solve [ try_solve_by_type_of_rawexpr_eqn ]
                                   | match goal with
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
                           | [ H : wf_maybe_do_again_expr _ ?v _ |- context[?v] ] => clear -H wf_do_again reflect_base_beq; cbv [wf_maybe_do_again_expr maybe_do_again] in *
                           | [ |- UnderLets.wf _ _ _ _ ] => constructor
                           | [ |- context[type.decode _ _ ?pf ] ]
                             => is_var pf;
                                lazymatch type of pf with
                                | match ?t with type.base _ => _ | _ => _ end
                                  => destruct t eqn:?
                                end
                           end
                         | progress destruct_head (@rewrite_ruleTP)
                         | solve [ eauto ] ].
          Qed.

          Section with_do_again.
            Context (dtree : @decision_tree raw_pident)
                    (rew1 : rewrite_rulesT1)
                    (rew2 : rewrite_rulesT2)
                    (Hrew : rewrite_rules_goodT rew1 rew2)
                    (do_again1 : forall t : base_type, @expr (@value var1) t -> @UnderLets var1 (@expr var1 t))
                    (do_again2 : forall t : base_type, @expr (@value var2) t -> @UnderLets var2 (@expr var2 t))
                    (wf_do_again : forall G G' (t : base_type) e1 e2,
                        (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> Compile.wf_value G v1 v2)
                        -> expr.wf G' e1 e2
                        -> UnderLets.wf (fun G' => expr.wf G') G (@do_again1 t e1) (@do_again2 t e2)).

            Local Notation assemble_identifier_rewriters' var := (@assemble_identifier_rewriters' base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple dtree).
            Local Notation assemble_identifier_rewriters var := (@assemble_identifier_rewriters base try_make_transport_base_cps base_beq ident var eta_ident_cps pident pident_arg_types pident_unify pident_unify_unknown raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple dtree).

            Lemma wf_assemble_identifier_rewriters' G t re1 e1 re2 e2
                  K1 K2
                  (He : @wf_rawexpr G t re1 e1 re2 e2)
                  (HK1 : forall P v, K1 P v = rew [P] (proj1 (eq_type_of_rawexpr_of_wf He)) in v)
                  (HK2 : forall P v, K2 P v = rew [P] (proj2 (eq_type_of_rawexpr_of_wf He)) in v)
              : wf_value_with_lets
                  G
                  (@assemble_identifier_rewriters' var1 rew1 do_again1 t re1 K1)
                  (@assemble_identifier_rewriters' var2 rew2 do_again2 t re2 K2).
            Proof using invert_bind_args_unknown_correct pident_unify_unknown_correct raw_pident_to_typed_invert_bind_args try_make_transport_base_cps_correct wf_do_again Hrew.
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
            Proof using invert_bind_args_unknown_correct pident_unify_unknown_correct raw_pident_to_typed_invert_bind_args try_make_transport_base_cps_correct wf_do_again Hrew eta_ident_cps_correct.
              cbv [assemble_identifier_rewriters]; rewrite !eta_ident_cps_correct.
              unshelve eapply wf_assemble_identifier_rewriters'; [ shelve | shelve | constructor | | ]; reflexivity.
            Qed.
          End with_do_again.
        End with_var2.
      End with_type.

      Section full.
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}
                {base_interp : base -> Type}
                (ident_is_var_like : forall t, ident t -> bool).
        Local Notation expr := (@expr base_type ident).
        Let type_base (x : base) : @base.type base := base.type.type_base x.
        Let base' {bt} (x : Compilers.base.type bt) : type.type _ := type.base x.
        Local Coercion base' : base.type >-> type.type.
        Local Coercion type_base : base >-> base.type.
        Context {base_beq : base -> base -> bool}
                {reflect_base_beq : reflect_rel (@eq base) base_beq}
                {try_make_transport_base_cps : type.try_make_transport_cpsT base}
                {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}
                {baseTypeHasNat : base.type.BaseTypeHasNatT base}
                {buildIdent : ident.BuildIdentT base_interp ident}
                {buildEagerIdent : ident.BuildEagerIdentT ident}
                {toRestrictedIdent : ident.ToRestrictedIdentT ident}
                {toFromRestrictedIdent : ident.ToFromRestrictedIdentT ident}
                {invertIdent : invert_expr.InvertIdentT base_interp ident}
                {baseHasNatCorrect : base.BaseHasNatCorrectT base_interp}
                {buildInvertIdentCorrect : invert_expr.BuildInvertIdentCorrectT}.

        Local Notation value := (@Compile.value base_type ident).
        Local Notation value_with_lets := (@Compile.value_with_lets base_type ident).
        Local Notation UnderLets := (UnderLets.UnderLets base_type ident).
        Local Notation reflect := (@Compile.reflect base ident).

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Section with_rewrite_head.
            Context (rewrite_head1 : forall t (idc : ident t), @value_with_lets var1 t)
                    (rewrite_head2 : forall t (idc : ident t), @value_with_lets var2 t)
                    (wf_rewrite_head : forall G t (idc1 idc2 : ident t),
                        idc1 = idc2 -> wf_value_with_lets G (rewrite_head1 t idc1) (rewrite_head2 t idc2)).

            Local Notation rewrite_bottomup1 := (@rewrite_bottomup base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps var1 rewrite_head1).
            Local Notation rewrite_bottomup2 := (@rewrite_bottomup base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps var2 rewrite_head2).

            Local Ltac t :=
              repeat first [ reflexivity
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
                             | [ H : _ |- _ ] => apply H; clear H; solve [ t ]
                             end ].

            Lemma wf_rewrite_bottomup G G' {t} e1 e2 (Hwf : expr.wf G e1 e2)
                  (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2)
              : wf_value_with_lets G' (@rewrite_bottomup1 t e1) (@rewrite_bottomup2 t e2).
            Proof using wf_rewrite_head try_make_transport_base_cps_correct buildInvertIdentCorrect.
              revert dependent G'; induction Hwf; intros; cbn [rewrite_bottomup].
              all: t.
            Qed.
          End with_rewrite_head.

          Local Notation nbe var := (@rewrite_bottomup base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps var (fun t idc => reflect (expr.Ident idc))).

          Lemma wf_nbe G G' {t} e1 e2
                (Hwf : expr.wf G e1 e2)
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2)
            : wf_value_with_lets G' (@nbe var1 t e1) (@nbe var2 t e2).
          Proof using try_make_transport_base_cps_correct buildInvertIdentCorrect.
            eapply wf_rewrite_bottomup; try eassumption.
            intros; subst; eapply wf_reflect; wf_t.
          Qed.

          Section with_rewrite_head2.
            Context (rewrite_head1 : forall (do_again : forall t : base_type, @expr (@value var1) (type.base t) -> @UnderLets var1 (@expr var1 (type.base t)))
                                            t (idc : ident t), @value_with_lets var1 t)
                    (rewrite_head2 : forall (do_again : forall t : base_type, @expr (@value var2) (type.base t) -> @UnderLets var2 (@expr var2 (type.base t)))
                                            t (idc : ident t), @value_with_lets var2 t)
                    (wf_rewrite_head
                     : forall
                        do_again1
                        do_again2
                        (wf_do_again
                         : forall G' G (t : base_type) e1 e2
                                  (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
                            expr.wf G e1 e2
                            -> UnderLets.wf (fun G' => expr.wf G') G' (do_again1 t e1) (do_again2 t e2))
                        G t (idc1 idc2 : ident t),
                        idc1 = idc2 -> wf_value_with_lets G (rewrite_head1 do_again1 t idc1) (rewrite_head2 do_again2 t idc2)).

            Local Notation repeat_rewrite1 := (@repeat_rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps var1 rewrite_head1).
            Local Notation repeat_rewrite2 := (@repeat_rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps var2 rewrite_head2).
            Local Notation rewrite1 := (@rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps var1 rewrite_head1).
            Local Notation rewrite2 := (@rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps var2 rewrite_head2).

            Lemma wf_repeat_rewrite fuel
              : forall {t} G G' e1 e2
                       (Hwf : expr.wf G e1 e2)
                       (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
                wf_value_with_lets G' (@repeat_rewrite1 fuel t e1) (@repeat_rewrite2 fuel t e2).
            Proof using wf_rewrite_head try_make_transport_base_cps_correct buildInvertIdentCorrect.
              induction fuel as [|fuel IHfuel]; intros; cbn [repeat_rewrite]; eapply wf_rewrite_bottomup; try eassumption;
                apply wf_rewrite_head; intros; [ eapply wf_nbe with (t:=type.base _) | eapply IHfuel with (t:=type.base _) ];
                  eassumption.
            Qed.

            Lemma wf_rewrite fuel
              : forall {t} G G' e1 e2
                       (Hwf : expr.wf G e1 e2)
                       (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> wf_value G' v1 v2),
                expr.wf G' (@rewrite1 fuel t e1) (@rewrite2 fuel t e2).
            Proof. intros; eapply wf_reify, wf_repeat_rewrite; eassumption. Qed.
          End with_rewrite_head2.
        End with_var2.

        Local Notation Rewrite := (@Rewrite base ident base_interp ident_is_var_like buildIdent invertIdent try_make_transport_base_cps).

        Theorem Wf_Rewrite
                (rewrite_head
                 : forall var
                          (do_again : forall t : base_type, @expr (@value var) (type.base t) -> @UnderLets.UnderLets base_type ident var (@expr var (type.base t)))
                          t (idc : ident t), @value_with_lets var t)
                (wf_rewrite_head
                 : forall
                    var1 var2
                    do_again1
                    do_again2
                    (wf_do_again
                     : forall G G' (t : base_type) e1 e2,
                        (forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> Compile.wf_value G v1 v2)
                        -> expr.wf G' e1 e2
                        -> UnderLets.wf (fun G' => expr.wf G') G (do_again1 t e1) (do_again2 t e2))
                    t (idc : ident t),
                    wf_value_with_lets nil (rewrite_head var1 do_again1 t idc) (rewrite_head var2 do_again2 t idc))
                fuel {t} (e : Expr t) (Hwf : Wf e)
          : Wf (@Rewrite rewrite_head fuel t e).
        Proof using try_make_transport_base_cps_correct buildInvertIdentCorrect.
          intros var1 var2; cbv [Rewrite]; eapply wf_rewrite with (G:=nil); [ | apply Hwf | wf_t ].
          intros; subst; eapply wf_value'_Proper_list; [ | eapply wf_rewrite_head ]; wf_t.
        Qed.
      End full.
    End Compile.
  End RewriteRules.
End Compilers.
