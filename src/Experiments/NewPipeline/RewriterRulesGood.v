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

      Local Ltac start_cps_id :=
        lazymatch goal with
        | [ |- In _ ?rewr -> _ ] => let h := head rewr in cbv [h]
        end;
        cbn [In combine]; intros; destruct_head'_or; inversion_sigma; subst; try reflexivity; destruct_head' False.

      Local Ltac cps_id_step :=
        first [ reflexivity
              | progress destruct_head' False
              | progress subst
              | progress inversion_option
              | progress cbv [id Compile.binding_dataT pattern.ident.arg_types Compile.ptype_interp Compile.ptype_interp_cps Compile.pbase_type_interp_cps Compile.value Compile.value' Compile.app_binding_data Compile.app_ptype_interp_cps Compile.app_pbase_type_interp_cps Compile.lift_with_bindings Compile.lift_ptype_interp_cps Compile.lift_pbase_type_interp_cps cpsbind cpscall cpsreturn cps_option_bind type_base rwhen] in *
              | progress cbn [UnderLets.splice eq_rect projT1 projT2 Option.bind Option.sequence Option.sequence_return] in *
              | progress type_beq_to_eq
              | progress rewrite_type_transport_correct
              | progress cbv [Compile.option_bind' Compile.castbe Compile.castb Compile.castv] in *
              | progress break_innermost_match
              | progress destruct_head'_sigT
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

      Lemma nbe_cps_id {var} p r
        : In (existT _ p r) (@nbe_rewrite_rules var)
          -> forall v T k, r v T k = k (r v _ id).
      Proof. cps_id_t. Qed.

      Lemma arith_cps_id max_const {var} p r
        : In (existT _ p r) (@arith_rewrite_rules var max_const)
          -> forall v T k, r v T k = k (r v _ id).
      Proof. cps_id_t. Qed.

      Lemma fancy_cps_id invert_low invert_high {var} p r
        : In (existT _ p r) (@fancy_rewrite_rules var invert_low invert_high)
          -> forall v T k, r v T k = k (r v _ id).
      Proof. cps_id_t. Qed.

      Local Ltac start_good cps_id rewrite_rules :=
        split; [ reflexivity | ];
          repeat apply conj; try solve [ eapply cps_id ]; [];
            cbv [rewrite_rules]; cbn [In combine];
              intros; destruct_head'_or; inversion_prod; inversion_sigma; subst; destruct_head' False;
              (split; [ reflexivity | ]).

      Local Ltac good_t_step :=
        first [ progress subst
              | progress cbv [id Compile.binding_dataT pattern.ident.arg_types Compile.ptype_interp Compile.ptype_interp_cps Compile.pbase_type_interp_cps Compile.value Compile.value' Compile.app_binding_data Compile.app_ptype_interp_cps Compile.app_pbase_type_interp_cps Compile.lift_with_bindings Compile.lift_ptype_interp_cps Compile.lift_pbase_type_interp_cps cpsbind cpscall cpsreturn cps_option_bind type_base Compile.wf_binding_dataT Compile.wf_ptype_interp_id Compile.wf_ptype_interp_cps Compile.wf_pbase_type_interp_cps ident.smart_Literal rwhen AnyExpr.unwrap] in *
              | progress destruct_head'_sig
              | progress cbn [eq_rect option_eq projT1 projT2 fst snd base.interp In combine Option.bind Option.sequence Option.sequence_return UnderLets.splice] in *
              | progress destruct_head'_prod
              | progress destruct_head'_sigT
              | progress intros
              | progress eliminate_hprop_eq
              | progress cbv [Compile.option_bind' Compile.castbe Compile.castb Compile.castv] in *
              | progress type_beq_to_eq
              | progress rewrite_type_transport_correct
              | break_innermost_match_step
              | wf_safe_t_step
              | rewrite !expr.reflect_list_cps_id
              | congruence
              | match goal with
                | [ |- expr.wf _ (reify_list _) (reify_list _) ] => rewrite expr.wf_reify_list
                | [ |- context[length ?ls] ] => tryif is_var ls then fail else (progress autorewrite with distr_length)
                | [ |- ex _ ] => eexists
                | [ |- UnderLets.wf _ _ _ _ ] => constructor
                | [ |- UnderLets.wf _ _ (UnderLets.splice _ _) (UnderLets.splice _ _) ] => eapply UnderLets.wf_splice
                | [ |- Compile.wf_anyexpr _ _ _ _ ] => constructor
                | [ H : Compile.wf_value ?G ?e1 ?e2 |- UnderLets.wf _ ?G (?e1 _) (?e2 _) ] => eapply (H nil)
                | [ H : Compile.wf_value ?G ?e1 ?e2 |- UnderLets.wf _ ?G (?e1 _ _) (?e2 _ _) ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H; [ reflexivity | | reflexivity | ] ]; revgoals
                | [ |- context[@rlist_rect_cast ?var ?A ?A' ?P ?ivar ?N_case ?C_case ?ls ?T ?k] ]
                  => (tryif (let __ := constr:(eq_refl : k = (fun x => x)) in idtac)
                       then fail
                       else rewrite (@rlist_rect_cast_cps_id var A A' P ivar N_case C_case ls T k))
                | [ |- context[@rlist_rect ?var ?A ?P ?ivar ?N_case ?C_case ?ls ?T ?k] ]
                  => (tryif (let __ := constr:(eq_refl : k = (fun x => x)) in idtac)
                       then fail
                       else rewrite (@rlist_rect_cps_id var A P ivar N_case C_case ls T k))
                | [ |- ?x = ?x /\ _ ] => split; [ reflexivity | ]
                end
              | solve [ wf_t ]
(*| progress cbv [Option.bind]
                          | break_match_step ltac:(fun _ => idtac)*) ].

      Lemma nbe_rewrite_rules_good
        : rewrite_rules_goodT nbe_rewrite_rules nbe_rewrite_rules.
      Proof.
        start_good (@nbe_cps_id) (@nbe_rewrite_rules).
        all: repeat good_t_step.
      Admitted.

      Lemma arith_rewrite_rules_good max_const
        : rewrite_rules_goodT (arith_rewrite_rules max_const) (arith_rewrite_rules max_const).
      Proof.
        start_good (@arith_cps_id) (@arith_rewrite_rules).
        all: repeat good_t_step.
      Admitted.

      Lemma fancy_rewrite_rules_good
            (invert_low invert_high : Z -> Z -> option Z)
            (Hlow : forall s v v', invert_low s v = Some v' -> v = Z.land v' (2^(s/2)-1))
            (Hhigh : forall s v v', invert_high s v = Some v' -> v = Z.shiftr v' (s/2))
        : rewrite_rules_goodT (fancy_rewrite_rules invert_low invert_high) (fancy_rewrite_rules invert_low invert_high).
      Proof.
        start_good (@fancy_cps_id) (@fancy_rewrite_rules).
        all: repeat good_t_step.
        all: cbv [Option.bind].
        all: repeat good_t_step.
      Qed.
    End good.
  End RewriteRules.
End Compilers.
