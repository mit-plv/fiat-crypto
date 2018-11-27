Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.SetoidList.
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
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.CPSId.
Require Import Crypto.Util.FMapPositive.Equality.
Require Import Crypto.Util.MSetPositive.Equality.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Sigma.Related.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
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
  Import expr.Notations.
  Import defaults.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    Module pattern.
      Module base.
        Lemma subst_relax {t evm}
        : pattern.base.subst (pattern.base.relax t) evm = Some t.
        Proof using Type.
          induction t; cbn; cbv [Option.bind option_map];
            rewrite_hyp ?*; reflexivity.
        Qed.

        Lemma subst_Some_subst_default {pt evm t}
          : pattern.base.subst pt evm = Some t -> pattern.base.subst_default pt evm = t.
        Proof using Type.
          revert t; induction pt;
            repeat first [ progress cbn [pattern.base.subst pattern.base.subst_default]
                         | progress cbv [Option.bind option_map]
                         | progress inversion_option
                         | progress subst
                         | progress intros
                         | reflexivity
                         | apply (f_equal base.type.list)
                         | apply (f_equal2 base.type.prod)
                         | break_innermost_match_step
                         | break_innermost_match_hyps_step
                         | solve [ eauto ] ].
        Qed.

        Lemma subst_relax_evm {pt evm evm' t}
              (Hevm : forall i v, PositiveMap.find i evm = Some v -> PositiveMap.find i evm' = Some v)
          : pattern.base.subst pt evm = Some t -> pattern.base.subst pt evm' = Some t.
        Proof using Type.
          revert t; induction pt;
            repeat first [ progress cbn [pattern.base.subst]
                         | progress cbv [Option.bind option_map]
                         | progress inversion_option
                         | progress subst
                         | progress intros
                         | reflexivity
                         | solve [ eauto ]
                         | break_innermost_match_step
                         | break_innermost_match_hyps_step
                         | match goal with
                           | [ H : forall t, Some _ = Some t -> _ |- _ ] => specialize (H _ eq_refl)
                           end ].
        Qed.

        Lemma add_var_types_cps_id {t v evm T k}
        : @pattern.base.add_var_types_cps t v evm T k = k (@pattern.base.add_var_types_cps t v evm _ id).
        Proof using Type.
          revert v evm T k.
          induction t; cbn in *; intros; break_innermost_match; try reflexivity;
            auto.
          repeat match goal with H : _ |- _ => etransitivity; rewrite H; clear H; [ | reflexivity ] end.
          reflexivity.
        Qed.

        Ltac add_var_types_cps_id :=
          cps_id_with_option (@add_var_types_cps_id _ _ _ _ _).

        Lemma unify_extracted_cps_id {pt et T k}
          : @pattern.base.unify_extracted_cps pt et T k = k (@pattern.base.unify_extracted_cps pt et _ id).
        Proof using Type.
          revert et T k; induction pt, et; cbn [pattern.base.unify_extracted_cps]; cbv [id] in *; intros;
            repeat first [ reflexivity
                         | progress inversion_option
                         | progress subst
                         | break_innermost_match_step
                         | rewrite_hyp !* ].
        Qed.

        Ltac unify_extracted_cps_id :=
          cps_id_with_option (@unify_extracted_cps_id _ _ _ _).
      End base.

      Module type.
        Lemma subst_relax {t evm}
        : pattern.type.subst (pattern.type.relax t) evm = Some t.
        Proof using Type.
          induction t; cbn; cbv [Option.bind option_map];
            rewrite_hyp ?*; rewrite ?base.subst_relax; reflexivity.
        Qed.

        Lemma subst_Some_subst_default {pt evm t}
          : pattern.type.subst pt evm = Some t -> pattern.type.subst_default pt evm = t.
        Proof using Type.
          revert t; induction pt;
            repeat first [ progress cbn [pattern.type.subst pattern.type.subst_default]
                         | progress cbv [Option.bind option_map]
                         | progress inversion_option
                         | progress subst
                         | progress intros
                         | reflexivity
                         | apply (f_equal type.base)
                         | apply (f_equal2 type.arrow)
                         | break_innermost_match_step
                         | break_innermost_match_hyps_step
                         | solve [ eauto ]
                         | apply base.subst_Some_subst_default ].
        Qed.

        Lemma subst_relax_evm {pt evm evm' t}
              (Hevm : forall i v, PositiveMap.find i evm = Some v -> PositiveMap.find i evm' = Some v)
          : pattern.type.subst pt evm = Some t -> pattern.type.subst pt evm' = Some t.
        Proof using Type.
          revert t; induction pt;
            repeat first [ progress cbn [pattern.type.subst]
                         | progress cbv [Option.bind option_map]
                         | progress inversion_option
                         | progress subst
                         | progress intros
                         | reflexivity
                         | solve [ eauto ]
                         | break_innermost_match_step
                         | break_innermost_match_hyps_step
                         | congruence
                         | match goal with
                           | [ H : forall t, Some _ = Some t -> _ |- _ ] => specialize (H _ eq_refl)
                           | [ H : pattern.base.subst _ _ = Some _ |- _ ]
                             => unique pose proof (base.subst_relax_evm Hevm H)
                           | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                             => assert (a = b) by congruence; (subst a || subst b)
                           end ].
        Qed.

        Lemma add_var_types_cps_id {t v evm T k}
        : @pattern.type.add_var_types_cps t v evm T k = k (@pattern.type.add_var_types_cps t v evm _ id).
        Proof using Type.
          revert v evm T k.
          induction t; cbn in *; intros; break_innermost_match; try reflexivity;
            auto using base.add_var_types_cps_id.
          repeat match goal with H : _ |- _ => etransitivity; rewrite H; clear H; [ | reflexivity ] end.
          reflexivity.
        Qed.

        Ltac add_var_types_cps_id :=
          cps_id_with_option (@add_var_types_cps_id _ _ _ _ _).

        Lemma unify_extracted_cps_id {pt et T k}
          : @pattern.type.unify_extracted_cps pt et T k = k (@pattern.type.unify_extracted_cps pt et _ id).
        Proof using Type.
          revert et T k; induction pt, et; cbn [pattern.type.unify_extracted_cps]; cbv [id] in *; intros;
            repeat first [ reflexivity
                         | progress inversion_option
                         | progress subst
                         | apply base.unify_extracted_cps_id
                         | break_innermost_match_step
                         | rewrite_hyp !* ].
        Qed.

        Ltac unify_extracted_cps_id :=
          cps_id_with_option (@unify_extracted_cps_id _ _ _ _).

        Lemma app_forall_vars_under_forall_vars_relation
              {p k1 k2 F v1 v2 evm}
          : @pattern.type.under_forall_vars_relation p k1 k2 F v1 v2
            -> option_eq
                 (F _)
                 (@pattern.type.app_forall_vars p k1 v1 evm)
                 (@pattern.type.app_forall_vars p k2 v2 evm).
        Proof using Type.
          revert k1 k2 F v1 v2 evm.
          cbv [pattern.type.under_forall_vars_relation pattern.type.app_forall_vars pattern.type.forall_vars].
          generalize (PositiveMap.empty base.type).
          induction (List.rev (PositiveSet.elements p)) as [|x xs IHxs]; cbn; eauto.
          intros; break_innermost_match; cbn in *; eauto.
        Qed.

        Local Lemma app_forall_vars_under_forall_vars_relation1_helper0
              xs x v evm evm'
              (H_NoDup : NoDupA PositiveSet.E.eq (x::xs))
              (H_find : PositiveMap.find x evm' = Some v)
              (body := fun evm (i : PositiveMap.key) (k : EvarMap -> EvarMap) (evm' : EvarMap)
                       => k
                            match PositiveMap.find i evm with
                            | Some v => PositiveMap.add i v evm'
                            | None => evm'
                            end)
          : (fold_right (body evm) (fun evm' => evm') xs evm')
            = (fold_right (body (PositiveMap.add x v evm)) (fun evm' => evm') xs evm').
        Proof using Type.
          cbv [PositiveSet.E.eq] in *.
          subst body; cbv beta.
          inversion H_NoDup; clear H_NoDup; subst.
          revert evm evm' H_find.
          induction xs as [|x' xs IHxs]; cbn [fold_right] in *; [ reflexivity | ]; intros.
          repeat first [ progress subst
                       | rewrite PositiveMapAdditionalFacts.gsspec in *
                       | progress specialize_by_assumption
                       | progress destruct_head'_and
                       | match goal with
                         | [ H : NoDupA _ (cons _ _) |- _ ] => inversion H; clear H
                         | [ H : context[InA _ _ (cons _ _)] |- _ ] => rewrite InA_cons in H
                         | [ H : ~(or _ _) |- _ ] => apply Decidable.not_or in H
                         | [ H : ?x <> ?x |- _ ] => exfalso; apply H; reflexivity
                         end
                       | break_innermost_match_step
                       | match goal with
                         | [ H : _ |- _ ] => apply H; clear H
                         end ].
        Qed.

        Local Lemma app_forall_vars_under_forall_vars_relation1_helper1
              xs x
              (H_NoDup : NoDupA PositiveSet.E.eq (x::xs))
              v evm evm'
              (body := fun evm (i : PositiveMap.key) (k : EvarMap -> EvarMap) (evm' : EvarMap)
                       => k
                            match PositiveMap.find i evm with
                            | Some v => PositiveMap.add i v evm'
                            | None => evm'
                            end)
          : (fold_right (body evm) (fun evm' => evm') xs (PositiveMap.add x v evm'))
            = (fold_right (body (PositiveMap.add x v evm)) (fun evm' => evm') xs (PositiveMap.add x v evm')).
        Proof using Type.
          apply app_forall_vars_under_forall_vars_relation1_helper0; [ assumption | ].
          apply PositiveMap.gss.
        Qed.

        Local Lemma app_forall_vars_under_forall_vars_relation1_helper2
              xs x
              (H_NoDup : NoDupA PositiveSet.E.eq (x::xs))
              v evm evm'
              (body := fun evm (i : PositiveMap.key) (k : EvarMap -> EvarMap) (evm' : EvarMap)
                       => k
                            match PositiveMap.find i evm with
                            | Some v => PositiveMap.add i v evm'
                            | None => evm'
                            end)
          : (fold_right (body evm) (fun evm' => evm') xs (PositiveMap.add x v evm'))
            = (fold_right (body (PositiveMap.add x v evm)) (fun evm' => evm') xs
                          (match PositiveMap.find x (PositiveMap.add x v evm) with
                           | Some v => PositiveMap.add x v evm'
                           | None => evm'
                           end)).
        Proof using Type.
          rewrite PositiveMap.gss; apply app_forall_vars_under_forall_vars_relation1_helper1; assumption.
        Qed.

        Lemma app_forall_vars_under_forall_vars_relation1
              {p k1 F f}
          : @pattern.type.under_forall_vars_relation1 p k1 F f
            <-> (forall evm fv, pattern.type.app_forall_vars f evm = Some fv -> F _ fv).
        Proof using Type.
          revert k1 F f.
          cbv [pattern.type.under_forall_vars_relation1 pattern.type.app_forall_vars pattern.type.forall_vars].
          generalize (PositiveMap.empty base.type).
          pose proof (PositiveSet.elements_spec2w p) as H_NoDup.
          apply (@NoDupA_rev _ eq _) in H_NoDup.
          induction (List.rev (PositiveSet.elements p)) as [|x xs IHxs]; cbn in *.
          { split; intros; inversion_option; subst; eauto. }
          { intros; setoid_rewrite IHxs; clear IHxs; [ | inversion_clear H_NoDup; assumption ].
            split; intro H'.
            { intros; break_innermost_match; break_innermost_match_hyps; eauto; congruence. }
            { intros t' evm fv H''.
              (** Now we do a lot of manual equality munging :-( *)
              let evm := match type of fv with ?k1 (fold_right _ _ _ (PositiveMap.add ?x ?v _)) => constr:(PositiveMap.add x v evm) end in
              specialize (H' evm).
              rewrite PositiveMap.gss in H'.
              lazymatch goal with
              | [ |- context[fold_right (fun i k evm'' => k match PositiveMap.find i ?evm with _ => _ end) _ ?xs (PositiveMap.add ?x ?v ?evm')] ]
                => pose proof (@app_forall_vars_under_forall_vars_relation1_helper1 xs x ltac:(assumption) v evm evm') as H''';
                     cbv beta iota zeta in H'''
              end.
              pose (existT k1 _ fv) as fv'.
              assert (Hf : existT k1 _ fv = fv') by reflexivity.
              change fv with (projT2 fv').
              let T := match (eval cbv delta [fv'] in fv') with existT _ ?T _ => T end in
              change T with (projT1 fv') in H''' |- *.
              clearbody fv'.
              destruct fv' as [evm' fv']; cbn [projT1 projT2] in *.
              subst evm'.
              apply H'; clear H'.
              inversion_sigma; subst fv'.
              rewrite (@Equality.commute_eq_rect _ k1 (fun t => option (k1 t)) (fun _ v => Some v)).
              rewrite <- H''.
              clear -H_NoDup.
              match goal with
              | [ |- context[list_rect _ _ _ _ _ (?f ?t)] ]
                => generalize (f t); clear f
              end.
              intro f.
              lazymatch type of f with
              | fold_right _ _ _ (PositiveMap.add ?x ?v ?evm)
                => assert (PositiveMap.find x (PositiveMap.add x v evm) = Some v)
                  by apply PositiveMap.gss;
                     generalize dependent (PositiveMap.add x v evm); clear evm
              end.
              revert dependent evm.
              induction xs as [|x' xs IHxs]; cbn [list_rect fold_right] in *.
              { intros; eliminate_hprop_eq; reflexivity. }
              { repeat first [ progress subst
                             | progress destruct_head'_and
                             | match goal with
                               | [ H : NoDupA _ (cons _ _) |- _ ] => inversion H; clear H
                               | [ H : context[InA _ _ (cons _ _)] |- _ ] => rewrite InA_cons in H
                               | [ H : ~(or _ _) |- _ ] => apply Decidable.not_or in H
                               end ].
                specialize (IHxs ltac:(constructor; assumption)).
                intros; break_innermost_match.
                all: repeat first [ match goal with
                                    | [ H : context[PositiveMap.find _ (PositiveMap.add _ _ _)] |- _  ]
                                      => rewrite PositiveMap.gso in H by congruence
                                    | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                                      => assert (a = b) by congruence; (subst a || subst b); (clear H || clear H')
                                    | [ H : ?x = Some _, H' : ?x = None |- _ ]
                                      => exfalso; clear -H H'; congruence
                                    | [ |- None = rew ?pf in None ]
                                      => progress clear;
                                         lazymatch type of pf with
                                         | ?a = ?b => generalize dependent a || generalize dependent b
                                         end;
                                         intros; progress subst; reflexivity
                                    | [ H : _ |- _ ] => apply H; rewrite PositiveMap.gso by congruence; assumption
                                    end ]. } } }
        Qed.

        Lemma under_forall_vars_relation1_lam_forall_vars
              {p k1 F f}
          : @pattern.type.under_forall_vars_relation1 p k1 F (@pattern.type.lam_forall_vars p k1 f)
            <-> forall ls',
              List.length ls' = List.length (List.rev (PositiveSet.elements p))
              -> let evm := fold_left (fun m '(k, v) => PositiveMap.add k v m) (List.combine (List.rev (PositiveSet.elements p)) ls') (PositiveMap.empty _) in
                 F evm (f evm).
        Proof using Type.
          cbv [pattern.type.under_forall_vars_relation1 pattern.type.lam_forall_vars].
          generalize (PositiveMap.empty base.type).
          generalize (rev (PositiveSet.elements p)).
          clear p.
          intros ls m.
          revert k1 F f m.
          induction ls as [|l ls IHls]; cbn [list_rect fold_right fold_left List.length] in *; intros.
          { split; intro H; [ intros [|] | specialize (H nil eq_refl) ]; cbn [List.length List.combine fold_right] in *; intros; try discriminate; assumption. }
          { setoid_rewrite IHls; clear IHls.
            split; intro H; [ intros [|l' ls'] Hls'; [ | specialize (H l' ls') ]
                            | intros t ls' Hls'; specialize (H (cons t ls')) ];
            cbn [List.length List.combine fold_left] in *;
            try discriminate; inversion Hls'; eauto. }
        Qed.

        Lemma app_forall_vars_lam_forall_vars {p k f evm v}
          : @pattern.type.app_forall_vars p k (pattern.type.lam_forall_vars f) evm = Some v
            -> v = f _.
        Proof using Type.
          revert v; cbv [pattern.type.app_forall_vars pattern.type.lam_forall_vars].
          generalize (rev (PositiveSet.elements p)); clear p; intro ls.
          generalize (PositiveMap.empty base.type).
          induction ls as [|x xs IHxs]; cbn [list_rect fold_right]; [ congruence | ].
          intros t v H; eapply IHxs; clear IHxs.
          rewrite <- H.
          break_innermost_match; [ | now discriminate ].
          reflexivity.
        Qed.
      End type.
    End pattern.

    Module Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.

      Section with_type0.
        Context {base_type} {ident : type.type base_type -> Type}.
        Local Notation type := (type.type base_type).
        Local Notation expr := (@expr.expr base_type ident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident).
        Let type_base (t : base_type) : type := type.base t.
        Coercion type_base : base_type >-> type.

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Local Notation value'1 := (@value' base_type ident var1).
          Local Notation value'2 := (@value' base_type ident var2).
          Local Notation value1 := (@value base_type ident var1).
          Local Notation value2 := (@value base_type ident var2).
          Local Notation value_with_lets1 := (@value_with_lets base_type ident var1).
          Local Notation value_with_lets2 := (@value_with_lets base_type ident var2).
          Local Notation Base_value := (@Base_value base_type ident).
          Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base_type ident).
          Local Notation splice_value_with_lets := (@splice_value_with_lets base_type ident).

          Fixpoint wf_value' {with_lets : bool} G {t : type} : value'1 with_lets t -> value'2 with_lets t -> Prop
            := match t, with_lets with
               | type.base t, true => UnderLets.wf (fun G' => expr.wf G') G
               | type.base t, false => expr.wf G
               | type.arrow s d, _
                 => fun f1 f2
                    => (forall seg G' v1 v2,
                           G' = (seg ++ G)%list
                           -> @wf_value' false seg s v1 v2
                           -> @wf_value' true G' d (f1 v1) (f2 v2))
               end.

          Definition wf_value G {t} : value1 t -> value2 t -> Prop := @wf_value' false G t.
          Definition wf_value_with_lets G {t} : value_with_lets1 t -> value_with_lets2 t -> Prop := @wf_value' true G t.

          Lemma wf_value'_Proper_list {with_lets} G1 G2
                (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                t e1 e2
                (Hwf : @wf_value' with_lets G1 t e1 e2)
            : @wf_value' with_lets G2 t e1 e2.
          Proof.
            revert Hwf; revert dependent with_lets; revert dependent G2; revert dependent G1; induction t;
              repeat first [ progress cbn in *
                           | progress intros
                           | solve [ eauto ]
                           | progress subst
                           | progress destruct_head'_or
                           | progress inversion_sigma
                           | progress inversion_prod
                           | progress break_innermost_match_hyps
                           | eapply UnderLets.wf_Proper_list; [ .. | solve [ eauto ] ]
                           | wf_unsafe_t_step
                           | match goal with H : _ |- _ => solve [ eapply H; [ .. | solve [ eauto ] ]; wf_t ] end ].
          Qed.

          Lemma wf_Base_value G {t} v1 v2 (Hwf : @wf_value G t v1 v2)
            : @wf_value_with_lets G t (Base_value v1) (Base_value v2).
          Proof.
            destruct t; cbn; intros; subst; hnf; try constructor; try assumption.
            eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; trivial.
          Qed.

          Lemma wf_splice_under_lets_with_value {T1 T2 t}
                G
                (x1 : @UnderLets var1 T1) (x2 : @UnderLets var2 T2)
                (e1 : T1 -> value_with_lets1 t) (e2 : T2 -> value_with_lets2 t)
                (Hx : UnderLets.wf (fun G' a1 a2 => wf_value_with_lets G' (e1 a1) (e2 a2)) G x1 x2)
            : wf_value_with_lets G (splice_under_lets_with_value x1 e1) (splice_under_lets_with_value x2 e2).
          Proof.
            cbv [wf_value_with_lets] in *.
            revert dependent G; induction t as [t|s IHs d IHd]; cbn [splice_under_lets_with_value wf_value']; intros.
            { eapply UnderLets.wf_splice; eauto. }
            { intros; subst; apply IHd.
              eapply UnderLets.wf_Proper_list_impl; [ | | solve [ eauto ] ]; wf_t.
              eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; wf_t. }
          Qed.

          Lemma wf_splice_value_with_lets {t t'}
                G
                (x1 : value_with_lets1 t) (x2 : value_with_lets2 t)
                (e1 : value1 t -> value_with_lets1 t') (e2 : value2 t -> value_with_lets2 t')
                (Hx : wf_value_with_lets G x1 x2)
                (He : forall seg G' v1 v2, (G' = (seg ++ G)%list) -> wf_value G' v1 v2 -> wf_value_with_lets G' (e1 v1) (e2 v2))
            : wf_value_with_lets G (splice_value_with_lets x1 e1) (splice_value_with_lets x2 e2).
          Proof.
            destruct t; cbn [splice_value_with_lets].
            { eapply wf_splice_under_lets_with_value.
              eapply UnderLets.wf_Proper_list_impl; [ | | eassumption ]; trivial; wf_t. }
            { eapply wf_value'_Proper_list; [ | eapply He with (seg:=nil); hnf in Hx |- * ].
              { eauto; subst G'; wf_t. }
              { reflexivity. }
              { intros; subst; eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; wf_t. } }
          Qed.
        End with_var2.
      End with_type0.
      Local Notation EvarMap := pattern.EvarMap.
      Section with_var.
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
                (pident_to_typed
                 : forall t (idc : pident t) (evm : EvarMap),
                    type_of_list (pident_arg_types t idc) -> ident (pattern.type.subst_default t evm))
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
        Local Notation expr := (@expr.expr base.type ident).
        Local Notation pattern := (@pattern.pattern pident).
        Local Notation rawpattern := (@pattern.Raw.pattern raw_pident).
        Local Notation anypattern := (@pattern.anypattern pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base.type ident).
        Local Notation ptype := (type.type pattern.base.type).
        Local Notation value' := (@value' base.type ident).
        Local Notation value := (@value base.type ident).
        Local Notation value_with_lets := (@value_with_lets base.type ident).
        Local Notation Base_value := (@Base_value base.type ident).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base.type ident).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base.type ident).
        Local Notation to_raw_pattern := (@pattern.to_raw pident raw_pident (@strip_types)).
        Local Notation reify := (@reify ident).
        Local Notation reflect := (@reflect ident).
        Local Notation reify_expr := (@reify_expr ident).
        Local Notation rawexpr := (@rawexpr ident).
        Local Notation eval_decision_tree var := (@eval_decision_tree ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation reveal_rawexpr_gen assume_known e := (@reveal_rawexpr_cps_gen ident _ assume_known e _ id).
        Local Notation reveal_rawexpr e := (@reveal_rawexpr_cps ident _ e _ id).
        Local Notation unify_pattern' var := (@unify_pattern' ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation unify_pattern var := (@unify_pattern ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation app_transport_with_unification_resultT'_cps var := (@app_transport_with_unification_resultT'_cps ident var pident pident_arg_types).
        Local Notation app_with_unification_resultT_cps var := (@app_with_unification_resultT_cps ident var pident pident_arg_types type_vars_of_pident).

        Definition lam_type_of_list {ls K} : (type_of_list ls -> K) -> type_of_list_cps K ls
          := list_rect
               (fun ls => (type_of_list ls -> K) -> type_of_list_cps K ls)
               (fun f => f tt)
               (fun T Ts rec k t => rec (fun ts => k (t, ts)))
               ls.

        Lemma app_lam_type_of_list
              {K ls f args}
          : @app_type_of_list K ls (@lam_type_of_list ls K f) args = f args.
        Proof using Type.
          cbv [app_type_of_list lam_type_of_list].
          induction ls as [|l ls IHls]; cbn [list_rect type_of_list type_of_list_cps] in *;
            destruct_head'_unit; destruct_head'_prod; cbn [fst snd] in *; try reflexivity; apply IHls.
        Qed.

        Section with_var1.
          Context {var : type -> Type}.
          Local Notation expr := (@expr.expr base.type ident var).
          Local Notation deep_rewrite_ruleTP_gen := (@deep_rewrite_ruleTP_gen ident var).

          Local Notation "e1 === e2" := (existT expr _ e1 = existT expr _ e2) : type_scope.

          Fixpoint rawexpr_equiv_expr {t0} (e1 : expr t0) (r2 : rawexpr) {struct r2} : Prop
            := match r2 with
               | rIdent _ t idc t' alt
                 => alt === e1 /\ expr.Ident idc === e1
               | rApp f x t alt
                 => alt === e1
                    /\ match e1 with
                       | expr.App _ _ f' x'
                         => rawexpr_equiv_expr f' f /\ rawexpr_equiv_expr x' x
                       | _ => False
                       end
               | rExpr t e => e === e1
               | rValue t e => reify e === e1
               end.

          Definition rawexpr_ok (r : rawexpr) := rawexpr_equiv_expr (expr_of_rawexpr r) r.

          Fixpoint rawexpr_equiv (r1 r2 : rawexpr) : Prop
            := match r1, r2 with
               | rExpr t e, r
               | r, rExpr t e
                 => rawexpr_equiv_expr e r
                                       (*
               | rValue t1 e1, rValue t2 e2
                 => existT _ t1 e1 = existT _ t2 e2
                                        *)
               | rValue t e, r
               | r, rValue t e
                 => rawexpr_equiv_expr (reify e) r
               | rIdent _ t1 idc1 t'1 alt1, rIdent _ t2 idc2 t'2 alt2
                 => alt1 === alt2
                    /\ (existT ident _ idc1 = existT ident _ idc2)
               | rApp f1 x1 t1 alt1, rApp f2 x2 t2 alt2
                 => alt1 === alt2
                    /\ rawexpr_equiv f1 f2
                    /\ rawexpr_equiv x1 x2
               | rIdent _ _ _ _ _, _
               | rApp _ _ _ _, _
                 => False
               end.

          Global Instance rawexpr_equiv_Reflexive : Reflexive rawexpr_equiv.
          Proof using Type.
            intro x; induction x; cbn; repeat apply conj; break_innermost_match; try reflexivity; auto.
          Qed.

          Global Instance rawexpr_equiv_Symmetric : Symmetric rawexpr_equiv.
          Proof using Type.
            intro x; induction x; intro y; destruct y; intros;
              repeat first [ progress destruct_head'_and
                           | progress subst
                           | progress cbn in *
                           | progress inversion_sigma
                           | break_innermost_match_step
                           | break_innermost_match_hyps_step
                           | type.inversion_type_step
                           | solve [ auto ]
                           | apply conj
                           | (exists eq_refl)
                           | apply path_sigT_uncurried ].
          Qed.

          Lemma rawexpr_equiv_expr_to_rawexpr_equiv {t} e r
            : @rawexpr_equiv_expr t e r <-> rawexpr_equiv (rExpr e) r /\ rawexpr_equiv r (rExpr e).
          Proof using Type.
            split; [ intro H | intros [H0 H1] ]; cbn; try apply conj; (idtac + symmetry); assumption.
          Qed.

          Local Ltac invert_t_step :=
            first [ progress cbn -[rawexpr_equiv] in *
                  | exfalso; assumption
                  | progress intros
                  | progress destruct_head'_and
                  | progress subst
                  | match goal with
                    | [ H : (existT ?P ?t (reify ?e)) = _ |- _ ] => generalize dependent (existT P t (reify e)); clear e t
                    | [ H : _ = (existT ?P ?t (reify ?e)) |- _ ] => generalize dependent (existT P t (reify e)); clear e t
                    | [ H : existT value ?t1 ?e1 = existT value ?t2 ?e2 |- _ ]
                      => first [ is_var t1; is_var e1 | is_var t2; is_var e2 ];
                         induction_sigma_in_using H (@path_sigT_rect)
                    | [ H : match reify ?e with _ => _ end |- _ ] => generalize dependent (reify e); clear e
                    end
                  | progress inversion_sigma
                  | progress inversion_option
                  | reflexivity
                  | (exists eq_refl)
                  | match goal with
                    | [ |- ?x = ?x /\ _ ] => apply conj
                    | [ |- ?x = ?y :> sigT _ ] => apply path_sigT_uncurried
                    end
                  | (idtac + symmetry); assumption ].
          Local Ltac equiv_t_step :=
            first [ invert_t_step
                  | apply conj
                  | solve [ eauto ]
                  | break_innermost_match_step
                  | expr.inversion_expr_step
                  | type.inversion_type_step
                  | break_innermost_match_hyps_step
                  | match goal with
                    | [ H : forall y z : rawexpr, rawexpr_equiv ?x _ -> _ -> _, H' : rawexpr_equiv ?x _ |- _ ]
                      => unique pose proof (fun z => H _ z H')
                    | [ H : forall z : rawexpr, rawexpr_equiv ?x _ -> _, H' : rawexpr_equiv ?x _ |- _ ]
                      => unique pose proof (H _ H')
                    | [ H : rawexpr_equiv_expr _ _ |- _ ] => rewrite rawexpr_equiv_expr_to_rawexpr_equiv in H
                    | [ |- rawexpr_equiv_expr ?e ?r ] => change (rawexpr_equiv (rExpr e) r)
                    end
                  | expr.invert_match_step ].

          Local Instance rawexpr_equiv_expr_Proper {t}
            : Proper (eq ==> rawexpr_equiv ==> Basics.impl) (@rawexpr_equiv_expr t).
          Proof using Type.
            cbv [Proper respectful Basics.impl]; intros e e' ? r1 r2 H0 H1; subst e'.
            revert r2 t e H1 H0.
            induction r1, r2; cbn in *; repeat equiv_t_step.
          Qed.

          Local Instance rawexpr_equiv_expr_Proper' {t}
            : Proper (eq ==> rawexpr_equiv ==> Basics.flip Basics.impl) (@rawexpr_equiv_expr t).
          Proof using Type.
            intros e e' ? r1 r2 H0 H1; subst e'.
            rewrite H0; assumption.
          Qed.

          Local Instance rawexpr_equiv_expr_Proper'' {t}
            : Proper (eq ==> rawexpr_equiv ==> iff) (@rawexpr_equiv_expr t).
          Proof using Type.
            intros e e' ? r1 r2 H; subst e'.
            split; intro; (rewrite H + rewrite <- H); assumption.
          Qed.

          Global Instance rawexpr_equiv_Transitive : Transitive rawexpr_equiv.
          Proof using Type.
            intro x; induction x; intros y z; destruct y, z.
            all: intros; cbn in *; repeat invert_t_step.
            all: cbn in *; expr.invert_match; break_innermost_match.
            all: try solve [ intros; destruct_head'_and; inversion_sigma; subst; cbn [eq_rect] in *; subst; repeat apply conj; eauto;
                             match goal with
                             | [ H : rawexpr_equiv ?a ?b, H' : rawexpr_equiv_expr ?e ?a |- rawexpr_equiv_expr ?e ?b ]
                               => rewrite <- H; assumption
                             | [ H : rawexpr_equiv ?a ?b, H' : rawexpr_equiv_expr ?e ?b |- rawexpr_equiv_expr ?e ?a ]
                               => rewrite H; assumption
                             end
                           | exfalso; assumption
                           | repeat equiv_t_step ].
          Qed.

          Global Instance rawexpr_equiv_Equivalence : Equivalence rawexpr_equiv.
          Proof using Type. split; exact _. Qed.

          Lemma rawexpr_equiv_expr_to_type_of_rawexpr
                {t e re}
            : @rawexpr_equiv_expr t e re -> t = type_of_rawexpr re.
          Proof using Type.
            destruct re; cbn [rawexpr_equiv_expr];
              intros; destruct_head'_and; inversion_sigma;
                repeat (subst || cbn [eq_rect type_of_rawexpr] in * );
                reflexivity.
          Qed.

          Lemma swap_swap_list {A n m ls ls'}
            : @swap_list A n m ls = Some ls' -> @swap_list A n m ls' = Some ls.
          Proof using Type.
            cbv [swap_list].
            break_innermost_match; intros; inversion_option; subst;
              f_equal; try apply list_elementwise_eq; intros;
                repeat first [ progress subst
                             | progress inversion_option
                             | rewrite !nth_set_nth
                             | rewrite !length_set_nth
                             | congruence
                             | match goal with
                               | [ H : context[nth_error (set_nth _ _ _) _] |- _ ] => rewrite !nth_set_nth in H
                               | [ H : context[List.length (set_nth _ _ _)] |- _ ] => rewrite !length_set_nth in H
                               | [ H : nth_error ?ls ?n = Some ?x |- _ ] => unique pose proof (@nth_error_value_length _ _ _ _ H)
                               | [ H : context[Nat.eq_dec ?x ?y] |- _ ] => destruct (Nat.eq_dec x y)
                               | [ |- context[Nat.eq_dec ?x ?y] ] => destruct (Nat.eq_dec x y)
                               | [ H : context[lt_dec ?x ?y] |- _ ] => destruct (lt_dec x y)
                               end ].
          Qed.
          Lemma swap_swap_list_iff {A n m ls ls'}
            : @swap_list A n m ls = Some ls' <-> @swap_list A n m ls' = Some ls.
          Proof using Type. split; apply swap_swap_list. Qed.

          Lemma swap_list_eqlistA {A R}
            : Proper (eq ==> eq ==> SetoidList.eqlistA R ==> option_eq (SetoidList.eqlistA R))
                     (@swap_list A).
          Proof using Type.
            intros n n' ? m m' ? ls1 ls2 Hls; subst m' n'.
            cbv [swap_list].
            break_innermost_match; intros; inversion_option; subst; cbn [option_eq];
              try apply list_elementwise_eqlistA; intros;
                repeat first [ progress subst
                             | progress inversion_option
                             | rewrite !nth_set_nth
                             | rewrite !length_set_nth
                             | progress cbv [option_eq] in *
                             | congruence
                             | break_innermost_match_step
                             | match goal with
                               | [ H : eqlistA _ _ _ |- _ ] => unique pose proof (@eqlistA_length _ _ _ _ H)
                               | [ H : context[nth_error (set_nth _ _ _) _] |- _ ] => rewrite !nth_set_nth in H
                               | [ H : context[List.length (set_nth _ _ _)] |- _ ] => rewrite !length_set_nth in H
                               | [ H : nth_error ?ls ?n = Some ?x |- _ ] => unique pose proof (@nth_error_value_length _ _ _ _ H)
                               | [ H : context[Nat.eq_dec ?x ?y] |- _ ] => destruct (Nat.eq_dec x y)
                               | [ |- context[Nat.eq_dec ?x ?y] ] => destruct (Nat.eq_dec x y)
                               | [ H : context[lt_dec ?x ?y] |- _ ] => destruct (lt_dec x y)
                               | [ |- context[lt_dec ?x ?y] ] => destruct (lt_dec x y)
                               | [ H : eqlistA ?R ?ls1 ?ls2, H1 : nth_error ?ls1 ?n = Some ?v1, H2 : nth_error ?ls2 ?n = Some ?v2 |- _ ]
                                 => unique assert (R v1 v2)
                                   by (generalize (nth_error_Proper_eqlistA ls1 ls2 H n n eq_refl); rewrite H1, H2; cbn; congruence)
                               | [ H : eqlistA ?R ?ls1 ?ls2, H1 : nth_error ?ls1 ?n = _, H2 : nth_error ?ls2 ?n = _ |- _ ]
                                 => exfalso; generalize (nth_error_Proper_eqlistA ls1 ls2 H n n eq_refl); rewrite H1, H2; cbn; congruence
                               | [ |- nth_error ?a ?b = _ ] => destruct (nth_error a b) eqn:?
                               end ].
          Qed.

          Local Ltac rew_swap_list_step0 :=
            match goal with
            | [ H : swap_list ?a ?b ?ls1 = Some ?ls2, H' : context[swap_list ?a ?b ?ls2] |- _ ]
              => rewrite (swap_swap_list H) in H'
            | [ H : swap_list ?a ?b ?ls1 = Some ?ls2 |- context[swap_list ?a ?b ?ls2] ]
              => rewrite (swap_swap_list H)
            | [ H : swap_list ?a ?b ?ls1 = Some ?ls2 |- context[swap_list ?a ?b ?ls1] ]
              => rewrite H
            end.

          Lemma swap_swap_list_eqlistA {A R a b ls1 ls2 ls3 ls4}
                (H : swap_list a b ls1 = Some ls2)
                (H' : swap_list a b ls3 = Some ls4)
                (Hl : eqlistA R ls2 ls3)
            : @eqlistA A R ls1 ls4.
          Proof using Type.
            generalize (swap_list_eqlistA a a eq_refl b b eq_refl _ _ Hl).
            clear Hl.
            (destruct (swap_list a b ls2) eqn:?, (swap_list a b ls4) eqn:?).
            all: repeat (rew_swap_list_step0 || inversion_option || subst); cbn [option_eq]; tauto.
          Qed.

          Lemma swap_list_None_iff {A} (i j : nat) (ls : list A)
            : swap_list i j ls = None <-> (length ls <= i \/ length ls <= j)%nat.
          Proof using Type.
            rewrite <- !nth_error_None.
            cbv [swap_list]; break_innermost_match; intuition congruence.
          Qed.

          Lemma swap_list_Some_length {A} (i j : nat) (ls ls' : list A)
            : swap_list i j ls = Some ls'
              -> (i < length ls /\ j < length ls /\ length ls' = length ls)%nat.
          Proof using Type.
            cbv [swap_list]; break_innermost_match; intros; inversion_option; subst.
            repeat match goal with H : _ |- _ => apply nth_error_value_length in H end.
            autorewrite with distr_length; tauto.
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

          Lemma nth_error_swap_list {A} {i j : nat} {ls ls' : list A}
            : swap_list i j ls = Some ls'
              -> forall k,
                nth_error ls' k = if Nat.eq_dec k i then nth_error ls j else if Nat.eq_dec k j then nth_error ls i else nth_error ls k.
          Proof.
            cbv [swap_list]; break_innermost_match; intros; inversion_option; subst;
              rewrite ?nth_set_nth; distr_length; break_innermost_match; try congruence; try lia;
                handle_nth_error.
          Qed.

          Lemma unify_types_cps_id {t e p T k}
            : @unify_types ident var pident t e p T k = k (@unify_types ident var pident t e p _ id).
          Proof using Type.
            cbv [unify_types]; break_innermost_match; try reflexivity.
            etransitivity; rewrite pattern.type.add_var_types_cps_id; [ reflexivity | ]; break_innermost_match; reflexivity.
          Qed.

          Lemma unify_pattern'_cps_id {t e p evm T cont}
            : @unify_pattern' var t e p evm T cont
              = (v' <- @unify_pattern' var t e p evm _ (@Some _); cont v')%option.
          Proof using Type.
            clear.
            revert e evm T cont; induction p; intros; cbn in *;
              repeat first [ progress rewrite_type_transport_correct
                           | reflexivity
                           | progress cbv [Option.bind cpscall option_bind'] in *
                           | match goal with H : _ |- _ => etransitivity; rewrite H; clear H; [ | reflexivity ] end
                           | break_innermost_match_step ].
          Qed.

          Lemma unify_pattern_cps_id {t e p T cont}
            : @unify_pattern var t e p T cont
              = (v' <- @unify_pattern var t e p _ (@Some _); cont v')%option.
          Proof using Type.
            clear.
            cbv [unify_pattern].
            etransitivity; rewrite unify_types_cps_id; [ | reflexivity ].
            repeat first [ reflexivity
                         | progress rewrite_type_transport_correct
                         | progress cbv [Option.bind cpscall option_bind'] in *
                         | match goal with
                           | [ |- @unify_pattern' _ _ _ _ _ _ _ = _ ]
                             => etransitivity; rewrite unify_pattern'_cps_id; [ | reflexivity ]
                           end
                         | break_innermost_match_step
                         | break_match_step ltac:(fun _ => idtac) ].
          Qed.

          Lemma app_transport_with_unification_resultT'_cps_id {t p evm1 evm2 K f v T cont}
            : @app_transport_with_unification_resultT'_cps var t p evm1 evm2 K f v T cont
              = (res <- @app_transport_with_unification_resultT'_cps var t p evm1 evm2 K f v _ (@Some _); cont res)%option.
          Proof using Type.
            revert K f v T cont; induction p; cbn [app_transport_with_unification_resultT'_cps]; intros.
            all: repeat first [ progress rewrite_type_transport_correct
                              | progress type_beq_to_eq
                              | progress cbn [Option.bind with_unification_resultT' unification_resultT'] in *
                              | progress subst
                              | reflexivity
                              | progress fold (@with_unification_resultT' ident var pident pident_arg_types)
                              | progress inversion_option
                              | break_innermost_match_step
                              | match goal with
                                | [ H : context G[fun x => ?f x] |- _ ] => let G' := context G[f] in change G' in H
                                | [ |- context G[fun x => ?f x] ] => let G' := context G[f] in change G'
                                | [ H : forall K f v T cont, _ cont = _ |- _ ] => progress cps_id'_with_option H
                                end
                              | progress cbv [Option.bind] ].
          Qed.

          Lemma app_with_unification_resultT_cps_id {t p K f v T cont}
            : @app_with_unification_resultT_cps var t p K f v T cont
              = (res <- @app_with_unification_resultT_cps var t p K f v _ (@Some _); cont res)%option.
          Proof using Type.
            cbv [app_with_unification_resultT_cps].
            repeat first [ progress cbv [Option.bind] in *
                         | reflexivity
                         | progress subst
                         | progress inversion_option
                         | progress break_match
                         | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id ].
          Qed.

          Lemma reveal_rawexpr_cps_gen_id assume_known e T k
            : @reveal_rawexpr_cps_gen ident var assume_known e T k = k (reveal_rawexpr_gen assume_known e).
          Proof.
            cbv [reveal_rawexpr_cps_gen]; break_innermost_match; try reflexivity.
            all: cbv [value value'] in *; expr.invert_match; try reflexivity.
          Qed.

          Lemma reveal_rawexpr_cps_id e T k
            : @reveal_rawexpr_cps ident var e T k = k (reveal_rawexpr e).
          Proof. apply reveal_rawexpr_cps_gen_id. Qed.

          Fixpoint eval_decision_tree_cont_None_ext
                   {T ctx d cont}
                   (Hcont : forall x y, cont x y = None)
                   {struct d}
            : @eval_decision_tree var T ctx d cont = None.
          Proof using Type.
            clear -Hcont eval_decision_tree_cont_None_ext.
            specialize (fun d ctx => @eval_decision_tree_cont_None_ext T ctx d).
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
              rewrite reveal_rawexpr_cps_id.
              all: repeat (rewrite reveal_rawexpr_cps_id; set (reveal_rawexpr_cps _ _ id)).
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

          Lemma eval_decision_tree_cont_None {T ctx d}
            : @eval_decision_tree var T ctx d (fun _ _ => None) = None.
          Proof using Type. apply eval_decision_tree_cont_None_ext; reflexivity. Qed.

          Lemma related1_app_type_of_list_under_type_of_list_relation1_cps
                {A1 ls F f}
            : @under_type_of_list_relation1_cps A1 ls F f
              <-> (forall args, F (app_type_of_list f args)).
          Proof.
            cbv [under_type_of_list_relation1_cps app_type_of_list].
            induction ls as [|l ls IHls]; cbn in *; [ tauto | ].
            setoid_rewrite IHls; split; intro H; intros; first [ apply H | apply (H (_, _)) ].
          Qed.

          Lemma under_type_of_list_relation1_cps_always {A1 ls F v}
                (F_always : forall v, F v : Prop)
            : @under_type_of_list_relation1_cps A1 ls F v.
          Proof using Type.
            cbv [under_type_of_list_relation1_cps] in *.
            induction ls; cbn in *; eauto.
          Qed.
          (*
          Lemma under_with_unification_resultT'_relation1_gen_always
                {t p evm K1 FH F v}
                (F_always : forall v, F v : Prop)
            : @under_with_unification_resultT'_relation1_gen
                ident var pident pident_arg_types t p evm K1 FH F v.
          Proof using Type.
            revert evm K1 F v F_always.
            induction p; intros; cbn in *; eauto using @under_type_of_list_relation1_cps_always.
          Qed.
           *)
        End with_var1.

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
          Local Notation unification_resultT'1 := (@unification_resultT' ident var1 pident pident_arg_types).
          Local Notation unification_resultT'2 := (@unification_resultT' ident var2 pident pident_arg_types).
          Local Notation unification_resultT1 := (@unification_resultT ident var1 pident pident_arg_types).
          Local Notation unification_resultT2 := (@unification_resultT ident var2 pident pident_arg_types).
          Local Notation rewrite_rule_data1 := (@rewrite_rule_data ident var1 pident pident_arg_types type_vars_of_pident).
          Local Notation rewrite_rule_data2 := (@rewrite_rule_data ident var2 pident pident_arg_types type_vars_of_pident).
          Local Notation with_unif_rewrite_ruleTP_gen1 := (@with_unif_rewrite_ruleTP_gen ident var1 pident pident_arg_types type_vars_of_pident).
          Local Notation with_unif_rewrite_ruleTP_gen2 := (@with_unif_rewrite_ruleTP_gen ident var2 pident pident_arg_types type_vars_of_pident).
          Local Notation deep_rewrite_ruleTP_gen1 := (@deep_rewrite_ruleTP_gen ident var1).
          Local Notation deep_rewrite_ruleTP_gen2 := (@deep_rewrite_ruleTP_gen ident var2).
          Local Notation preunify_types1 := (@preunify_types ident var1 pident).
          Local Notation preunify_types2 := (@preunify_types ident var2 pident).
          Local Notation unify_types1 := (@unify_types ident var1 pident).
          Local Notation unify_types2 := (@unify_types ident var2 pident).

          Fixpoint wf_reify {with_lets} G {t}
            : forall e1 e2, @wf_value' with_lets G t e1 e2 -> expr.wf G (@reify _ with_lets t e1) (@reify _ with_lets t e2)
          with wf_reflect {with_lets} G {t}
               : forall e1 e2, expr.wf G e1 e2 -> @wf_value' with_lets G t (@reflect _ with_lets t e1) (@reflect _ with_lets t e2).
          Proof using Type.
            { destruct t as [t|s d];
                [ clear wf_reflect wf_reify
                | specialize (fun with_lets G => @wf_reify with_lets G d); specialize (fun with_lets G => wf_reflect with_lets G s) ].
              { destruct with_lets; cbn; intros; auto using UnderLets.wf_to_expr. }
              { intros e1 e2 Hwf.
                change (reify e1) with (λ x, @reify _ _ d (e1 (@reflect _ _ s ($x))))%expr.
                change (reify e2) with (λ x, @reify _ _ d (e2 (@reflect _ _ s ($x))))%expr.
                constructor; intros; eapply wf_reify, Hwf with (seg:=cons _ nil); [ | eapply wf_reflect; constructor ]; wf_t. } }
            { destruct t as [t|s d];
                [ clear wf_reflect wf_reify
                | specialize (fun with_lets G => @wf_reify with_lets G s); specialize (fun with_lets G => wf_reflect with_lets G d) ].
              { destruct with_lets; repeat constructor; auto. }
              { intros e1 e2 Hwf.
                change (reflect e1) with (fun x => @reflect _ true d (e1 @ (@reify _ false s x)))%expr.
                change (reflect e2) with (fun x => @reflect _ true d (e2 @ (@reify _ false s x)))%expr.
                hnf; intros; subst.
                eapply wf_reflect; constructor; [ wf_t | ].
                eapply wf_reify, wf_value'_Proper_list; [ | eassumption ]; wf_t. } }
          Qed.

          Lemma wf_reify_and_let_binds_cps {with_lets} G {t} x1 x2
                (Hx : @wf_value' with_lets G t x1 x2)
                T1 T2 P
                (e1 : expr t -> @UnderLets var1 T1) (e2 : expr t -> @UnderLets var2 T2)
                (He : forall x1 x2 G' seg, (G' = (seg ++ G)%list) -> expr.wf G' x1 x2 -> UnderLets.wf P G' (e1 x1) (e2 x2))
            : UnderLets.wf P G (@reify_and_let_binds_cps1 with_lets t x1 T1 e1) (@reify_and_let_binds_cps2 with_lets t x2 T2 e2).
          Proof.
            destruct t; [ destruct with_lets | ]; cbn [reify_and_let_binds_cps]; auto.
            { eapply UnderLets.wf_splice; [ eapply Hx | ]; wf_t; destruct_head'_ex; wf_t.
              eapply wf_reify_and_let_binds_base_cps; wf_t.
              eapply He; rewrite app_assoc; wf_t. }
            { eapply He with (seg:=nil); [ reflexivity | ].
              eapply wf_reify; auto. }
          Qed.

          Lemma wf_reify_expr G G' {t}
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> @wf_value G' t v1 v2)
                e1 e2
                (Hwf : expr.wf G e1 e2)
            : expr.wf G' (@reify_expr var1 t e1) (@reify_expr var2 t e2).
          Proof using Type.
            cbv [wf_value] in *; revert dependent G'; induction Hwf; intros; cbn [reify_expr];
              first [ constructor | apply wf_reify ]; eauto; intros.
            all: match goal with H : _ |- _ => apply H end.
            all: repeat first [ progress cbn [In eq_rect] in *
                              | progress intros
                              | progress destruct_head'_or
                              | progress subst
                              | progress inversion_sigma
                              | progress inversion_prod
                              | apply wf_reflect
                              | solve [ eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; wf_safe_t ]
                              | constructor ].
          Qed.

          Inductive wf_rawexpr : list { t : type & var1 t * var2 t }%type -> forall {t}, @rawexpr var1 -> @expr var1 t -> @rawexpr var2 -> @expr var2 t -> Prop :=
          | Wf_rIdent {t} G known (idc : ident t) : wf_rawexpr G (rIdent known idc (expr.Ident idc)) (expr.Ident idc) (rIdent known idc (expr.Ident idc)) (expr.Ident idc)
          | Wf_rApp {s d} G
                    f1 (f1e : @expr var1 (s -> d)) x1 (x1e : @expr var1 s)
                    f2 (f2e : @expr var2 (s -> d)) x2 (x2e : @expr var2 s)
            : wf_rawexpr G f1 f1e f2 f2e
              -> wf_rawexpr G x1 x1e x2 x2e
              -> wf_rawexpr G
                            (rApp f1 x1 (expr.App f1e x1e)) (expr.App f1e x1e)
                            (rApp f2 x2 (expr.App f2e x2e)) (expr.App f2e x2e)
          | Wf_rExpr {t} G (e1 e2 : expr t)
            : expr.wf G e1 e2 -> wf_rawexpr G (rExpr e1) e1 (rExpr e2) e2
          | Wf_rValue {t} G (v1 v2 : value t)
            : wf_value G v1 v2
              -> wf_rawexpr G (rValue v1) (reify v1) (rValue v2) (reify v2).

          Lemma wf_rawexpr_Proper_list G1 G2
                (HG1G2 : forall t v1 v2, List.In (existT _ t (v1, v2)) G1 -> List.In (existT _ t (v1, v2)) G2)
                t re1 e1 re2 e2
                (Hwf : @wf_rawexpr G1 t re1 e1 re2 e2)
            : @wf_rawexpr G2 t re1 e1 re2 e2.
          Proof.
            revert dependent G2; induction Hwf; intros; constructor; eauto.
            { eapply expr.wf_Proper_list; eauto. }
            { eapply wf_value'_Proper_list; eauto. }
          Qed.

          (* Because [proj1] and [proj2] in the stdlib are opaque *)
          Local Notation proj1 x := (let (a, b) := x in a).
          Local Notation proj2 x := (let (a, b) := x in b).

          Definition eq_type_of_rawexpr_of_wf {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : type_of_rawexpr re1 = t /\ type_of_rawexpr re2 = t.
          Proof. split; destruct Hwf; reflexivity. Defined.

          Definition eq_expr_of_rawexpr_of_wf {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : (rew [expr] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re1) = e1
              /\ (rew [expr] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re2) = e2.
          Proof. split; destruct Hwf; reflexivity. Defined.

          Definition eq_expr_of_rawexpr_of_wf' {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr_of_rawexpr re1 = (rew [expr] (eq_sym (proj1 (eq_type_of_rawexpr_of_wf Hwf))) in e1)
              /\ expr_of_rawexpr re2 = (rew [expr] (eq_sym (proj2 (eq_type_of_rawexpr_of_wf Hwf))) in e2).
          Proof. split; destruct Hwf; reflexivity. Defined.

          Lemma wf_expr_of_wf_rawexpr {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr.wf G e1 e2.
          Proof. induction Hwf; repeat (assumption || constructor || apply wf_reify). Qed.

          Lemma wf_expr_of_wf_rawexpr' {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr.wf G
                      (rew [expr] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re1)
                      (rew [expr] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re2).
          Proof.
            pose proof Hwf as Hwf'.
            rewrite <- (proj1 (eq_expr_of_rawexpr_of_wf Hwf)) in Hwf'.
            rewrite <- (proj2 (eq_expr_of_rawexpr_of_wf Hwf)) in Hwf'.
            eapply wf_expr_of_wf_rawexpr; eassumption.
          Qed.

          Lemma wf_value_of_wf_rawexpr {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : wf_value G
                       (rew [value] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in value_of_rawexpr re1)
                       (rew [value] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in value_of_rawexpr re2).
          Proof.
            pose proof (wf_expr_of_wf_rawexpr Hwf).
            destruct Hwf; cbn; try eapply wf_reflect; try assumption.
          Qed.

          Lemma wf_value_of_wf_rawexpr_gen {t t' G re1 e1 re2 e2}
                {pf1 pf2 : _ = t'}
                (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : wf_value G
                       (rew [value] pf1 in value_of_rawexpr re1)
                       (rew [value] pf2 in value_of_rawexpr re2).
          Proof using Type.
            assert (H : t = t');
              [
              | destruct H;
                replace pf1 with (proj1 (eq_type_of_rawexpr_of_wf Hwf));
                [ replace pf2 with (proj2 (eq_type_of_rawexpr_of_wf Hwf)) | ] ];
              [ | apply wf_value_of_wf_rawexpr | | ];
              destruct (eq_type_of_rawexpr_of_wf Hwf); generalize dependent (type_of_rawexpr re1); generalize dependent (type_of_rawexpr re2); intros; subst; clear; eliminate_hprop_eq; reflexivity.
          Qed.

          Lemma wf_reveal_rawexpr t G re1 e1 re2 e2 (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : @wf_rawexpr G t (reveal_rawexpr re1) e1 (reveal_rawexpr re2) e2.
          Proof.
            pose proof (wf_expr_of_wf_rawexpr Hwf).
            destruct Hwf; cbv [reveal_rawexpr_cps reveal_rawexpr_cps_gen id];
              repeat first [ assumption
                           | constructor
                           | progress subst
                           | progress cbn [reify eq_rect value value'] in *
                           | progress destruct_head'_sig
                           | progress destruct_head'_and
                           | break_innermost_match_step
                           | progress expr.invert_match
                           | progress expr.inversion_wf_constr ].
          Qed.

          Lemma related_app_type_of_list_of_under_type_of_list_relation_cps {K1 K2 ls args}
                {v1 v2}
                (P : _ -> _ -> Prop)
            : @under_type_of_list_relation_cps K1 K2 ls P v1 v2
              -> P (app_type_of_list v1 args) (app_type_of_list v2 args).
          Proof using Type.
            induction ls as [|x ls IHls]; [ now (cbn; eauto) | ].
            (* N.B. [simpl] does more refolding than [cbn], and it's important that we use [simpl] and not [cbn] here *)
            intro H; cbn in args, v1, v2; simpl in *; eauto.
          Qed.

          Lemma wf_preunify_types {G t t' re1 e1 re2 e2 p}
                (H : @wf_rawexpr G t' re1 e1 re2 e2)
            : @preunify_types1 t re1 p = @preunify_types2 t re2 p.
          Proof using Type.
            revert G t' re1 e1 re2 e2 H.
            induction p; cbn; intros; destruct H; cbn in *; try reflexivity.
            repeat match goal with H : _ |- _ => erewrite H by eassumption; clear H end;
              reflexivity.
          Qed.

          Lemma wf_unify_types {G t t' re1 e1 re2 e2 p}
                (H : @wf_rawexpr G t' re1 e1 re2 e2)
            : @unify_types1 t re1 p _ id = @unify_types2 t re2 p _ id.
          Proof using Type.
            cbv [unify_types]; erewrite wf_preunify_types by eassumption.
            reflexivity.
          Qed.

          Lemma wf_unify_types_cps {G t t' re1 e1 re2 e2 p T K}
                (H : @wf_rawexpr G t' re1 e1 re2 e2)
            : @unify_types1 t re1 p T K = @unify_types2 t re2 p T K.
          Proof using Type.
            etransitivity; rewrite unify_types_cps_id; [ | reflexivity ].
            erewrite wf_unify_types by eassumption; reflexivity.
          Qed.

          Fixpoint related_unification_resultT' (R : forall t, @value var1 t -> @value var2 t -> Prop) {t p evm}
            : @unification_resultT'1 t p evm -> @unification_resultT'2 t p evm -> Prop
            := match p return unification_resultT'1 p evm -> unification_resultT'2 p evm -> Prop with
               | pattern.Wildcard t => R _
               | pattern.Ident t idc => eq
               | pattern.App s d f x
                 => fun (v1 : unification_resultT'1 f evm * unification_resultT'1 x evm)
                        (v2 : unification_resultT'2 f evm * unification_resultT'2 x evm)
                    => @related_unification_resultT' R _ _ _ (fst v1) (fst v2)
                       /\ @related_unification_resultT' R  _ _ _ (snd v1) (snd v2)
               end.

          Definition wf_unification_resultT' (G : list {t1 : type & (var1 t1 * var2 t1)%type}) {t p evm}
            : @unification_resultT'1 t p evm -> @unification_resultT'2 t p evm -> Prop
            := @related_unification_resultT' (fun _ => wf_value G) t p evm.

          Definition related_unification_resultT (R : forall t, @value var1 t -> @value var2 t -> Prop) {t p}
            : @unification_resultT1 t p -> @unification_resultT2 t p -> Prop
            := related_sigT_by_eq (@related_unification_resultT' R t p).

          Definition wf_unification_resultT (G : list {t1 : type & (var1 t1 * var2 t1)%type}) {t p}
            : @unification_resultT1 t p -> @unification_resultT2 t p -> Prop
            := @related_unification_resultT (fun _ => wf_value G) t p.

          Fixpoint under_with_unification_resultT'_relation_hetero {t p evm K1 K2}
                   (FH : forall t, value t -> value t -> Prop)
                   (F : K1 -> K2 -> Prop)
                   {struct p}
            : @with_unification_resultT'1 t p evm K1 -> @with_unification_resultT'2 t p evm K2 -> Prop
            := match p return with_unification_resultT'1 p evm K1 -> with_unification_resultT'2 p evm K2 -> Prop with
               | pattern.Wildcard t => fun f1 f2 => forall v1 v2, FH _ v1 v2 -> F (f1 v1) (f2 v2)
               | pattern.Ident t idc => under_type_of_list_relation_cps F
               | pattern.App s d f x
                 => @under_with_unification_resultT'_relation_hetero
                      _ f evm _ _
                      FH
                      (@under_with_unification_resultT'_relation_hetero _ x evm _ _ FH F)
               end.

          Definition under_with_unification_resultT_relation_hetero {t p K1 K2}
                     (FH : forall t, value t -> value t -> Prop)
                     (F : forall evm, K1 (pattern.type.subst_default t evm) -> K2 (pattern.type.subst_default t evm) -> Prop)
            : @with_unification_resultT1 t p K1 -> @with_unification_resultT2 t p K2 -> Prop
            := pattern.type.under_forall_vars_relation
                 (fun evm => under_with_unification_resultT'_relation_hetero FH (F evm)).

          Definition wf_with_unification_resultT
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t} {p : pattern t} {K1 K2 : type -> Type}
                     (P : forall evm, K1 (pattern.type.subst_default t evm) -> K2 (pattern.type.subst_default t evm) -> Prop)
            : @with_unification_resultT1 t p K1 -> @with_unification_resultT2 t p K2 -> Prop
            := under_with_unification_resultT_relation_hetero
                 (fun t => wf_value G)
                 P.

          Lemma related_app_with_unification_resultT' {t p evm K1 K2}
                R1 R2
                f1 f2 v1 v2
            : @under_with_unification_resultT'_relation_hetero
                t p evm K1 K2 R1 R2 f1 f2
              -> @related_unification_resultT' R1 t p evm v1 v2
              -> R2 (@app_with_unification_resultT' _ _ _ _ t p evm K1 f1 v1)
                    (@app_with_unification_resultT' _ _ _ _ t p evm K2 f2 v2).
          Proof using Type.
            revert K1 K2 R1 R2 f1 f2 v1 v2; induction p; cbn in *; intros; subst; destruct_head'_and;
              try apply related_app_type_of_list_of_under_type_of_list_relation_cps;
              auto.
            repeat match goal with H : _ |- _ => eapply H; eauto; clear H end.
          Qed.

          Lemma related_app_transport_with_unification_resultT' {t p evm1 evm2 K1 K2}
                R1 R2
                f1 f2 v1 v2
            : @under_with_unification_resultT'_relation_hetero
                t p evm1 K1 K2 R1 R2 f1 f2
              -> @related_unification_resultT' R1 t p evm2 v1 v2
              -> option_eq
                   R2
                   (@app_transport_with_unification_resultT'_cps _ t p evm1 evm2 K1 f1 v1 _ (@Some _))
                   (@app_transport_with_unification_resultT'_cps _ t p evm1 evm2 K2 f2 v2 _ (@Some _)).
          Proof using Type.
            revert K1 K2 R1 R2 f1 f2 v1 v2; induction p; cbn in *; intros; subst; destruct_head'_and;
              try apply related_app_type_of_list_of_under_type_of_list_relation_cps;
              auto.
            all: repeat first [ progress rewrite_type_transport_correct
                              | progress type_beq_to_eq
                              | break_innermost_match_step
                              | reflexivity
                              | progress cbn [Option.bind option_eq] in *
                              | progress fold (@with_unification_resultT'1) (@with_unification_resultT'2)
                              | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                              | progress cbv [eq_rect]
                              | solve [ auto ]
                              | exfalso; assumption
                              | progress inversion_option
                              | match goal with
                                | [ H : (forall K1 K2 R1 R2 (f1 : with_unification_resultT'1 ?p1 ?evm1 K1), _)
                                    |- context[@app_transport_with_unification_resultT'_cps _ ?t ?p1 ?evm1 ?evm2 ?K1' ?f1' ?v1' _ _] ]
                                  => specialize (H K1' _ _ _ f1' _ v1' _ ltac:(eassumption) ltac:(eassumption))
                                | [ H : option_eq ?R ?x ?y |- _ ]
                                  => destruct x eqn:?, y eqn:?; cbv [option_eq] in H
                                end ].
          Qed.

          Lemma related_app_with_unification_resultT {t p K1 K2}
                R1 R2
                f1 f2 v1 v2
            : @under_with_unification_resultT_relation_hetero
                t p K1 K2 R1 R2 f1 f2
              -> @related_unification_resultT R1 t p v1 v2
              -> option_eq
                   (related_sigT_by_eq R2)
                   (@app_with_unification_resultT_cps _ t p K1 f1 v1 _ (@Some _))
                   (@app_with_unification_resultT_cps _ t p K2 f2 v2 _ (@Some _)).
          Proof using Type.
            cbv [related_unification_resultT under_with_unification_resultT_relation_hetero app_with_unification_resultT_cps related_sigT_by_eq unification_resultT] in *.
            repeat first [ progress destruct_head'_sigT
                         | progress destruct_head'_sig
                         | progress subst
                         | progress intros
                         | progress cbn [eq_rect Option.bind projT1 projT2 option_eq] in *
                         | exfalso; assumption
                         | progress inversion_option
                         | reflexivity
                         | (exists eq_refl)
                         | assumption
                         | match goal with
                           | [ H : pattern.type.under_forall_vars_relation ?R ?f1 ?f2
                               |- context[pattern.type.app_forall_vars ?f1 ?x] ]
                             => apply (pattern.type.app_forall_vars_under_forall_vars_relation (evm:=x)) in H
                           | [ H : option_eq ?R ?x ?y |- _ ]
                             => destruct x eqn:?, y eqn:?; cbv [option_eq] in H
                           end
                         | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                         | match goal with
                           | [ H : under_with_unification_resultT'_relation_hetero _ _ _ _, H' : related_unification_resultT' _ _ _ |- _ ]
                             => pose proof (related_app_transport_with_unification_resultT' _ _ _ _ _ _ H H'); clear H'
                           end ].
          Qed.

          Lemma wf_app_with_unification_resultT G {t p K1 K2}
                R
                f1 f2 v1 v2
            : @wf_with_unification_resultT G t p K1 K2 R f1 f2
              -> @wf_unification_resultT G t p v1 v2
              -> option_eq
                   (related_sigT_by_eq R)
                   (@app_with_unification_resultT_cps _ t p K1 f1 v1 _ (@Some _))
                   (@app_with_unification_resultT_cps _ t p K2 f2 v2 _ (@Some _)).
          Proof using Type. apply related_app_with_unification_resultT. Qed.

          Definition map_related_unification_resultT' {R1 R2 : forall t : type, value t -> value t -> Prop}
                     (HR : forall t v1 v2, R1 t v1 v2 -> R2 t v1 v2)
                     {t p evm v1 v2}
            : @related_unification_resultT' R1 t p evm v1 v2
              -> @related_unification_resultT' R2 t p evm v1 v2.
          Proof using Type.
            induction p; cbn [related_unification_resultT']; intuition auto.
          Qed.

          Definition map_related_unification_resultT {R1 R2 : forall t : type, value t -> value t -> Prop}
                     (HR : forall t v1 v2, R1 t v1 v2 -> R2 t v1 v2)
                     {t p v1 v2}
            : @related_unification_resultT R1 t p v1 v2
              -> @related_unification_resultT R2 t p v1 v2.
          Proof using Type.
            cbv [related_unification_resultT]; apply map_related_sigT_by_eq; intros *.
            apply map_related_unification_resultT'; auto.
          Qed.

          Definition wf_maybe_do_again_expr
                     {t}
                     {rew_should_do_again1 rew_should_do_again2 : bool}
                     (G : list {t : _ & (var1 t * var2 t)%type})
            : expr (var:=if rew_should_do_again1 then @value var1 else var1) t
              -> expr (var:=if rew_should_do_again2 then @value var2 else var2) t
              -> Prop
            := match rew_should_do_again1, rew_should_do_again2
                     return expr (var:=if rew_should_do_again1 then @value var1 else var1) t
                            -> expr (var:=if rew_should_do_again2 then @value var2 else var2) t
                            -> Prop
               with
               | true, true
                 => fun e1 e2
                    => exists G',
                        (forall t' v1' v2', List.In (existT _ t' (v1', v2')) G' -> wf_value G v1' v2')
                        /\ expr.wf G' e1 e2
               | false, false => expr.wf G
               | _, _ => fun _ _ => False
               end.

          Definition wf_maybe_under_lets_expr
                     {T1 T2}
                     (P : list {t : _ & (var1 t * var2 t)%type} -> T1 -> T2 -> Prop)
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {rew_under_lets1 rew_under_lets2 : bool}
            : (if rew_under_lets1 then UnderLets var1 T1 else T1)
              -> (if rew_under_lets2 then UnderLets var2 T2 else T2)
              -> Prop
            := match rew_under_lets1, rew_under_lets2
                     return (if rew_under_lets1 then UnderLets var1 T1 else T1)
                            -> (if rew_under_lets2 then UnderLets var2 T2 else T2)
                            -> Prop
               with
               | true, true
                 => UnderLets.wf P G
               | false, false
                 => P G
               | _, _ => fun _ _ => False
               end.

          Definition maybe_option_eq {A B} {opt1 opt2 : bool} (R : A -> B -> Prop)
            : (if opt1 then option A else A) -> (if opt2 then option B else B) -> Prop
            := match opt1, opt2 with
               | true, true => option_eq R
               | false, false => R
               | _, _ => fun _ _ => False
               end.

          Definition wf_deep_rewrite_ruleTP_gen
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t}
                     {rew_should_do_again1 rew_with_opt1 rew_under_lets1 : bool}
                     {rew_should_do_again2 rew_with_opt2 rew_under_lets2 : bool}
            : deep_rewrite_ruleTP_gen1 rew_should_do_again1 rew_with_opt1 rew_under_lets1 t
              -> deep_rewrite_ruleTP_gen2 rew_should_do_again2 rew_with_opt2 rew_under_lets2 t
              -> Prop
            := maybe_option_eq
                 (wf_maybe_under_lets_expr
                    wf_maybe_do_again_expr
                    G).

          Definition wf_with_unif_rewrite_ruleTP_gen
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t} {p : pattern t}
                     {rew_should_do_again1 rew_with_opt1 rew_under_lets1}
                     {rew_should_do_again2 rew_with_opt2 rew_under_lets2}
            : with_unif_rewrite_ruleTP_gen1 p rew_should_do_again1 rew_with_opt1 rew_under_lets1
              -> with_unif_rewrite_ruleTP_gen2 p rew_should_do_again2 rew_with_opt2 rew_under_lets2
              -> Prop
            := fun f g
               => forall x y,
                   wf_unification_resultT G x y
                   -> option_eq
                        (fun (fx : { evm : _ & deep_rewrite_ruleTP_gen1 rew_should_do_again1 rew_with_opt1 rew_under_lets1 _ })
                             (gy : { evm : _ & deep_rewrite_ruleTP_gen2 rew_should_do_again2 rew_with_opt2 rew_under_lets2 _ })
                         => related_sigT_by_eq
                              (fun _ => wf_deep_rewrite_ruleTP_gen G) fx gy)
                        (app_with_unification_resultT_cps _ f x _ (@Some _))
                        (app_with_unification_resultT_cps _ g y _ (@Some _)).

          Definition wf_rewrite_rule_data
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t} {p : pattern t}
                     (r1 : @rewrite_rule_data1 t p)
                     (r2 : @rewrite_rule_data2 t p)
            : Prop
            := wf_with_unif_rewrite_ruleTP_gen G (rew_replacement _ _ r1) (rew_replacement _ _ r2).

          Definition rewrite_rules_goodT
                     (rew1 : rewrite_rulesT1) (rew2 : rewrite_rulesT2)
            : Prop
            := length rew1 = length rew2
               /\ (forall p1 r1 p2 r2,
                      List.In (existT _ p1 r1, existT _ p2 r2) (combine rew1 rew2)
                      -> { pf : p1 = p2
                         | forall G,
                             wf_rewrite_rule_data
                               G
                               (rew [fun tp => @rewrite_rule_data1 _ (pattern.pattern_of_anypattern tp)] pf in r1)
                               r2 }).

          Definition wf_with_unif_rewrite_ruleTP_gen_curried
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t} {p : pattern t}
                     {rew_should_do_again1 rew_with_opt1 rew_under_lets1}
                     {rew_should_do_again2 rew_with_opt2 rew_under_lets2}
            : with_unif_rewrite_ruleTP_gen1 p rew_should_do_again1 rew_with_opt1 rew_under_lets1
              -> with_unif_rewrite_ruleTP_gen2 p rew_should_do_again2 rew_with_opt2 rew_under_lets2
              -> Prop
            := wf_with_unification_resultT
                 G
                 (fun evm => wf_deep_rewrite_ruleTP_gen G).

          Definition wf_rewrite_rule_data_curried
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t} {p : pattern t}
                     (r1 : @rewrite_rule_data1 t p)
                     (r2 : @rewrite_rule_data2 t p)
            : Prop
            := wf_with_unif_rewrite_ruleTP_gen_curried G (rew_replacement _ _ r1) (rew_replacement _ _ r2).

          Definition rewrite_rules_goodT_curried
                     (rew1 : rewrite_rulesT1) (rew2 : rewrite_rulesT2)
            : Prop
            := length rew1 = length rew2
               /\ (forall p1 r1 p2 r2,
                      List.In (existT _ p1 r1, existT _ p2 r2) (combine rew1 rew2)
                      -> { pf : p1 = p2
                         | forall G,
                             wf_rewrite_rule_data_curried
                               G
                               (rew [fun tp => @rewrite_rule_data1 _ (pattern.pattern_of_anypattern tp)] pf in r1)
                               r2 }).

          Lemma rewrite_rules_goodT_by_curried rew1 rew2
            : rewrite_rules_goodT_curried rew1 rew2 -> rewrite_rules_goodT rew1 rew2.
          Proof using Type.
            cbv [rewrite_rules_goodT rewrite_rules_goodT_curried wf_rewrite_rule_data_curried wf_rewrite_rule_data wf_with_unif_rewrite_ruleTP_gen wf_with_unif_rewrite_ruleTP_gen_curried].
            intros [Hlen H]; split; [ exact Hlen | clear Hlen ].
            repeat (let x := fresh "x" in intro x; specialize (H x)).
            destruct H as [H0 H]; exists H0.
            repeat (let x := fresh "x" in intro x; specialize (H x)).
            intros X Y HXY.
            pose proof (wf_app_with_unification_resultT _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)) as H'.
            cps_id'_with_option app_with_unification_resultT_cps_id.
            cbv [deep_rewrite_ruleTP_gen] in *.
            let H1 := fresh in
            let H2 := fresh in
            lazymatch type of H' with
            | option_eq ?R ?x ?y
              => destruct x eqn:H1, y eqn:H2; cbv [option_eq] in H'
            end.
            all: repeat first [ progress cbn [option_eq]
                              | reflexivity
                              | progress inversion_option
                              | exfalso; assumption
                              | assumption ].
          Qed.
        End with_var2.

        Section with_interp.
          Context (ident_interp : forall t, ident t -> type.interp base.interp t)
                  {ident_interp_Proper : forall t, Proper (eq ==> type.eqv) (ident_interp t)}.
          Local Notation var := (type.interp base.interp) (only parsing).
          Local Notation expr := (@expr.expr base.type ident var).
          Local Notation rewrite_rulesT := (@rewrite_rulesT ident var pident pident_arg_types type_vars_of_pident).
          Local Notation rewrite_rule_data := (@rewrite_rule_data ident var pident pident_arg_types type_vars_of_pident).
          Local Notation with_unif_rewrite_ruleTP_gen := (@with_unif_rewrite_ruleTP_gen ident var pident pident_arg_types type_vars_of_pident).
          Local Notation with_unification_resultT' := (@with_unification_resultT' ident var pident pident_arg_types).
          Local Notation normalize_deep_rewrite_rule := (@normalize_deep_rewrite_rule ident var).

          Local Notation deep_rewrite_ruleTP_gen := (@deep_rewrite_ruleTP_gen ident var).

          Local Notation UnderLets_maybe_interp with_lets
            := (if with_lets as with_lets' return (if with_lets' then UnderLets var _ else _) -> _
                then UnderLets.interp ident_interp
                else (fun x => x)).

          Definition value'_interp {with_lets t} (v : @value' var with_lets t)
            : var t
            := expr.interp ident_interp (reify v).

          Fixpoint value'_interp_related
                   {with_lets1 with_lets2 t}
            : @value' var with_lets1 t
              -> @value' var with_lets2 t
              -> Prop
            := match t return value' _ t -> value' _ t -> Prop with
               | type.base t
                 => fun v1 v2
                    => expr.interp ident_interp (UnderLets_maybe_interp with_lets1 v1)
                       == expr.interp ident_interp (UnderLets_maybe_interp with_lets2 v2)
               | type.arrow s d
                 => fun (f1 f2 : value' _ s -> value' _ d)
                    => forall x1 x2,
                        @value'_interp_related _ _ s x1 x2
                        -> @value'_interp_related _ _ d (f1 x1) (f2 x2)
               end.

          Local Infix "===" := value'_interp_related : type_scope.

          Definition value_interp_related {t} : relation (@value var t)
            := value'_interp_related.

          Definition value_interp_ok {with_lets t} : @value' var with_lets t -> Prop
            := fun v => value'_interp_related v v.

          Lemma value'_interp_related_sym_iff {with_lets1 with_lets2 t v1 v2}
            : @value'_interp_related with_lets1 with_lets2 t v1 v2
              <-> @value'_interp_related with_lets2 with_lets1 t v2 v1.
          Proof using Type.
            split; revert with_lets1 with_lets2 v1 v2; induction t as [|s IHs d IHd];
              cbn [value'_interp_related]; intros.
            all: solve [ symmetry; assumption | eauto ].
          Qed.

          Lemma value'_interp_related_trans {with_lets1 with_lets2 with_lets3 t v1 v2 v3}
            : @value'_interp_related with_lets1 with_lets2 t v1 v2
              -> @value'_interp_related with_lets2 with_lets3 t v2 v3
              -> @value'_interp_related with_lets1 with_lets3 t v1 v3.
          Proof using Type.
            intros H0 H1; revert with_lets1 with_lets2 with_lets3 v1 v2 v3 H0 H1; induction t as [|s IHs d IHd];
              cbn [value'_interp_related]; intros.
            all: try solve [ etransitivity; eassumption ].
            eapply IHd; [ eapply H0; eassumption | eapply H1 ].
            eapply IHs; [ eapply value'_interp_related_sym_iff | ]; eassumption.
          Qed.

          Global Instance value'_interp_related_Symmetric {with_lets t}
            : Symmetric (@value'_interp_related with_lets with_lets t) | 10
            := fun v1 v2 => proj1 value'_interp_related_sym_iff.
          Global Instance value'_interp_related_Transitive {with_lets t}
            : Transitive (@value'_interp_related with_lets with_lets t) | 10
            := fun v1 v2 v3 => value'_interp_related_trans.

          Lemma value_interp_related_sym_iff {t v1 v2}
            : @value_interp_related t v1 v2
              <-> @value_interp_related t v2 v1.
          Proof using Type. apply value'_interp_related_sym_iff. Qed.

          Lemma value_interp_related_trans {t v1 v2 v3}
            : @value_interp_related t v1 v2
              -> @value_interp_related t v2 v3
              -> @value_interp_related t v1 v3.
          Proof using Type. apply value'_interp_related_trans. Qed.

          Global Instance value_interp_related_Symmetric {t}
            : Symmetric (@value_interp_related t) | 10
            := fun v1 v2 => proj1 value_interp_related_sym_iff.
          Global Instance value_interp_related_Transitive {t}
            : Transitive (@value_interp_related t) | 10
            := fun v1 v2 v3 => value_interp_related_trans.

          Lemma interp_Base_value {with_lets2 t} v1 (v2 : value' with_lets2 t)
            : v1 === v2 -> @Base_value var t v1 === v2.
          Proof using Type.
            cbv [Base_value]; break_innermost_match; destruct with_lets2; cbn [value'_interp_related UnderLets.interp];
              exact id.
          Qed.

          Fixpoint value_interp_related_reify {with_lets1 with_lets2 t e1 e2} {struct t}
            : e1 === e2
              -> expr.interp ident_interp (@reify var with_lets1 t e1) == expr.interp ident_interp (@reify var with_lets2 t e2)
          with value_interp_related_reflect {with_lets1 with_lets2 t e1 e2} {struct t}
            : expr.interp ident_interp e1 == expr.interp ident_interp e2
              -> @reflect var with_lets1 t e1 === @reflect var with_lets2 t e2.
          Proof using Type.
            all: destruct t as [t|s d];
              [ clear value_interp_related_reflect value_interp_related_reify
              | pose proof (fun with_lets1 with_lets2 => value_interp_related_reify with_lets1 with_lets2 s) as value_interp_related_reify_s;
                pose proof (fun with_lets1 with_lets2 => value_interp_related_reify with_lets1 with_lets2 d) as value_interp_related_reify_d;
                pose proof (fun with_lets1 with_lets2 => value_interp_related_reflect with_lets1 with_lets2 s) as value_interp_related_reflect_s;
                pose proof (fun with_lets1 with_lets2 => value_interp_related_reflect with_lets1 with_lets2 d) as value_interp_related_reflect_d;
                clear value_interp_related_reify value_interp_related_reflect ].

            all: repeat first [ progress cbn [reflect reify type.related value'_interp_related expr.interp] in *
                              | progress cbv [respectful]
                              | progress fold (@reify) (@reflect) in *
                              | break_innermost_match_step
                              | rewrite UnderLets.interp_to_expr
                              | exact id
                              | progress intros
                              | match goal with
                                | [ H : _ |- _ ] => apply H; clear H
                                end ].
          Qed.

          Lemma interp_reify_reflect {with_lets t} e v
            : expr.interp ident_interp e == v -> expr.interp ident_interp (@reify _ with_lets t (reflect e)) == v.
          Proof using Type.
            revert with_lets; induction t as [|s IHs d IHd]; intro;
              cbn [type.related reflect reify];
              fold (@reify var) (@reflect var); cbv [respectful]; break_innermost_match;
                cbn [expr.interp UnderLets.to_expr]; auto; [].
            intros Hf ? ? Hx.
            apply IHd; cbn [expr.interp]; auto.
          Qed.

          Lemma interp_reflect_reify {with_lets with_lets1 with_lets2 t} x y
            : @value'_interp_related with_lets with_lets2 t x y -> @value'_interp_related with_lets1 with_lets2 t (reflect (@reify _ with_lets t x)) y.
          Proof using Type.
            revert with_lets with_lets1 with_lets2 x y; induction t as [|s IHs d IHd]; intros ? ? ? ? ?;
              cbn [type.related value'_interp_related reflect reify] in *;
              fold (@reify var) (@reflect var); cbv [respectful]; break_innermost_match;
                cbn [expr.interp UnderLets.to_expr UnderLets.interp]; rewrite ?UnderLets.interp_to_expr; auto; [].
            intros Hf ? ? Hx.
            etransitivity.
            { eapply value_interp_related_reflect; cbn [expr.interp].
              eapply value_interp_related_reify.
              eapply Hf.
              eapply value_interp_related_reflect; cbn [expr.interp].
              eapply value_interp_related_reify; eassumption. }
            { etransitivity; [ eapply IHd; symmetry | ]; eapply Hf; [ symmetry | eassumption ].
              eapply IHs; symmetry; eassumption. }
          Qed.

          Lemma value_interp_related_of_ok {with_lets1 with_lets2 t v1 v2}
            : @value'_interp_related with_lets1 with_lets2 t v1 v2
              -> value'_interp v1 == value'_interp v2.
          Proof using Type.
            revert with_lets1 with_lets2 v1 v2; induction t as [|s IHs d IHd].
            { cbn; intros; break_innermost_match; rewrite ?UnderLets.interp_to_expr; assumption. }
            { cbn [type.related value'_interp value'_interp_related value']; cbv [respectful].
              intros.
              apply IHd; fold (@reify var) (@reflect var).
              match goal with H : _ |- _ => apply H end.
              apply value_interp_related_reflect; cbn [expr.interp]; assumption. }
          Qed.

          Local Ltac t_value_interp_related :=
            repeat match goal with
                   | _ => progress cbn [expr.interp]
                   | [ |- expr.interp ?ii ?e == ?v ]
                     => is_var v; is_evar e; refine (_ : expr.interp ii (expr.Var v) == v)
                   | [ H : ?R ?x ?y |- ?R ?x ?x ]
                     => etransitivity; (idtac + symmetry); eassumption
                   | [ H : ?R ?y ?x |- ?R ?x ?x ]
                     => etransitivity; (idtac + symmetry); eassumption
                   | [ |- expr.interp _ (reify _) == expr.interp _ (reify _) ]
                     => eapply value_interp_related_reify
                   | [ |- reflect _ === reflect _ ]
                     => eapply value_interp_related_reflect
                   | [ |- reflect (expr.Var _) === _ ]
                     => etransitivity; [ eapply value_interp_related_reflect | ]
                   | [ |- _ === reflect (expr.Var _) ]
                     => etransitivity; [ | eapply value_interp_related_reflect ]
                   | [ |- _ === reflect ?v ]
                     => is_evar v; symmetry; eapply interp_reflect_reify
                   | [ |- reflect ?v === _ ]
                     => is_evar v; eapply interp_reflect_reify
                   | [ |- _ == expr.interp _ (reify ?v) ]
                     => is_evar v; symmetry; eapply interp_reify_reflect
                   | [ |- expr.interp _ (reify ?v) == _ ]
                     => is_evar v; eapply interp_reify_reflect
                   | [ |- expr.interp _ (reify ?x) == ?v ]
                     => is_var x; is_evar v; eapply value_interp_related_reify
                   | [ |- ?v == expr.interp _ (reify ?x) ]
                     => is_var x; is_evar v; eapply value_interp_related_reify
                   | [ |- expr.interp _ (reify ?x) == expr.interp _ ?v ]
                     => is_var x; is_evar v; eapply value_interp_related_reify
                   | [ |- expr.interp _ ?v == expr.interp _ (reify ?x) ]
                     => is_var x; is_evar v; eapply value_interp_related_reify
                   | [ H : forall x1 x2, x1 === x2 -> ?f1 x1 === ?f2 x2 |- ?f1 _ === _ ] => eapply H; clear H
                   | [ H : (forall x1 x2, x1 === x2 -> ?f1 x1 === reflect (?f2 @ reify x2)%expr)
                       |- ?f1 _ === reflect (?f2 @ reify _)%expr ]
                     => eapply H; clear H
                   | [ H : forall x y, x == y -> _ == expr.interp _ ?f2 y |- _ == expr.interp _ ?f2 _ ]
                     => etransitivity; [ | eapply H ]; clear H
                   | _ => (idtac + symmetry); eassumption
                   end.

          Lemma value_interp_related_reify_reflect_iff
                {with_lets1 with_lets2 t v1 e2}
                (v2 := reflect e2)
            : @value_interp_ok with_lets1 t v1
              -> expr.interp ident_interp e2 == expr.interp ident_interp e2
              -> (@value'_interp_related with_lets1 with_lets2 t v1 v2
                  <-> expr.interp ident_interp (reify v1) == expr.interp ident_interp e2).
          Proof using Type.
            subst v2; cbv [value_interp_ok] in *.
            revert with_lets1 with_lets2 v1 e2.
            induction t as [|s IHs d IHd]; cbn [value'_interp_related] in *.
            { cbn; intros; break_innermost_match; rewrite ?UnderLets.interp_to_expr; reflexivity. }
            { intros ? ? v1 e2 H1 H2.
              cbn [type.related] in *; cbv [respectful] in *.
              specialize (IHd true true); specialize (IHs false false).
              cbn [reify reflect expr.interp] in *.
              fold (@reify var) (@reflect var) in *.
              cbn [value' expr.interp] in *.
              specialize (fun x1 (x2 : value' false s) pf1 => IHd (v1 x1) (e2 @ reify x2)%expr (H1 _ _ pf1)); cbn [expr.interp] in *.
              specialize (fun x1 x2 pf1 pf2 => IHd x1 x2 pf1 (H2 _ _ (value_interp_related_reify pf2))).
              split; intros H ? ? H'; [ etransitivity; [ eapply IHd | eapply H2 ]; clear IHd | apply IHd; clear IHd ]; cbn [expr.interp] in *.
              all: unshelve (t_value_interp_related; t_value_interp_related); trivial. }
          Qed.

          Lemma value_interp_related_iff_of_ok {t with_lets1 with_lets2 v1 v2}
            : @value_interp_ok with_lets1 t v1
              -> @value_interp_ok with_lets2 t v2
              -> (@value'_interp_related with_lets1 with_lets2 t v1 v2
                  <-> value'_interp v1 == value'_interp v2).
          Proof using Type.
            cbv [value_interp_ok value'_interp] in *.
            intros H1 H2; split; intro H.
            { eapply value_interp_related_reify_reflect_iff;
                [ eassumption | eapply value_interp_related_reify | symmetry; eapply interp_reflect_reify ].
              { etransitivity; (idtac + symmetry); eassumption. }
              { eapply value'_interp_related_sym_iff; eassumption. } }
            { eapply value_interp_related_reify_reflect_iff in H; [ | eassumption | ].
              { eapply value'_interp_related_trans; [ eexact H | eapply interp_reflect_reify ].
                etransitivity; (idtac + symmetry); eassumption. }
              { eapply value_interp_related_reify.
                etransitivity; (idtac + symmetry); eassumption. } }
            Unshelve.
            all: trivial.
          Qed.

          Lemma value'_interp_app {with_lets s d f x}
            : @value_interp_ok with_lets (type.arrow s d) f
              -> @value_interp_ok _ s x
              -> value'_interp (f x) == value'_interp f (value'_interp x).
          Proof using Type.
            cbv [value_interp_ok]; cbn [value'_interp_related value'] in *.
            intros Hf Hx.
            transitivity (value'_interp (with_lets:=false) (t:=type.arrow s d) (fun x => f (reflect (reify x))) (value'_interp x)).
            all: fold (@value' var).
            { cbv [value'_interp]; cbn [reify reflect expr.interp].
              fold (@reify var) (@reflect var).
              eapply value_interp_related_iff_of_ok; apply Hf;
                repeat first [ eassumption
                             | progress cbn [expr.interp]
                             | (idtac + symmetry); apply interp_reflect_reify
                             | eapply value_interp_related_reflect
                             | eapply value_interp_related_reify
                             | etransitivity; [ eapply value_interp_related_reflect; progress cbn [expr.interp] | ] ]. }
            { eapply (@value_interp_related_iff_of_ok (type.arrow s d));
                fold (@type.related); cbv [value_interp_ok]; cbn [value'_interp_related];
                  [ .. | eapply value_interp_related_iff_of_ok ]; try assumption.
              all: intros; apply Hf.
              all: repeat first [ (idtac + symmetry); apply interp_reflect_reify
                                | (idtac + symmetry); assumption ]. }
          Qed.

          Lemma interp_of_wf_reify_expr G {t}
                (HG : forall t v1 v2, List.In (existT _ t (v1, v2)) G -> expr.interp ident_interp (reify v1) == v2)
                e1 e2
                (Hwf : expr.wf G e1 e2)
            : expr.interp ident_interp (@reify_expr _ t e1) == expr.interp ident_interp e2.
          Proof using ident_interp_Proper.
            induction Hwf; cbn [expr.interp reify_expr]; cbv [LetIn.Let_In];
              try solve [ auto
                        | apply ident_interp_Proper; reflexivity ].
            all: cbn [type.related] in *; cbv [respectful]; intros.
            all: match goal with H : _ |- _ => apply H; clear H end.
            all: repeat first [ progress cbn [In eq_rect fst snd] in *
                              | progress intros
                              | progress destruct_head'_or
                              | progress subst
                              | progress inversion_sigma
                              | progress inversion_prod
                              | apply interp_reify_reflect
                              | solve [ auto ] ].
          Qed.

          Fixpoint pattern_default_interp' {K t} (p : pattern t) evm {struct p} : (expr (pattern.type.subst_default t evm) -> K) -> @with_unification_resultT' t p evm K
            := match p in pattern.pattern t return (expr (pattern.type.subst_default t evm) -> K) -> @with_unification_resultT' t p evm K with
               | pattern.Wildcard t => fun k v => k (reify v)
               | pattern.Ident t idc
                 => fun k
                    => lam_type_of_list (fun args => k (expr.Ident (pident_to_typed _ idc _ args)))
               | pattern.App s d f x
                 => fun k
                    => @pattern_default_interp'
                         _ _ f evm
                         (fun ef
                          => @pattern_default_interp'
                               _ _ x evm
                               (fun ex
                                => k (expr.App ef ex)))
               end.

          Definition pattern_default_interp {t} (p : pattern t) : @with_unif_rewrite_ruleTP_gen t p false false false
            := pattern.type.lam_forall_vars
                 (fun evm
                  => pattern_default_interp' p evm id).

          Definition deep_rewrite_ruleTP_gen_good_relation
                     {should_do_again with_opt under_lets : bool} {t}
                     (v1 : @deep_rewrite_ruleTP_gen should_do_again with_opt under_lets t)
                     (v2 : expr t)
            : Prop
            := (let v1 := normalize_deep_rewrite_rule v1 in
                match v1 with
                | None => True
                | Some v1 => let v1 := UnderLets.interp ident_interp v1 in
                             (if should_do_again
                                 return (@expr.expr base.type ident (if should_do_again then @value var else var) t) -> Prop
                              then
                                (fun v1
                                 => expr.interp ident_interp (reify_expr v1) == expr.interp ident_interp v2)
                              else
                                (fun v1 => expr.interp ident_interp v1 == expr.interp ident_interp v2))
                               v1
                end).

          Definition rewrite_rule_data_interp_goodT
                     {t} {p : pattern t} (r : @rewrite_rule_data t p)
            : Prop
            := forall x y,
              related_unification_resultT (fun t v1 v2 => value_interp_ok v1 /\ value_interp_ok v2 /\ value'_interp v1 == value'_interp v2) x y
              -> option_eq
                   (fun fx gy
                    => related_sigT_by_eq
                         (fun evm
                          => @deep_rewrite_ruleTP_gen_good_relation
                               (rew_should_do_again _ _ r) (rew_with_opt _ _ r) (rew_under_lets _ _ r) (pattern.type.subst_default t evm))
                         fx gy)
                   (app_with_unification_resultT_cps _ (rew_replacement _ _ r) x _ (@Some _))
                   (app_with_unification_resultT_cps _ (pattern_default_interp p) y _ (@Some _)).

          Definition rewrite_rules_interp_goodT
                     (rews : rewrite_rulesT)
            : Prop
            := forall p r,
              List.In (existT _ p r) rews
              -> rewrite_rule_data_interp_goodT r.

          Definition rewrite_rule_data_interp_goodT_curried
                     {t} {p : pattern t} (r : @rewrite_rule_data t p)
            : Prop
            := under_with_unification_resultT_relation_hetero
                 (fun _ => value_interp_related)
                 (fun evm => deep_rewrite_ruleTP_gen_good_relation)
                 (rew_replacement _ _ r)
                 (pattern_default_interp p).

          Definition rewrite_rules_interp_goodT_curried
                     (rews : rewrite_rulesT)
            : Prop
            := forall p r,
              List.In (existT _ p r) rews
              -> rewrite_rule_data_interp_goodT_curried r.

          Lemma rewrite_rules_interp_goodT_by_curried rews
            : rewrite_rules_interp_goodT_curried rews -> rewrite_rules_interp_goodT rews.
          Proof using Type.
            cbv [rewrite_rules_interp_goodT rewrite_rules_interp_goodT_curried rewrite_rule_data_interp_goodT rewrite_rule_data_interp_goodT_curried].
            intro H.
            repeat (let x := fresh "x" in intro x; specialize (H x)).
            intros X Y HXY.
            pose proof (related_app_with_unification_resultT _ _ _ _ _ _ ltac:(eassumption) ltac:(eapply map_related_unification_resultT; [ | eassumption ]; intros; cbv beta in *; destruct_head'_and; eapply value_interp_related_iff_of_ok; eassumption)) as H'.
            cps_id'_with_option app_with_unification_resultT_cps_id.
            cbv [deep_rewrite_ruleTP_gen] in *.
            let H1 := fresh in
            let H2 := fresh in
            lazymatch type of H' with
            | option_eq ?R ?x ?y
              => destruct x eqn:H1, y eqn:H2; cbv [option_eq] in H'
            end.
            all: repeat first [ progress cbn [option_eq]
                              | reflexivity
                              | progress inversion_option
                              | exfalso; assumption
                              | assumption ].
          Qed.
        End with_interp.
      End with_var.
    End Compile.
  End RewriteRules.
End Compilers.
