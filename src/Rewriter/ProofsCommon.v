Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.MSets.MSetPositive.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.Program.Tactics.
Require Import Crypto.Language.Language.
Require Import Crypto.Language.Inversion.
Require Import Crypto.Language.Wf.
Require Import Crypto.Language.UnderLetsProofs.
Require Import Crypto.Language.IdentifiersBasicLibrary.
Require Import Crypto.Language.IdentifiersLibrary.
Require Import Crypto.Language.IdentifiersLibraryProofs.
Require Import Crypto.Rewriter.Rewriter.
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
Require Import Crypto.Util.MSetPositive.Facts.
Require Import Crypto.Util.Bool.Reflect.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Sigma.Related.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.ListUtil.Forall.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Logic.ExistsEqAnd.
Require Import Crypto.Util.CPSNotations.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.HProp.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.NatUtil.
Require Crypto.Util.PrimitiveHList.
Import Coq.Lists.List ListNotations. Local Open Scope list_scope.
Local Open Scope Z_scope.

Import EqNotations.
Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import UnderLetsProofs.Compilers.
  Import IdentifiersLibrary.Compilers.
  Import IdentifiersBasicLibrary.Compilers.
  Import IdentifiersLibraryProofs.Compilers.
  Import Rewriter.Compilers.
  Import expr.Notations.

  Module Import RewriteRules.
    Import Rewriter.Compilers.RewriteRules.

    Module pattern.
      Module base.
        Import IdentifiersLibrary.Compilers.pattern.base.
        Section with_base.
          Context {base : Type}.
          Local Notation type := (type base).
          Local Notation pattern_base_subst := (@pattern.base.subst base).

          Lemma subst_relax {t evm}
            : pattern_base_subst (pattern.base.relax t) evm = Some t.
          Proof using Type.
            induction t; cbn; cbv [Option.bind option_map];
              rewrite_hyp ?*; reflexivity.
          Qed.

          Lemma subst_Some_subst_default {pt evm t}
            : pattern_base_subst pt evm = Some t -> pattern.base.subst_default pt evm = t.
          Proof using Type.
            revert t; induction pt;
              repeat first [ progress cbn [pattern.base.subst pattern.base.subst_default]
                           | progress cbv [pattern.base.lookup_default]
                           | progress cbv [Option.bind option_map]
                           | progress inversion_option
                           | progress subst
                           | progress intros
                           | reflexivity
                           | apply (f_equal base.type.list)
                           | apply (f_equal base.type.option)
                           | apply (f_equal2 base.type.prod)
                           | break_innermost_match_step
                           | break_innermost_match_hyps_step
                           | solve [ eauto ] ].
          Qed.

          Lemma subst_relax_evm {pt evm evm' t}
                (Hevm : forall i v, PositiveMap.find i evm = Some v -> PositiveMap.find i evm' = Some v)
            : pattern_base_subst pt evm = Some t -> pattern_base_subst pt evm' = Some t.
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

          Local Ltac t_subst_eq_iff :=
            repeat first [ progress cbn [pattern.base.collect_vars pattern.base.subst]
                         | reflexivity
                         | assumption
                         | congruence
                         | match goal with
                           | [ |- context[PositiveSet.mem _ (PositiveSet.add _ _)] ]
                             => setoid_rewrite PositiveSetFacts.add_b
                           | [ |- context[PositiveSet.mem _ PositiveSet.empty] ]
                             => setoid_rewrite PositiveSetFacts.empty_b
                           | [ |- context[PositiveSet.mem _ (PositiveSet.union _ _)] ]
                             => setoid_rewrite PositiveSetFacts.union_b
                           | [ |- context[orb _ false] ]
                             => setoid_rewrite Bool.orb_false_r
                           | [ |- context[orb _ _ = true] ]
                             => setoid_rewrite Bool.orb_true_iff
                           | _ => progress cbv [PositiveSetFacts.eqb Option.bind option_map]
                           end
                         | progress intros
                         | progress subst
                         | progress specialize_by (exact eq_refl)
                         | progress specialize_by_assumption
                         | progress inversion_option
                         | progress destruct_head'_and
                         | progress destruct_head'_ex
                         | progress specialize_by discriminate
                         | match goal with
                           | [ |- iff _ _ ] => split
                           | [ H : base.type.prod _ _ = base.type.prod _ _ |- _ ] => inversion H; clear H
                           | [ H : base.type.list _ = base.type.list _ |- _ ] => inversion H; clear H
                           | [ H : base.type.option _ = base.type.option _ |- _ ] => inversion H; clear H
                           | [ H : Some _ = _ |- _ ] => symmetry in H
                           | [ H : None = _ |- _ ] => symmetry in H
                           | [ H : ?x = Some _ |- context[?x] ] => rewrite H
                           | [ H : ?x = None |- context[?x] ] => rewrite H
                           | [ |- (?x = None /\ _) \/ _ ]
                             => destruct x eqn:?; [ right | left ]
                           | [ |- Some _ <> _ /\ _ ] => split; [ congruence | ]
                           | [ |- ?x = ?x /\ _ ] => split; [ reflexivity | ]
                           | [ |- exists t', (if PositiveSetFacts.eq_dec ?t t' then true else false) = true /\ _ ]
                             => exists t
                           | [ H : forall t', (if PositiveSetFacts.eq_dec ?t t' then true else false) = true -> _ |- _ ]
                             => specialize (H t)
                           | [ H : (Some _ = None /\ _) \/ _ -> _ |- _ ]
                             => specialize (fun pf => H (or_intror pf))
                           | [ H : _ /\ _ -> _ |- _ ]
                             => specialize (fun pf1 pf2 => H (conj pf1 pf2))
                           end
                         | progress cbv [Option.bind option_map] in *
                         | progress split_contravariant_or
                         | apply conj
                         | progress destruct_head'_or
                         | break_innermost_match_step
                         | break_innermost_match_hyps_step
                         | solve [ eauto ] ].

          Lemma subst_eq_iff {t evm1 evm2}
            : pattern_base_subst t evm1 = pattern_base_subst t evm2
              <-> ((pattern_base_subst t evm1 = None
                    /\ pattern_base_subst t evm2 = None)
                   \/ (forall t', PositiveSet.mem t' (pattern.base.collect_vars t) = true -> PositiveMap.find t' evm1 = PositiveMap.find t' evm2)).
          Proof using Type. split; induction t; t_subst_eq_iff. Qed.

          Lemma subst_eq_if_mem {t evm1 evm2}
            : (forall t', PositiveSet.mem t' (pattern.base.collect_vars t) = true -> PositiveMap.find t' evm1 = PositiveMap.find t' evm2)
              -> pattern_base_subst t evm1 = pattern_base_subst t evm2.
          Proof using Type. rewrite subst_eq_iff; eauto. Qed.

          Lemma subst_eq_Some_if_mem {t evm1 evm2}
            : pattern_base_subst t evm1 <> None
              -> (forall t', PositiveSet.mem t' (pattern.base.collect_vars t) = true -> PositiveMap.find t' evm1 <> None -> PositiveMap.find t' evm1 = PositiveMap.find t' evm2)
              -> pattern_base_subst t evm1 = pattern_base_subst t evm2.
          Proof using Type. induction t; t_subst_eq_iff. Qed.

          Local Instance subst_Proper
            : Proper (eq ==> @PositiveMap.Equal _ ==> eq) pattern_base_subst.
          Proof using Type.
            intros t t' ? ? ? ?; subst t'; cbv [Proper respectful PositiveMap.Equal] in *.
            apply subst_eq_if_mem; auto.
          Qed.

          Local Notation mk_new_evm0 evm ls
            := (fold_right
                  (fun i k evm'
                   => k match PositiveMap.find i evm with
                        | Some v => PositiveMap.add i v evm'
                        | None => evm'
                        end) (fun evm' => evm')
                  (List.rev ls)) (only parsing).

          Local Notation mk_new_evm evm ps
            := (mk_new_evm0
                  evm
                  (PositiveSet.elements ps)) (only parsing).

          Lemma fold_right_evar_map_find_In'' {A} evm ps evm0 k
            : PositiveMap.find k (mk_new_evm evm ps evm0)
              = if in_dec PositiveSet.E.eq_dec k (List.rev (PositiveSet.elements ps))
                then match PositiveMap.find k evm with
                     | Some v => Some v
                     | None => PositiveMap.find k evm0
                     end
                else @PositiveMap.find A k evm0.
          Proof using Type.
            revert evm evm0.
            induction (List.rev (PositiveSet.elements ps)) as [|x xs IHxs]; cbn [fold_right List.In]; intros;
              [ | rewrite IHxs; clear IHxs ].
            all: repeat first [ progress split_iff
                              | progress subst
                              | break_innermost_match_step
                              | solve [ exfalso; eauto
                                      | eauto ]
                              | progress cbn [List.In] in *
                              | progress destruct_head'_or
                              | congruence
                              | rewrite PositiveMapAdditionalFacts.gsspec ].
          Qed.

          Lemma fold_right_evar_map_find_In' {A} evm ps evm0 k
            : PositiveMap.find k (mk_new_evm evm ps evm0)
              = if in_dec PositiveSet.E.eq_dec k (PositiveSet.elements ps)
                then match PositiveMap.find k evm with
                     | Some v => Some v
                     | None => PositiveMap.find k evm0
                     end
                else @PositiveMap.find A k evm0.
          Proof using Type.
            rewrite fold_right_evar_map_find_In''; break_innermost_match; try reflexivity.
            all: rewrite <- in_rev in *; tauto.
          Qed.

          Lemma fold_right_evar_map_find_In {A} evm ps evm0 k
            : PositiveMap.find k (mk_new_evm evm ps evm0)
              = if PositiveSet.mem k ps
                then match PositiveMap.find k evm with
                     | Some v => Some v
                     | None => PositiveMap.find k evm0
                     end
                else @PositiveMap.find A k evm0.
          Proof using Type.
            pose proof (PositiveSet.elements_spec1 ps k) as He.
            rewrite <- PositiveSet.mem_spec in He.
            rewrite InA_alt in He.
            cbv [PositiveSet.E.eq] in *.
            ex_eq_and.
            split_iff.
            rewrite fold_right_evar_map_find_In'; break_match; try reflexivity;
              intuition congruence.
          Qed.

          Lemma fold_right_evar_map_find_elements_Proper {A}
            : Proper (PositiveSet.Equal ==> @PositiveMap.Equal A ==> @PositiveMap.Equal _ ==> @PositiveMap.Equal _) (fun ps evm => mk_new_evm evm ps).
          Proof using Type.
            intros ps ps' Hps evm evm' Hevm evm0 evm0' Hevm0.
            cbv [PositiveMap.Equal] in *.
            apply PositiveSetFacts.elements_Proper_Equal in Hps.
            intro y.
            apply (f_equal (@List.rev _)) in Hps.
            revert dependent evm; revert dependent evm'.
            generalize dependent (List.rev (PositiveSet.elements ps)); intro ls.
            generalize dependent (List.rev (PositiveSet.elements ps')); intro ls'.
            clear ps ps'; intro; subst ls'.
            revert evm0 evm0' Hevm0; induction ls as [|l ls IHls]; cbn [fold_right] in *; intros;
              [ now eauto | apply IHls; clear IHls ].
            all: repeat first [ progress intros
                              | solve [ eauto ]
                              | progress subst
                              | rewrite_hyp !*
                              | congruence
                              | break_innermost_match_step
                              | rewrite PositiveMapAdditionalFacts.gsspec ].
          Qed.

          Lemma eq_subst_types_pattern_collect_vars pt t evm evm0
                (evm' := mk_new_evm evm (pattern.base.collect_vars pt) evm0)
                (Hty : pattern_base_subst pt evm = Some t)
            : pattern_base_subst pt evm' = Some t.
          Proof using Type.
            rewrite <- Hty; symmetry; apply subst_eq_Some_if_mem; subst evm'; intros; try congruence; [].
            rewrite fold_right_evar_map_find_In; rewrite_hyp !*.
            destruct (PositiveMap.find t' evm) eqn:H'; [ reflexivity | ].
            congruence.
          Qed.

          Lemma eq_subst_types_pattern_collect_vars_empty_iff pt evm (evm0:=PositiveMap.empty _)
                (evm' := mk_new_evm evm (pattern.base.collect_vars pt) evm0)
            : pattern_base_subst pt evm = pattern_base_subst pt evm'.
          Proof using Type.
            apply subst_eq_if_mem; subst evm' evm0; intro.
            rewrite fold_right_evar_map_find_In, PositiveMap.gempty.
            intro H; rewrite H.
            break_innermost_match; reflexivity.
          Qed.

          Lemma add_var_types_cps_id {t v evm T k}
            : @pattern.base.add_var_types_cps base t v evm T k = k (@pattern.base.add_var_types_cps base t v evm _ id).
          Proof using Type.
            revert v evm T k.
            induction t; cbn in *; intros; break_innermost_match; try reflexivity;
              auto.
            repeat match goal with H : _ |- _ => (rewrite H; reflexivity) + (etransitivity; rewrite H; clear H; [ | reflexivity ]) end;
              reflexivity.
          Qed.

          Lemma mem_collect_vars_subst_Some_find {x t evm t'}
                (Hmem : PositiveSet.mem x (pattern.base.collect_vars t) = true)
                (H : pattern_base_subst t evm = Some t')
            : PositiveMap.find x evm <> None.
          Proof using Type.
            revert t' H; induction t; intros.
            all: repeat first [ progress cbn [pattern.base.collect_vars pattern.base.subst] in *
                              | progress cbv [PositiveSetFacts.eqb Option.bind option_map] in *
                              | progress subst
                              | progress inversion_option
                              | progress specialize_by_assumption
                              | rewrite PositiveSetFacts.add_b in *
                              | rewrite PositiveSetFacts.empty_b in *
                              | rewrite PositiveSetFacts.union_b in *
                              | rewrite Bool.orb_true_iff in *
                              | congruence
                              | break_innermost_match_hyps_step
                              | progress destruct_head'_or
                              | match goal with
                                | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                                end ].
          Qed.
        End with_base.
        Ltac add_var_types_cps_id :=
          cps_id_with_option (@add_var_types_cps_id _ _ _ _ _ _).
      End base.

      Module type.
        Section with_base.
          Context {base : Type}
                  {base_beq : base -> base -> bool}
                  {reflect_base_beq : reflect_rel (@eq base) base_beq}.

          Local Notation EvarMap := (PositiveMap.t (base.type.type base)).
          Local Notation pattern_type_subst := (@pattern.type.subst base).

          Lemma subst_relax {t evm}
            : pattern_type_subst (pattern.type.relax t) evm = Some t.
          Proof using Type.
            induction t; cbn; cbv [Option.bind option_map];
              rewrite_hyp ?*; rewrite ?base.subst_relax; reflexivity.
          Qed.

          Lemma subst_Some_subst_default {pt evm t}
            : pattern_type_subst pt evm = Some t -> pattern.type.subst_default pt evm = t.
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
            : pattern_type_subst pt evm = Some t -> pattern_type_subst pt evm' = Some t.
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
            : @pattern.type.add_var_types_cps base t v evm T k = k (@pattern.type.add_var_types_cps base t v evm _ id).
          Proof using Type.
            revert v evm T k.
            induction t; cbn in *; intros; break_innermost_match; try reflexivity;
              auto using base.add_var_types_cps_id.
            repeat match goal with H : _ |- _ => (rewrite H; reflexivity) + (etransitivity; rewrite H; clear H; [ | reflexivity ]) end;
              reflexivity.
          Qed.

          Local Ltac t_subst_eq_iff :=
            repeat first [ progress apply conj
                         | progress cbv [option_map Option.bind] in *
                         | progress intros
                         | progress inversion_option
                         | progress subst
                         | progress destruct_head'_and
                         | progress destruct_head'_or
                         | progress destruct_head' iff
                         | match goal with
                           | [ |- context[PositiveSet.mem _ (PositiveSet.union _ _)] ]
                             => setoid_rewrite PositiveSetFacts.union_b
                           | [ |- context[orb _ _ = true] ]
                             => setoid_rewrite Bool.orb_true_iff
                           | [ H : context[PositiveSet.mem _ (PositiveSet.union _ _)] |- _ ]
                             => setoid_rewrite PositiveSetFacts.union_b in H
                           | [ H : context[orb _ _ = true] |- _ ]
                             => setoid_rewrite Bool.orb_true_iff in H
                           | [ H : type.base _ = type.base _ |- _ ] => inversion H; clear H
                           | [ H : type.arrow _ _ = type.arrow _ _ |- _ ] => inversion H; clear H
                           | [ H : ?x = ?x |- _ ] => clear H
                           | [ H : (Some _ = None /\ _) \/ _ -> _ |- _ ]
                             => specialize (fun pf => H (or_intror pf))
                           | [ H : (_ /\ Some _ = None) \/ _ -> _ |- _ ]
                             => specialize (fun pf => H (or_intror pf))
                           | [ |- (Some _ = None /\ _) \/ _ ] => right
                           end
                         | progress specialize_by (exact eq_refl)
                         | progress specialize_by_assumption
                         | progress specialize_by congruence
                         | progress split_contravariant_or
                         | solve [ eauto ]
                         | break_innermost_match_hyps_step
                         | break_innermost_match_step
                         | progress cbn [pattern.type.subst pattern.type.collect_vars] in * ].

          Lemma subst_eq_iff {t evm1 evm2}
            : pattern_type_subst t evm1 = pattern_type_subst t evm2
              <-> ((pattern_type_subst t evm1 = None
                    /\ pattern_type_subst t evm2 = None)
                   \/ (forall t', PositiveSet.mem t' (pattern.type.collect_vars t) = true -> PositiveMap.find t' evm1 = PositiveMap.find t' evm2)).
          Proof using Type.
            induction t as [t|s IHs d IHd]; cbn [pattern.type.collect_vars pattern.type.subst];
              [ pose proof (@pattern.base.subst_eq_iff base t evm1 evm2) | ].
            all: t_subst_eq_iff.
          Qed.

          Lemma subst_eq_if_mem {t evm1 evm2}
            : (forall t', PositiveSet.mem t' (pattern.type.collect_vars t) = true -> PositiveMap.find t' evm1 = PositiveMap.find t' evm2)
              -> pattern_type_subst t evm1 = pattern_type_subst t evm2.
          Proof using Type. rewrite subst_eq_iff; eauto. Qed.

          Lemma subst_eq_Some_if_mem {t evm1 evm2}
            : pattern_type_subst t evm1 <> None
              -> (forall t', PositiveSet.mem t' (pattern.type.collect_vars t) = true -> PositiveMap.find t' evm1 <> None -> PositiveMap.find t' evm1 = PositiveMap.find t' evm2)
              -> pattern_type_subst t evm1 = pattern_type_subst t evm2.
          Proof using Type.
            induction t;
              repeat first [ progress t_subst_eq_iff
                           | match goal with
                             | [ H : pattern.base.subst ?t ?evm1 = Some _, H' : pattern.base.subst ?t ?evm2 = _ |- _ ]
                               => let H'' := fresh in
                                  pose proof (@base.subst_eq_Some_if_mem base t evm1 evm2) as H'';
                                  rewrite H, H' in H''; clear H H'
                             end ].
          Qed.

          Local Instance subst_Proper
            : Proper (eq ==> @PositiveMap.Equal _ ==> eq) pattern_type_subst.
          Proof using Type.
            intros t t' ? ? ? ?; subst t'; cbv [Proper respectful PositiveMap.Equal] in *.
            apply subst_eq_if_mem; auto.
          Qed.

          Local Notation mk_new_evm0 evm ls
            := (fold_right
                  (fun i k evm'
                   => k match PositiveMap.find i evm with
                        | Some v => PositiveMap.add i v evm'
                        | None => evm'
                        end) (fun evm' => evm')
                  (List.rev ls)) (only parsing).

          Local Notation mk_new_evm evm ps
            := (mk_new_evm0
                  evm
                  (PositiveSet.elements ps)) (only parsing).

          Lemma eq_subst_types_pattern_collect_vars pt t evm evm0
                (evm' := mk_new_evm evm (pattern.type.collect_vars pt) evm0)
                (Hty : pattern_type_subst pt evm = Some t)
            : pattern_type_subst pt evm' = Some t.
          Proof using Type.
            rewrite <- Hty; symmetry; apply subst_eq_Some_if_mem; subst evm'; intros; try congruence; [].
            rewrite base.fold_right_evar_map_find_In; rewrite_hyp !*.
            destruct (PositiveMap.find t' evm) eqn:H'; [ reflexivity | ].
            congruence.
          Qed.

          Lemma eq_subst_types_pattern_collect_vars_empty_iff pt evm (evm0:=PositiveMap.empty _)
                (evm' := mk_new_evm evm (pattern.type.collect_vars pt) evm0)
            : pattern_type_subst pt evm = pattern_type_subst pt evm'.
          Proof using Type.
            apply subst_eq_if_mem; subst evm' evm0; intro.
            rewrite base.fold_right_evar_map_find_In, PositiveMap.gempty.
            intro H; rewrite H.
            break_innermost_match; reflexivity.
          Qed.

          Lemma app_forall_vars_under_forall_vars_relation
                {p k1 k2 F v1 v2 evm}
            : @pattern.type.under_forall_vars_relation base p k1 k2 F v1 v2
              -> option_eq
                   (F _)
                   (@pattern.type.app_forall_vars base p k1 v1 evm)
                   (@pattern.type.app_forall_vars base p k2 v2 evm).
          Proof using Type.
            revert k1 k2 F v1 v2 evm.
            cbv [pattern.type.under_forall_vars_relation pattern.type.app_forall_vars pattern.type.forall_vars].
            generalize (PositiveMap.empty (base.type base)).
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
            : @pattern.type.under_forall_vars_relation1 base p k1 F f
              <-> (forall evm fv, pattern.type.app_forall_vars f evm = Some fv -> F _ fv).
          Proof using reflect_base_beq.
            revert k1 F f.
            cbv [pattern.type.under_forall_vars_relation1 pattern.type.app_forall_vars pattern.type.forall_vars].
            generalize (PositiveMap.empty (base.type base)).
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
                clear -H_NoDup reflect_base_beq.
                match goal with
                | [ |- context[pattern.type.app_forall_vars_gen _ _ _ (?f ?t)] ]
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
                induction xs as [|x' xs IHxs]; cbn [pattern.type.app_forall_vars_gen fold_right] in *.
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
            : @pattern.type.under_forall_vars_relation1 base p k1 F (@pattern.type.lam_forall_vars base p k1 f)
              <-> forall ls',
                List.length ls' = List.length (List.rev (PositiveSet.elements p))
                -> let evm := fold_left (fun m '(k, v) => PositiveMap.add k v m) (List.combine (List.rev (PositiveSet.elements p)) ls') (PositiveMap.empty _) in
                   F evm (f evm).
          Proof using Type.
            cbv [pattern.type.under_forall_vars_relation1 pattern.type.lam_forall_vars].
            generalize (PositiveMap.empty (base.type base)).
            generalize (rev (PositiveSet.elements p)).
            clear p.
            intros ls m.
            revert k1 F f m.
            induction ls as [|l ls IHls]; cbn [pattern.type.lam_forall_vars_gen list_rect fold_right fold_left List.length] in *; intros.
            { split; intro H; [ intros [|] | specialize (H nil eq_refl) ]; cbn [List.length List.combine fold_right] in *; intros; try discriminate; assumption. }
            { setoid_rewrite IHls; clear IHls.
              split; intro H; [ intros [|l' ls'] Hls'; [ | specialize (H l' ls') ]
                              | intros t ls' Hls'; specialize (H (cons t ls')) ];
              cbn [List.length List.combine fold_left] in *;
              try discriminate; inversion Hls'; eauto. }
          Qed.

          Lemma app_forall_vars_lam_forall_vars {p k f evm v}
            : @pattern.type.app_forall_vars base p k (pattern.type.lam_forall_vars f) evm = Some v
              -> v = f _.
          Proof using Type.
            revert v; cbv [pattern.type.app_forall_vars pattern.type.lam_forall_vars].
            generalize (rev (PositiveSet.elements p)); clear p; intro ls.
            generalize (PositiveMap.empty (base.type base)).
            induction ls as [|x xs IHxs]; cbn [pattern.type.app_forall_vars_gen pattern.type.lam_forall_vars_gen fold_right]; [ congruence | ].
            intros t v H; eapply IHxs; clear IHxs.
            rewrite <- H.
            break_innermost_match; [ | now discriminate ].
            reflexivity.
          Qed.

          Lemma mem_collect_vars_subst_Some_find {x t evm t'}
                (Hmem : PositiveSet.mem x (pattern.type.collect_vars t) = true)
                (H : pattern_type_subst t evm = Some t')
            : PositiveMap.find x evm <> None.
          Proof using Type.
            (* Coq's dependency tracking is broken and erroneously claims that [base.mem_collect_vars_subst_Some_find] depends on [type_base] if we wait too long to use it *)
            pose proof (@base.mem_collect_vars_subst_Some_find).
            revert t' H; induction t as [|s IHs d IHd]; intros.
            all: repeat first [ progress cbn [pattern.type.collect_vars pattern.type.subst] in *
                              | progress cbv [option_map Option.bind] in *
                              | rewrite PositiveSetFacts.union_b in *
                              | rewrite Bool.orb_true_iff in *
                              | progress specialize_by_assumption
                              | progress inversion_option
                              | progress subst
                              | break_innermost_match_hyps_step
                              | progress destruct_head'_or
                              | eassumption
                              | reflexivity
                              | solve [ eauto ]
                              | match goal with
                                | [ H : forall x, Some _ = Some x -> _ |- _ ] => specialize (H _ eq_refl)
                                end ].
          Qed.
        End with_base.
        Ltac add_var_types_cps_id :=
            cps_id_with_option (@add_var_types_cps_id _ _ _ _ _ _).
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
          Proof using Type.
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
          Proof using Type.
            destruct t; cbn; intros; subst; hnf; try constructor; try assumption.
            eapply wf_value'_Proper_list; [ | solve [ eauto ] ]; trivial.
          Qed.

          Lemma wf_splice_under_lets_with_value {T1 T2 t}
                G
                (x1 : @UnderLets var1 T1) (x2 : @UnderLets var2 T2)
                (e1 : T1 -> value_with_lets1 t) (e2 : T2 -> value_with_lets2 t)
                (Hx : UnderLets.wf (fun G' a1 a2 => wf_value_with_lets G' (e1 a1) (e2 a2)) G x1 x2)
            : wf_value_with_lets G (splice_under_lets_with_value x1 e1) (splice_under_lets_with_value x2 e2).
          Proof using Type.
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
          Proof using Type.
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
        Context {base : Type}.
        Local Notation base_type := (base.type base).
        Local Notation type := (type.type base_type).
        Local Notation pbase_type := (pattern.base.type base).
        Local Notation ptype := (type.type pbase_type).
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
                (pident_to_typed
                 : forall t (idc : pident t) (evm : EvarMap),
                    type_of_list (pident_arg_types t idc) -> ident (pattern.type.subst_default t evm))
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

        Local Notation expr := (@expr.expr base_type ident).
        Local Notation pattern := (@pattern.pattern base pident).
        Local Notation rawpattern := (@pattern.Raw.pattern raw_pident).
        Local Notation anypattern := (@pattern.anypattern base pident).
        Local Notation UnderLets := (@UnderLets.UnderLets base_type ident).
        Local Notation value' := (@value' base_type ident).
        Local Notation value := (@value base_type ident).
        Local Notation value_with_lets := (@value_with_lets base_type ident).
        Local Notation Base_value := (@Base_value base_type ident).
        Local Notation splice_under_lets_with_value := (@splice_under_lets_with_value base_type ident).
        Local Notation splice_value_with_lets := (@splice_value_with_lets base_type ident).
        Local Notation to_raw_pattern := (@pattern.to_raw base pident raw_pident (@strip_types)).
        Local Notation reify := (@reify base ident).
        Local Notation reflect := (@reflect base ident).
        Local Notation reify_expr := (@reify_expr base ident).
        Local Notation rawexpr := (@rawexpr base ident).
        Local Notation eval_decision_tree var := (@eval_decision_tree base ident var raw_pident full_types invert_bind_args invert_bind_args_unknown type_of_raw_pident raw_pident_to_typed raw_pident_is_simple).
        Local Notation reveal_rawexpr_gen assume_known e := (@reveal_rawexpr_cps_gen base ident _ assume_known e _ id).
        Local Notation reveal_rawexpr e := (@reveal_rawexpr_cps base ident _ e _ id).
        Local Notation unify_pattern' var := (@unify_pattern' base try_make_transport_base_cps ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation unify_pattern var := (@unify_pattern base try_make_transport_base_cps base_beq ident var pident pident_arg_types pident_unify pident_unify_unknown).
        Local Notation app_transport_with_unification_resultT'_cps := (@app_transport_with_unification_resultT'_cps base try_make_transport_base_cps pident pident_arg_types).
        Local Notation app_with_unification_resultT_cps := (@app_with_unification_resultT_cps base try_make_transport_base_cps pident pident_arg_types).
        Local Notation with_unification_resultT' := (@with_unification_resultT' base pident pident_arg_types).
        Local Notation with_unification_resultT := (@with_unification_resultT base pident pident_arg_types).
        Local Notation unification_resultT' := (@unification_resultT' base pident pident_arg_types).
        Local Notation unification_resultT := (@unification_resultT base pident pident_arg_types).

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
          Local Notation expr := (@expr.expr base_type ident var).
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
               | rExpr t e
               | rValue (type.base t) e
                 => e === e1
               | rValue t e => False
               end.

          Fixpoint rawexpr_equiv (r1 r2 : rawexpr) : Prop
            := match r1, r2 with
               | rExpr t e, r
               | r, rExpr t e
               | rValue (type.base t) e, r
               | r, rValue (type.base t) e
                 => rawexpr_equiv_expr e r
               | rValue t1 e1, rValue t2 e2
                 => existT _ t1 e1 = existT _ t2 e2
               | rIdent _ t1 idc1 t'1 alt1, rIdent _ t2 idc2 t'2 alt2
                 => alt1 === alt2
                    /\ (existT ident _ idc1 = existT ident _ idc2)
               | rApp f1 x1 t1 alt1, rApp f2 x2 t2 alt2
                 => alt1 === alt2
                    /\ rawexpr_equiv f1 f2
                    /\ rawexpr_equiv x1 x2
               | rValue _ _, _
               | rIdent _ _ _ _ _, _
               | rApp _ _ _ _, _
                 => False
               end.

          Fixpoint rawexpr_types_ok (r : @rawexpr var) (t : type) : Prop
            := match r with
               | rExpr t' _
               | rValue t' _
                 => t' = t
               | rIdent _ t1 _ t2 _
                 => t1 = t /\ t2 = t
               | rApp f x t' alt
                 => t' = t
                    /\ match alt with
                       | expr.App s d _ _
                         => rawexpr_types_ok f (type.arrow s d)
                            /\ rawexpr_types_ok x s
                       | _ => False
                       end
               end.

          Lemma eq_type_of_rawexpr_of_rawexpr_types_ok {re t}
            : rawexpr_types_ok re t
              -> t = type_of_rawexpr re.
          Proof using Type.
            destruct re; cbn; break_innermost_match; intuition.
          Qed.

          Lemma rawexpr_types_ok_for_type_of_rawexpr {re t}
            : rawexpr_types_ok re t
              -> rawexpr_types_ok re (type_of_rawexpr re).
          Proof using Type.
            intro H; pose proof H; apply eq_type_of_rawexpr_of_rawexpr_types_ok in H; subst; assumption.
          Qed.

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

          Lemma rawexpr_types_ok_of_rawexpr_equiv_expr {t e re}
            : @rawexpr_equiv_expr t e re
              -> rawexpr_types_ok re t.
          Proof using Type.
            revert t e; induction re.
            all: repeat first [ progress cbn [rawexpr_equiv_expr rawexpr_types_ok eq_rect] in *
                              | progress intros
                              | progress destruct_head'_and
                              | progress inversion_sigma
                              | progress subst
                              | apply conj
                              | reflexivity
                              | exfalso; assumption
                              | break_innermost_match_step
                              | break_innermost_match_hyps_step
                              | solve [ eauto ] ].
          Qed.

          Lemma rawexpr_types_ok_iff_of_rawexpr_equiv {re1 re2 t}
            : rawexpr_equiv re1 re2
              -> rawexpr_types_ok re1 t <-> rawexpr_types_ok re2 t.
          Proof using Type.
            revert re2 t; induction re1, re2.
            all: repeat first [ progress cbn [rawexpr_equiv rawexpr_types_ok eq_rect] in *
                              | progress intros
                              | progress destruct_head'_and
                              | progress inversion_sigma
                              | progress subst
                              | apply conj
                              | reflexivity
                              | exfalso; assumption
                              | match goal with
                                | [ H : rawexpr_equiv_expr _ _ |- _ ] => apply rawexpr_types_ok_of_rawexpr_equiv_expr in H
                                end
                              | break_innermost_match_step
                              | break_innermost_match_hyps_step
                              | progress split_iff
                              | solve [ eauto ] ].
          Qed.

          Lemma rawexpr_types_ok_of_reveal_rawexpr {re t}
            : rawexpr_types_ok (reveal_rawexpr re) t <-> rawexpr_types_ok re t.
          Proof using Type.
            cbv [reveal_rawexpr]; revert t; induction re.
            all: repeat first [ progress intros
                              | progress cbn [reveal_rawexpr_cps_gen rawexpr_types_ok value'] in *
                              | progress cbv [id value] in *
                              | progress destruct_head'_and
                              | progress subst
                              | reflexivity
                              | break_innermost_match_step
                              | apply conj
                              | expr.invert_match_step ].
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

          Lemma eq_type_of_rawexpr_equiv_expr
                {t e re}
            : @rawexpr_equiv_expr t e re -> t = type_of_rawexpr re.
          Proof using Type.
            destruct re; cbn [rawexpr_equiv_expr];
              intros; break_innermost_match_hyps; destruct_head'_and; inversion_sigma;
                repeat (subst || cbn [eq_rect type_of_rawexpr] in * );
                solve [ reflexivity | exfalso; assumption ].
          Qed.

          Lemma eq_type_of_rawexpr_equiv
                {r1 r2}
            : rawexpr_equiv r1 r2 -> type_of_rawexpr r1 = type_of_rawexpr r2.
          Proof using Type.
            revert r2; induction r1, r2.
            all: repeat first [ progress cbn [rawexpr_equiv type_of_rawexpr] in *
                              | progress subst
                              | progress destruct_head'_and
                              | progress inversion_sigma
                              | reflexivity
                              | exfalso; assumption
                              | progress intros
                              | break_innermost_match_hyps_step
                              | match goal with
                                | [ H : rawexpr_equiv_expr _ _ |- _ ] => apply eq_type_of_rawexpr_equiv_expr in H
                                end
                              | progress type.inversion_type ].
          Qed.

          Lemma eq_expr_of_rawexpr_equiv_expr' {t e re}
                (H : @rawexpr_equiv_expr t e re)
            : forall pf, expr_of_rawexpr re = rew [expr] pf in e.
          Proof using reflect_base_beq.
            revert t e H; induction re.
            all: repeat first [ progress cbn [expr_of_rawexpr rawexpr_equiv_expr type_of_rawexpr eq_rect] in *
                              | progress subst
                              | progress destruct_head'_and
                              | progress destruct_head'_False
                              | progress inversion_sigma
                              | progress eliminate_hprop_eq
                              | reflexivity
                              | progress intros
                              | break_innermost_match_hyps_step ].
          Qed.

          Lemma eq_expr_of_rawexpr_equiv_expr {t e re}
                (H : @rawexpr_equiv_expr t e re)
            : expr_of_rawexpr re = rew [expr] eq_type_of_rawexpr_equiv_expr H in e.
          Proof using reflect_base_beq. apply eq_expr_of_rawexpr_equiv_expr'; assumption. Qed.

          Lemma eq_expr_of_rawexpr_equiv' {t r1 r2}
                (H : rawexpr_equiv r1 r2)
            : forall pf1 pf2 : _ = t,
              rew [expr] pf1 in expr_of_rawexpr r1 = rew [expr] pf2 in expr_of_rawexpr r2.
          Proof using reflect_base_beq.
            revert r2 t H; induction r1, r2.
            all: repeat first [ progress cbn [expr_of_rawexpr rawexpr_equiv type_of_rawexpr eq_rect] in *
                              | progress subst
                              | progress destruct_head'_and
                              | progress destruct_head'_False
                              | progress inversion_sigma
                              | progress eliminate_hprop_eq
                              | reflexivity
                              | progress intros
                              | break_innermost_match_hyps_step
                              | match goal with
                                | [ H : rawexpr_equiv_expr _ _ |- _ ]
                                  => generalize (eq_type_of_rawexpr_equiv_expr H) (eq_expr_of_rawexpr_equiv_expr H); clear H
                                end ].
          Qed.

          Lemma eq_expr_of_rawexpr_equiv {r1 r2}
                (H : rawexpr_equiv r1 r2)
            : rew [expr] eq_type_of_rawexpr_equiv H in expr_of_rawexpr r1 = expr_of_rawexpr r2.
          Proof using reflect_base_beq. apply eq_expr_of_rawexpr_equiv' with (pf2:=eq_refl); assumption. Qed.

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
          Proof using Type.
            cbv [swap_list]; break_innermost_match; intros; inversion_option; subst;
              rewrite ?nth_set_nth; distr_length; break_innermost_match; try congruence; try lia;
                handle_nth_error.
          Qed.

          Lemma unify_types_cps_id {t e p T k}
            : @unify_types base base_beq ident var pident t e p T k = k (@unify_types base base_beq ident var pident t e p _ id).
          Proof using Type.
            cbv [unify_types]; break_innermost_match; try reflexivity.
            etransitivity; rewrite pattern.type.add_var_types_cps_id; [ reflexivity | ]; break_innermost_match; reflexivity.
          Qed.

          Lemma unify_pattern'_cps_id {t e p evm T cont}
            : @unify_pattern' var t e p evm T cont
              = (v' <- @unify_pattern' var t e p evm _ (@Some _); cont v')%option.
          Proof using try_make_transport_base_cps_correct.
            clear -try_make_transport_base_cps_correct.
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
          Proof using try_make_transport_base_cps_correct.
            clear -try_make_transport_base_cps_correct.
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
          Proof using try_make_transport_base_cps_correct.
            revert K f v T cont; induction p; cbn [app_transport_with_unification_resultT'_cps]; intros.
            all: repeat first [ progress rewrite_type_transport_correct
                              | progress type_beq_to_eq
                              | progress cbn [Option.bind with_unification_resultT' unification_resultT'] in *
                              | progress subst
                              | reflexivity
                              | progress fold (@with_unification_resultT' var)
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
          Proof using try_make_transport_base_cps_correct.
            cbv [app_with_unification_resultT_cps].
            repeat first [ progress cbv [Option.bind] in *
                         | reflexivity
                         | progress subst
                         | progress inversion_option
                         | progress break_match
                         | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id ].
          Qed.

          Local Notation mk_new_evm0 evm ls
            := (fold_right
                  (fun i k evm'
                   => k match PositiveMap.find i evm with
                        | Some v => PositiveMap.add i v evm'
                        | None => evm'
                        end) (fun evm' => evm')
                  (List.rev ls)) (only parsing).

          Local Notation mk_new_evm evm ps
            := (mk_new_evm0
                  evm
                  (PositiveSet.elements ps)) (only parsing).


          Lemma projT1_app_with_unification_resultT {t p K f v res}
            : @app_with_unification_resultT_cps var t p K f v _ (@Some _) = Some res
              -> projT1 res = mk_new_evm (projT1 v) (pattern.collect_vars p) (PositiveMap.empty _).
          Proof using try_make_transport_base_cps_correct.
            cbv [app_with_unification_resultT_cps].
            repeat first [ progress inversion_option
                         | progress subst
                         | progress cbn [projT1] in *
                         | progress intros
                         | reflexivity
                         | progress cbv [Option.bind] in *
                         | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                         | break_match_hyps_step ltac:(fun _ => idtac) ].
          Qed.

          Lemma reveal_rawexpr_cps_gen_id assume_known e T k
            : @reveal_rawexpr_cps_gen base ident var assume_known e T k = k (reveal_rawexpr_gen assume_known e).
          Proof using Type.
            cbv [reveal_rawexpr_cps_gen]; break_innermost_match; try reflexivity.
            all: cbv [value value'] in *; expr.invert_match; try reflexivity.
          Qed.

          Lemma reveal_rawexpr_cps_id e T k
            : @reveal_rawexpr_cps base ident var e T k = k (reveal_rawexpr e).
          Proof using Type. apply reveal_rawexpr_cps_gen_id. Qed.

          Lemma reveal_rawexpr_equiv e
            : rawexpr_equiv (reveal_rawexpr e) e.
          Proof using Type.
            cbv [reveal_rawexpr_cps]; induction e.
            all: repeat first [ progress cbn [rawexpr_equiv reveal_rawexpr_cps_gen value'] in *
                              | progress cbv [id value] in *
                              | break_innermost_match_step
                              | progress expr.invert_match
                              | reflexivity
                              | apply conj ].
          Qed.

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
          Proof using Type.
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

          Context (reify_and_let_binds_base_cps1 : forall (t : base_type), @expr var1 (type.base t) -> forall T, (@expr var1 (type.base t) -> @UnderLets var1 T) -> @UnderLets var1 T)
                  (reify_and_let_binds_base_cps2 : forall (t : base_type), @expr var2 (type.base t) -> forall T, (@expr var2 (type.base t) -> @UnderLets var2 T) -> @UnderLets var2 T)
                  (wf_reify_and_let_binds_base_cps
                   : forall G (t : base_type) x1 x2 T1 T2 P
                            (Hx : expr.wf G x1 x2)
                            (e1 : expr (type.base t) -> @UnderLets var1 T1) (e2 : expr (type.base t) -> @UnderLets var2 T2)
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
          Local Notation deep_rewrite_ruleTP_gen1 := (@deep_rewrite_ruleTP_gen base ident var1).
          Local Notation deep_rewrite_ruleTP_gen2 := (@deep_rewrite_ruleTP_gen base ident var2).
          Local Notation preunify_types1 := (@preunify_types base base_beq ident var1 pident).
          Local Notation preunify_types2 := (@preunify_types base base_beq ident var2 pident).
          Local Notation unify_types1 := (@unify_types base base_beq ident var1 pident).
          Local Notation unify_types2 := (@unify_types base base_beq ident var2 pident).

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
          Proof using wf_reify_and_let_binds_base_cps.
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
          Proof using Type.
            revert dependent G2; induction Hwf; intros; constructor; eauto.
            { eapply expr.wf_Proper_list; eauto. }
            { eapply wf_value'_Proper_list; eauto. }
          Qed.

          (* Because [proj1] and [proj2] in the stdlib are opaque *)
          Local Notation proj1 x := (let (a, b) := x in a).
          Local Notation proj2 x := (let (a, b) := x in b).

          Definition eq_type_of_rawexpr_of_wf {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : type_of_rawexpr re1 = t /\ type_of_rawexpr re2 = t.
          Proof using Type. split; destruct Hwf; reflexivity. Defined.

          Definition eq_expr_of_rawexpr_of_wf {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : (rew [expr] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re1) = e1
              /\ (rew [expr] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re2) = e2.
          Proof using Type. split; destruct Hwf; reflexivity. Defined.

          Definition eq_expr_of_rawexpr_of_wf' {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr_of_rawexpr re1 = (rew [expr] (eq_sym (proj1 (eq_type_of_rawexpr_of_wf Hwf))) in e1)
              /\ expr_of_rawexpr re2 = (rew [expr] (eq_sym (proj2 (eq_type_of_rawexpr_of_wf Hwf))) in e2).
          Proof using Type. split; destruct Hwf; reflexivity. Defined.

          Lemma wf_expr_of_wf_rawexpr {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr.wf G e1 e2.
          Proof using Type. induction Hwf; repeat (assumption || constructor || apply wf_reify). Qed.

          Lemma wf_expr_of_wf_rawexpr' {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : expr.wf G
                      (rew [expr] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re1)
                      (rew [expr] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in expr_of_rawexpr re2).
          Proof using Type.
            pose proof Hwf as Hwf'.
            rewrite <- (proj1 (eq_expr_of_rawexpr_of_wf Hwf)) in Hwf'.
            rewrite <- (proj2 (eq_expr_of_rawexpr_of_wf Hwf)) in Hwf'.
            eapply wf_expr_of_wf_rawexpr; eassumption.
          Qed.

          Lemma wf_value_of_wf_rawexpr {t G re1 e1 re2 e2} (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : wf_value G
                       (rew [value] (proj1 (eq_type_of_rawexpr_of_wf Hwf)) in value_of_rawexpr re1)
                       (rew [value] (proj2 (eq_type_of_rawexpr_of_wf Hwf)) in value_of_rawexpr re2).
          Proof using Type.
            pose proof (wf_expr_of_wf_rawexpr Hwf).
            destruct Hwf; cbn; try eapply wf_reflect; try assumption.
          Qed.

          Lemma wf_value_of_wf_rawexpr_gen {t t' G re1 e1 re2 e2}
                {pf1 pf2 : _ = t'}
                (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : wf_value G
                       (rew [value] pf1 in value_of_rawexpr re1)
                       (rew [value] pf2 in value_of_rawexpr re2).
          Proof using reflect_base_beq.
            assert (H : t = t');
              [
              | destruct H;
                replace pf1 with (proj1 (eq_type_of_rawexpr_of_wf Hwf));
                [ replace pf2 with (proj2 (eq_type_of_rawexpr_of_wf Hwf)) | ] ];
              [ | apply wf_value_of_wf_rawexpr | | ];
              destruct (eq_type_of_rawexpr_of_wf Hwf); generalize dependent (type_of_rawexpr re1); generalize dependent (type_of_rawexpr re2); intros; subst; clear -reflect_base_beq; eliminate_hprop_eq; reflexivity.
          Qed.

          Lemma wf_reveal_rawexpr t G re1 e1 re2 e2 (Hwf : @wf_rawexpr G t re1 e1 re2 e2)
            : @wf_rawexpr G t (reveal_rawexpr re1) e1 (reveal_rawexpr re2) e2.
          Proof using Type.
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

          Fixpoint related_unification_resultT' {var1 var2} (R : forall t, var1 t -> var2 t -> Prop) {t p evm}
            : @unification_resultT' var1 t p evm -> @unification_resultT' var2 t p evm -> Prop
            := match p in pattern.pattern t return @unification_resultT' var1 t p evm -> @unification_resultT' var2 t p evm -> Prop with
               | pattern.Wildcard t => R _
               | pattern.Ident t idc => eq
               | pattern.App s d f x
                 => fun (v1 : unification_resultT' f evm * unification_resultT' x evm)
                        (v2 : unification_resultT' f evm * unification_resultT' x evm)
                    => @related_unification_resultT' _ _ R _ _ _ (fst v1) (fst v2)
                       /\ @related_unification_resultT' _ _ R _ _ _ (snd v1) (snd v2)
               end.

          Definition wf_unification_resultT' (G : list {t1 : type & (var1 t1 * var2 t1)%type}) {t p evm}
            : @unification_resultT' value t p evm -> @unification_resultT' value t p evm -> Prop
            := @related_unification_resultT' _ _ (fun _ => wf_value G) t p evm.

          Definition related_unification_resultT {var1 var2} (R : forall t, var1 t -> var2 t -> Prop) {t p}
            : @unification_resultT _ t p -> @unification_resultT _ t p -> Prop
            := related_sigT_by_eq (@related_unification_resultT' _ _ R t p).

          Definition wf_unification_resultT (G : list {t1 : type & (var1 t1 * var2 t1)%type}) {t p}
            : @unification_resultT (@value var1) t p -> @unification_resultT (@value var2) t p -> Prop
            := @related_unification_resultT _ _ (fun _ => wf_value G) t p.

          Fixpoint under_with_unification_resultT'_relation_hetero {var1 var2 t p evm K1 K2}
                   (FH : forall t, var1 t -> var2 t -> Prop)
                   (F : K1 -> K2 -> Prop)
                   {struct p}
            : @with_unification_resultT' var1 t p evm K1 -> @with_unification_resultT' var2 t p evm K2 -> Prop
            := match p in pattern.pattern t return @with_unification_resultT' var1 t p evm K1 -> @with_unification_resultT' var2 t p evm K2 -> Prop with
               | pattern.Wildcard t => fun f1 f2 => forall v1 v2, FH _ v1 v2 -> F (f1 v1) (f2 v2)
               | pattern.Ident t idc => under_type_of_list_relation_cps F
               | pattern.App s d f x
                 => @under_with_unification_resultT'_relation_hetero
                      _ _ _ f evm _ _
                      FH
                      (@under_with_unification_resultT'_relation_hetero _ _ _ x evm _ _ FH F)
               end.

          Definition under_with_unification_resultT_relation_hetero {var1 var2 t p K1 K2}
                     (FH : forall t, var1 t -> var2 t -> Prop)
                     (F : forall evm, K1 (pattern.type.subst_default t evm) -> K2 (pattern.type.subst_default t evm) -> Prop)
            : @with_unification_resultT var1 t p K1 -> @with_unification_resultT var2 t p K2 -> Prop
            := pattern.type.under_forall_vars_relation
                 (fun evm => under_with_unification_resultT'_relation_hetero FH (F evm)).

          Definition wf_with_unification_resultT
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t} {p : pattern t} {K1 K2 : type -> Type}
                     (P : forall evm, K1 (pattern.type.subst_default t evm) -> K2 (pattern.type.subst_default t evm) -> Prop)
            : @with_unification_resultT value t p K1 -> @with_unification_resultT value t p K2 -> Prop
            := under_with_unification_resultT_relation_hetero
                 (fun t => wf_value G)
                 P.

          Lemma related_app_with_unification_resultT' {var1' var2' t p evm K1 K2}
                R1 R2
                f1 f2 v1 v2
            : @under_with_unification_resultT'_relation_hetero
                var1' var2' t p evm K1 K2 R1 R2 f1 f2
              -> @related_unification_resultT' var1' var2' R1 t p evm v1 v2
              -> R2 (@app_with_unification_resultT' _ _ _ _ t p evm K1 f1 v1)
                    (@app_with_unification_resultT' _ _ _ _ t p evm K2 f2 v2).
          Proof using Type.
            revert K1 K2 R1 R2 f1 f2 v1 v2; induction p; cbn in *; intros; subst; destruct_head'_and;
              try apply related_app_type_of_list_of_under_type_of_list_relation_cps;
              auto.
            repeat match goal with H : _ |- _ => eapply H; eauto; clear H end.
          Qed.

          Lemma related_app_transport_with_unification_resultT' {var1' var2' t p evm1 evm2 K1 K2}
                R1 R2
                f1 f2 v1 v2
            : @under_with_unification_resultT'_relation_hetero
                var1' var2' t p evm1 K1 K2 R1 R2 f1 f2
              -> @related_unification_resultT' var1' var2' R1 t p evm2 v1 v2
              -> option_eq
                   R2
                   (@app_transport_with_unification_resultT'_cps _ t p evm1 evm2 K1 f1 v1 _ (@Some _))
                   (@app_transport_with_unification_resultT'_cps _ t p evm1 evm2 K2 f2 v2 _ (@Some _)).
          Proof using try_make_transport_base_cps_correct.
            revert K1 K2 R1 R2 f1 f2 v1 v2; induction p; cbn in *; intros; subst; destruct_head'_and;
              try apply related_app_type_of_list_of_under_type_of_list_relation_cps;
              auto.
            all: repeat first [ progress rewrite_type_transport_correct
                              | progress type_beq_to_eq
                              | break_innermost_match_step
                              | reflexivity
                              | progress cbn [Option.bind option_eq] in *
                              | progress fold (@with_unification_resultT')
                              | progress cps_id'_with_option app_transport_with_unification_resultT'_cps_id
                              | progress cbv [eq_rect]
                              | solve [ auto ]
                              | exfalso; assumption
                              | progress inversion_option
                              | match goal with
                                | [ H : (forall K1 K2 R1 R2 (f1 : with_unification_resultT' ?p1 ?evm1 K1), _)
                                    |- context[@app_transport_with_unification_resultT'_cps _ ?t ?p1 ?evm1 ?evm2 ?K1' ?f1' ?v1' _ _] ]
                                  => specialize (H K1' _ _ _ f1' _ v1' _ ltac:(eassumption) ltac:(eassumption))
                                | [ H : option_eq ?R ?x ?y |- _ ]
                                  => destruct x eqn:?, y eqn:?; cbv [option_eq] in H
                                end ].
          Qed.

          Lemma related_app_with_unification_resultT {var1' var2' t p K1 K2}
                R1 R2
                f1 f2 v1 v2
            : @under_with_unification_resultT_relation_hetero
                var1' var2' t p K1 K2 R1 R2 f1 f2
              -> @related_unification_resultT var1' var2' R1 t p v1 v2
              -> option_eq
                   (related_sigT_by_eq R2)
                   (@app_with_unification_resultT_cps _ t p K1 f1 v1 _ (@Some _))
                   (@app_with_unification_resultT_cps _ t p K2 f2 v2 _ (@Some _)).
          Proof using try_make_transport_base_cps_correct.
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
          Proof using try_make_transport_base_cps_correct. apply related_app_with_unification_resultT. Qed.

          Definition map_related_unification_resultT' {var1' var2'} {R1 R2 : forall t : type, var1' t -> var2' t -> Prop}
                     (HR : forall t v1 v2, R1 t v1 v2 -> R2 t v1 v2)
                     {t p evm v1 v2}
            : @related_unification_resultT' var1' var2' R1 t p evm v1 v2
              -> @related_unification_resultT' var1' var2' R2 t p evm v1 v2.
          Proof using Type.
            induction p; cbn [related_unification_resultT']; intuition auto.
          Qed.

          Definition map_related_unification_resultT {var1' var2'} {R1 R2 : forall t : type, var1' t -> var2' t -> Prop}
                     (HR : forall t v1 v2, R1 t v1 v2 -> R2 t v1 v2)
                     {t p v1 v2}
            : @related_unification_resultT var1' var2' R1 t p v1 v2
              -> @related_unification_resultT var1' var2' R2 t p v1 v2.
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
                        (app_with_unification_resultT_cps f x _ (@Some _))
                        (app_with_unification_resultT_cps g y _ (@Some _)).

          Definition wf_rewrite_rule_data
                     (G : list {t : _ & (var1 t * var2 t)%type})
                     {t} {p : pattern t}
                     (r1 : @rewrite_rule_data1 t p)
                     (r2 : @rewrite_rule_data2 t p)
            : Prop
            := wf_with_unif_rewrite_ruleTP_gen G (rew_replacement r1) (rew_replacement r2).

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
            := wf_with_unif_rewrite_ruleTP_gen_curried G (rew_replacement r1) (rew_replacement r2).

          Fixpoint rewrite_rules_goodT_curried_cps_folded
                   (rew1 : rewrite_rulesT1) (rew2 : rewrite_rulesT2)
                   (H : List.map (@projT1 _ _) rew1 = List.map (@projT1 _ _) rew2)
                   (final : Prop)
            : Prop
            := match rew1, rew2 return List.map _ rew1 = List.map _ rew2 -> Prop with
               | nil, nil => fun _ => final
               | nil, _ | _, nil => fun _ => False -> final
               | rew1 :: rew1s, rew2 :: rew2s
                 => fun pf : projT1 rew1 :: List.map _ rew1s = projT1 rew2 :: List.map _ rew2s
                    => let pfs := f_equal (@tl _) pf in
                       let pf := f_equal (hd (projT1 rew1)) pf in
                       (forall G,
                           wf_rewrite_rule_data_curried
                             G
                             (rew [fun tp => @rewrite_rule_data1 _ (pattern.pattern_of_anypattern tp)] pf in projT2 rew1)
                             (projT2 rew2))
                       -> rewrite_rules_goodT_curried_cps_folded rew1s rew2s pfs final
               end H.

          Definition rewrite_rules_goodT_curried_cps
            := Eval cbv [id
                           rewrite_rules_goodT_curried_cps_folded
                           eq_rect f_equal hd tl List.map
                           wf_deep_rewrite_ruleTP_gen wf_rewrite_rule_data_curried rew_replacement rew_should_do_again rew_with_opt rew_under_lets wf_with_unif_rewrite_ruleTP_gen_curried wf_with_unification_resultT pattern.pattern_of_anypattern pattern.type_of_anypattern wf_maybe_under_lets_expr wf_maybe_do_again_expr wf_with_unification_resultT pattern.type.under_forall_vars_relation with_unification_resultT' pattern.collect_vars pattern.type.collect_vars pattern.base.collect_vars PositiveSet.empty PositiveSet.elements under_type_of_list_relation_cps pattern.ident.arg_types pattern.type.subst_default pattern.base.subst_default pattern.base.lookup_default PositiveSet.rev PositiveMap.empty under_with_unification_resultT_relation_hetero under_with_unification_resultT'_relation_hetero maybe_option_eq
                           List.map List.fold_right PositiveSet.union PositiveSet.xelements List.rev List.app projT1 projT2 list_rect PositiveSet.add PositiveSet.rev PositiveSet.rev_append PositiveMap.add PositiveMap.find orb] in
                rewrite_rules_goodT_curried_cps_folded.

          Lemma rewrite_rules_goodT_curried_cps_folded_Proper_impl rews1 rews2 H
            : Proper (Basics.impl ==> Basics.impl) (rewrite_rules_goodT_curried_cps_folded rews1 rews2 H).
          Proof using Type.
            cbv [impl]; intros P Q H'.
            revert dependent rews2; induction rews1, rews2; cbn; auto.
          Qed.
          Lemma rewrite_rules_goodT_curried_cps_Proper_impl rews1 rews2 H
            : Proper (Basics.impl ==> Basics.impl) (rewrite_rules_goodT_curried_cps rews1 rews2 H).
          Proof using Type.
            apply rewrite_rules_goodT_curried_cps_folded_Proper_impl.
          Qed.

          Lemma wf_rewrite_rule_data_by_curried G t p r1 r2
            : @wf_rewrite_rule_data_curried G t p r1 r2
              -> @wf_rewrite_rule_data G t p r1 r2.
          Proof using try_make_transport_base_cps_correct.
            cbv [wf_rewrite_rule_data_curried wf_rewrite_rule_data wf_with_unif_rewrite_ruleTP_gen wf_with_unif_rewrite_ruleTP_gen_curried].
            intro H.
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

          Lemma rewrite_rules_goodT_by_curried
                (rews1 : rewrite_rulesT1) (rews2 : rewrite_rulesT2)
                (H : List.map (@projT1 _ _) rews1 = List.map (@projT1 _ _) rews2)
            : rewrite_rules_goodT_curried_cps rews1 rews2 H (rewrite_rules_goodT rews1 rews2).
          Proof using try_make_transport_base_cps_correct.
            change rewrite_rules_goodT_curried_cps with rewrite_rules_goodT_curried_cps_folded.
            cbv [rewrite_rules_goodT].
            revert rews2 H; induction rews1 as [|[r p] rews1 IHrews], rews2 as [|[? ?] ?]; intro H.
            all: try solve [ cbn; tauto ].
            all: cbn [rewrite_rules_goodT_curried_cps_folded List.In projT2 projT1 Datatypes.fst Datatypes.snd] in *.
            all: intro H'; eapply rewrite_rules_goodT_curried_cps_folded_Proper_impl; [ | eapply IHrews ].
            all: repeat first [ progress cbv [impl]
                              | progress destruct_head'_or
                              | progress inversion_sigma
                              | progress subst
                              | progress destruct_head'_and
                              | progress destruct_head'_sig
                              | progress destruct_head'_or
                              | progress inversion_prod
                              | progress inversion_sigma
                              | (exists eq_refl)
                              | apply conj
                              | apply (f_equal S)
                              | progress cbn [eq_rect Datatypes.snd List.length List.In List.combine] in *
                              | solve [ eauto using wf_rewrite_rule_data_by_curried ]
                              | progress intros ].
          Qed.
        End with_var2.

        Section with_interp.
          Context {base_interp : base -> Type}.
          Local Notation base_type_interp := (base.interp base_interp).
          Context (ident_interp : forall t, ident t -> type.interp base_type_interp t)
                  {ident_interp_Proper : forall t, Proper (eq ==> type.eqv) (ident_interp t)}.
          Local Notation var := (type.interp base_type_interp) (only parsing).
          Local Notation expr := (@expr.expr base_type ident var).
          Local Notation rewrite_rulesT := (@rewrite_rulesT base ident var pident pident_arg_types).
          Local Notation rewrite_rule_data := (@rewrite_rule_data base ident var pident pident_arg_types).
          Local Notation with_unif_rewrite_ruleTP_gen := (@with_unif_rewrite_ruleTP_gen base ident var pident pident_arg_types).
          Local Notation normalize_deep_rewrite_rule := (@normalize_deep_rewrite_rule base ident var).
          Local Notation deep_rewrite_ruleTP_gen := (@deep_rewrite_ruleTP_gen base ident var).

          Local Notation UnderLets_maybe_interp with_lets
            := (if with_lets as with_lets' return (if with_lets' then UnderLets var _ else _) -> _
                then UnderLets.interp ident_interp
                else (fun x => x)).
          Local Notation UnderLets_maybe_wf with_lets G
            := (if with_lets as with_lets' return (if with_lets' then UnderLets var _ else _) -> (if with_lets' then UnderLets var _ else _) -> _
                then UnderLets.wf (fun G' => expr.wf G') G
                else expr.wf G).
          Definition value'_interp {with_lets t} (v : @value' var with_lets t)
            : var t
            := expr.interp ident_interp (reify v).
          Local Notation expr_interp_related := (@expr.interp_related _ ident _ ident_interp).
          Local Notation UnderLets_interp_related := (@UnderLets.interp_related _ ident _ ident_interp _ _ expr_interp_related).

          Fixpoint value_interp_related {t with_lets} : @value' var with_lets t -> type.interp base_type_interp t -> Prop
            := match t, with_lets with
               | type.base _, true => UnderLets_interp_related
               | type.base _, false => expr_interp_related
               | type.arrow s d, _
                 => fun (f1 : @value' _ _ s -> @value' _ _ d) (f2 : type.interp _ s -> type.interp _ d)
                    => forall x1 x2,
                        @value_interp_related s _ x1 x2
                        -> @value_interp_related d _ (f1 x1) (f2 x2)
               end.
          Fixpoint rawexpr_interp_related (r1 : rawexpr) : type.interp base_type_interp (type_of_rawexpr r1) -> Prop
            := match r1 return type.interp base_type_interp (type_of_rawexpr r1) -> Prop with
               | rExpr _ e1
               | rValue (type.base _) e1
                 => expr_interp_related e1
               | rValue t1 v1
                 => value_interp_related v1
               | rIdent _ t1 idc1 t'1 alt1
                 => fun v2
                    => expr.interp ident_interp alt1 == v2
                       /\ existT expr t1 (expr.Ident idc1) = existT expr t'1 alt1
               | rApp f1 x1 t1 alt1
                 => match alt1 in expr.expr t return type.interp base_type_interp t -> Prop with
                    | expr.App s d af ax
                      => fun v2
                         => exists fv xv (pff : type.arrow s d = type_of_rawexpr f1) (pfx : s = type_of_rawexpr x1),
                             @expr_interp_related _ af fv
                             /\ @expr_interp_related _ ax xv
                             /\ @rawexpr_interp_related f1 (rew pff in fv)
                             /\ @rawexpr_interp_related x1 (rew pfx in xv)
                             /\ fv xv = v2
                    | _ => fun _ => False
                    end
               end.
          Definition unification_resultT'_interp_related {t p evm}
            : @unification_resultT' (@value var) t p evm -> @unification_resultT' var t p evm -> Prop
            := related_unification_resultT' (fun t => value_interp_related).
          Definition unification_resultT_interp_related {t p}
            : @unification_resultT (@value var) t p -> @unification_resultT var t p -> Prop
            := related_unification_resultT (fun t => value_interp_related).
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
          Fixpoint reify_interp_related {t with_lets} v1 v2 {struct t}
            : @value_interp_related t with_lets v1 v2
              -> expr_interp_related (reify v1) v2
          with reflect_interp_related {t with_lets} e1 v2 {struct t}
               : expr_interp_related e1 v2
                 -> @value_interp_related t with_lets (reflect e1) v2.
          Proof using Type.
            all: destruct t as [|s d];
              [ clear reify_interp_related reflect_interp_related
              | pose proof (reify_interp_related s false) as reify_interp_related_s;
                pose proof (reflect_interp_related s false) as reflect_interp_related_s;
                pose proof (reify_interp_related d true) as reify_interp_related_d;
                pose proof (reflect_interp_related d true) as reflect_interp_related_d;
                clear reify_interp_related reflect_interp_related ].
            all: repeat first [ progress cbn [reify reflect] in *
                              | progress fold (@reify) (@reflect) in *
                              | progress cbv [expr.interp_related] in *
                              | progress cbn [expr.interp_related_gen value_interp_related] in *
                              | break_innermost_match_step
                              | match goal with
                                | [ |- context G[expr.interp_related_gen ?ii (@type.eqv) (UnderLets.to_expr ?v)] ]
                                  => let G' := context G[expr_interp_related (UnderLets.to_expr v)] in
                                     change G';
                                     rewrite <- UnderLets.to_expr_interp_related_iff
                                end
                              | rewrite <- UnderLets.to_expr_interp_related_iff
                              | exact id
                              | assumption
                              | solve [ eauto ]
                              | progress intros
                              | match goal with H : _ |- _ => apply H; clear H end
                              | progress repeat esplit ].
          Qed.
          Lemma expr_of_rawexpr_interp_related r v
            : rawexpr_interp_related r v
              -> expr_interp_related (expr_of_rawexpr r) v.
          Proof using Type.
            cbv [expr.interp_related]; revert v; induction r; cbn [expr_of_rawexpr expr.interp_related_gen rawexpr_interp_related]; intros.
            all: repeat first [ progress destruct_head'_and
                              | progress destruct_head'_ex
                              | progress subst
                              | progress inversion_sigma
                              | progress cbn [eq_rect type_of_rawexpr expr.interp expr.interp_related_gen type_of_rawexpr] in *
                              | assumption
                              | exfalso; assumption
                              | apply conj
                              | break_innermost_match_hyps_step
                              | solve [ eauto ]
                              | apply reify_interp_related ].
          Qed.
          Lemma value_of_rawexpr_interp_related {e v}
            : rawexpr_interp_related e v -> value_interp_related (value_of_rawexpr e) v.
          Proof using Type.
            destruct e; cbn [rawexpr_interp_related value_of_rawexpr]; break_innermost_match.
            all: repeat first [ progress intros
                              | exfalso; assumption
                              | progress inversion_sigma
                              | progress subst
                              | progress cbn [eq_rect expr.interp type_of_rawexpr] in *
                              | progress destruct_head'_ex
                              | progress destruct_head'_and
                              | assumption
                              | apply reflect_interp_related
                              | progress cbn [expr.interp_related_gen]
                              | progress cbv [expr.interp_related]
                              | solve [ eauto ] ].
          Qed.
          Lemma rawexpr_interp_related_Proper_rawexpr_equiv_expr {t e re v}
                (H : rawexpr_equiv_expr e re)
            : @expr_interp_related t e v
              -> rawexpr_interp_related re (rew eq_type_of_rawexpr_equiv_expr H in v).
          Proof using reflect_base_beq.
            revert t e H v; induction re.
            all: repeat first [ progress intros
                              | progress cbn [rawexpr_equiv_expr eq_rect rawexpr_interp_related type_of_rawexpr expr.interp_related_gen] in *
                              | progress cbv [expr.interp_related] in *
                              | progress subst
                              | progress destruct_head'_and
                              | progress destruct_head'_ex
                              | progress inversion_sigma
                              | apply conj
                              | eassumption
                              | reflexivity
                              | progress eliminate_hprop_eq
                              | break_innermost_match_step
                              | solve [ eauto ]
                              | exfalso; assumption
                              | instantiate (1:=eq_refl)
                              | match goal with
                                | [ |- context[@eq_type_of_rawexpr_equiv_expr ?var ?t ?r1 ?r2 ?H] ]
                                  => generalize (@eq_type_of_rawexpr_equiv_expr var t r1 r2 H)
                                | [ _ : context[@eq_type_of_rawexpr_equiv_expr ?var ?t ?r1 ?r2 ?H] |- _ ]
                                  => generalize dependent (@eq_type_of_rawexpr_equiv_expr var t r1 r2 H)
                                | [ IH : forall t e, rawexpr_equiv_expr e ?re -> _, H : rawexpr_equiv_expr _ ?re |- _ ]
                                  => specialize (IH _ _ H)
                                | [ IH : forall v, expr_interp_related ?e v -> _, H : expr_interp_related ?e _ |- _ ]
                                  => specialize (IH _ H)
                                | [ |- exists fv xv pff pfx, _ /\ _ /\ _ /\ _ ]
                                  => do 4 eexists; repeat apply conj; [ eassumption | eassumption | | | reflexivity ]
                                end ].
          Qed.
          Lemma rawexpr_interp_related_Proper_rawexpr_equiv_expr_no_rew {re e v}
                (H : rawexpr_equiv_expr e re)
            : @expr_interp_related _ e v
              -> rawexpr_interp_related re v.
          Proof using reflect_base_beq.
            intro H'.
            generalize (@rawexpr_interp_related_Proper_rawexpr_equiv_expr _ e re v H H').
            generalize (eq_type_of_rawexpr_equiv_expr H); intro; eliminate_hprop_eq.
            exact id.
          Qed.
          Lemma rawexpr_interp_related_Proper_rawexpr_equiv_expr_rew_gen {t e re v}
                (H : rawexpr_equiv_expr e re)
            : forall pf,
              @expr_interp_related t e v
              -> rawexpr_interp_related re (rew [type.interp base_type_interp] pf in v).
          Proof using reflect_base_beq.
            intro; subst; apply rawexpr_interp_related_Proper_rawexpr_equiv_expr_no_rew; assumption.
          Qed.
          Lemma rawexpr_interp_related_Proper_rawexpr_equiv {re1 re2 v}
                (H : rawexpr_equiv re1 re2)
            : rawexpr_interp_related re1 v
              -> rawexpr_interp_related re2 (rew [type.interp base_type_interp] eq_type_of_rawexpr_equiv H in v).
          Proof using reflect_base_beq.
            revert re2 H; induction re1, re2; intros H H'.
            all: repeat first [ progress cbn [rawexpr_equiv rawexpr_interp_related eq_rect type_of_rawexpr projT1 projT2 rawexpr_equiv_expr expr.interp_related_gen] in *
                              | progress cbv [expr.interp_related] in *
                              | eassumption
                              | reflexivity
                              | progress intros
                              | progress destruct_head'_and
                              | progress destruct_head'_ex
                              | progress inversion_sigma
                              | progress subst
                              | progress eliminate_hprop_eq
                              | apply conj
                              | exfalso; assumption
                              | break_innermost_match_step
                              | break_innermost_match_hyps_step
                              | solve [ eauto ]
                              | expr.inversion_expr_step
                              | type.inversion_type_step
                              | match goal with
                                | [ IH : forall v re', rawexpr_equiv ?re re' -> _, H : rawexpr_equiv ?re _ |- _ ] => specialize (fun v => IH v _ H)
                                | [ H : forall v, rawexpr_interp_related ?re v -> _, H' : rawexpr_interp_related ?re _ |- _ ] => specialize (H _ H')
                                | [ IH : forall v re', rawexpr_equiv ?re re' -> _, H : rawexpr_equiv_expr ?e ?re |- _ ]
                                  => specialize (fun v => IH v (rExpr e) ltac:(rewrite rawexpr_equiv_expr_to_rawexpr_equiv in H; apply H))
                                | [ H : context[rew _ in rew _ in _] |- _ ]
                                  => rewrite <- eq_trans_rew_distr in H
                                | [ |- context[@eq_type_of_rawexpr_equiv ?var ?r1 ?r2 ?H] ]
                                  => generalize (@eq_type_of_rawexpr_equiv var r1 r2 H)
                                | [ H : context[@eq_type_of_rawexpr_equiv ?var ?r1 ?r2 ?H] |- _ ]
                                  => generalize dependent (@eq_type_of_rawexpr_equiv var r1 r2 H)
                                | [ H : context[rew eq_trans ?a ?b in _] |- _ ]
                                  => generalize dependent (eq_trans a b)
                                | [ H : _ = _ :> and _ _ |- _ ] => clear H
                                | [ |- exists fv xv pff pfx, _ /\ _ /\ _ /\ _ ]
                                  => do 4 eexists; repeat apply conj; [ eassumption | eassumption | | | reflexivity ]
                                end
                              | unshelve (eapply rawexpr_interp_related_Proper_rawexpr_equiv_expr; eassumption); assumption ].
          Qed.

          Lemma rawexpr_interp_related_Proper_rawexpr_equiv_rew_gen {re1 re2 v}
                (H : rawexpr_equiv re1 re2)
            : forall pf,
              rawexpr_interp_related re1 v
              -> rawexpr_interp_related re2 (rew [type.interp base_type_interp] pf in v).
          Proof using reflect_base_beq.
            intros pf H'.
            generalize (@rawexpr_interp_related_Proper_rawexpr_equiv re1 re2 v H H').
            generalize (eq_type_of_rawexpr_equiv H); intro pf'.
            clear -reflect_base_beq; generalize dependent (type_of_rawexpr re1); intros; subst.
            eliminate_hprop_eq.
            assumption.
          Qed.

          Fixpoint pattern_default_interp' {K t} (p : pattern t) evm {struct p} : (var (pattern.type.subst_default t evm) -> K) -> @with_unification_resultT' var t p evm K
            := match p in pattern.pattern t return (var (pattern.type.subst_default t evm) -> K) -> @with_unification_resultT' var t p evm K with
               | pattern.Wildcard t => fun k v => k v
               | pattern.Ident t idc
                 => fun k
                    => lam_type_of_list (fun args => k (ident_interp _(pident_to_typed _ idc _ args)))
               | pattern.App s d f x
                 => fun k
                    => @pattern_default_interp'
                         _ _ f evm
                         (fun ef
                          => @pattern_default_interp'
                               _ _ x evm
                               (fun ex
                                => k (ef ex)))
               end.

          Lemma interp_Base_value {t v1 v2}
            : value_interp_related v1 v2
              -> value_interp_related (@Base_value var t v1) v2.
          Proof using Type.
            cbv [Base_value]; destruct t; exact id.
          Qed.

          Lemma interp_splice_under_lets_with_value_of_ex {T T' t R e f v}
            : (exists fv (xv : T'),
                  UnderLets.interp_related ident_interp R e xv
                  /\ (forall x1 x2,
                         R x1 x2
                         -> value_interp_related (f x1) (fv x2))
                  /\ fv xv = v)
              -> value_interp_related (@splice_under_lets_with_value var T t e f) v.
          Proof using Type.
            induction t as [|s IHs d IHd].
            all: repeat first [ progress cbn [value_interp_related splice_under_lets_with_value] in *
                              | progress intros
                              | progress destruct_head'_ex
                              | progress destruct_head'_and
                              | progress subst
                              | eassumption
                              | solve [ eauto ]
                              | now (eapply UnderLets.splice_interp_related_of_ex; eauto)
                              | match goal with
                                | [ H : _ |- _ ] => eapply H; clear H
                                | [ |- exists fv xv, _ /\ _ /\ _ ]
                                  => do 2 eexists; repeat apply conj; [ eassumption | | ]
                                end ].
          Qed.

          Lemma interp_splice_value_with_lets_of_ex {t t' e f v}
            : (exists fv xv,
                  value_interp_related e xv
                  /\ (forall x1 x2,
                         value_interp_related x1 x2
                         -> value_interp_related (f x1) (fv x2))
                  /\ fv xv = v)
              -> value_interp_related (@splice_value_with_lets var t t' e f) v.
          Proof using Type.
            cbv [splice_value_with_lets]; break_innermost_match.
            { apply interp_splice_under_lets_with_value_of_ex. }
            { intros; destruct_head'_ex; destruct_head'_and; subst; eauto. }
          Qed.

          Definition pattern_default_interp {t} (p : pattern t)
            : @with_unification_resultT var t p var
            (*: @with_unif_rewrite_ruleTP_gen var t p false false false*)
            := pattern.type.lam_forall_vars
                 (fun evm
                  => pattern_default_interp' p evm id).

          Lemma app_lam_forall_vars_not_None_iff {k f p} {args}
            : (@pattern.type.app_forall_vars base p k (pattern.type.lam_forall_vars f) args <> None)
              <-> (forall x, PositiveSet.mem x p = true -> PositiveMap.find x args <> None).
          Proof using Type.
            setoid_rewrite <- PositiveSetFacts.In_elements_mem_iff; setoid_rewrite List.in_rev.
            cbv [pattern.type.app_forall_vars pattern.type.lam_forall_vars].
            generalize (PositiveMap.empty base_type).
            induction (List.rev (PositiveSet.elements p)) as [|x xs IHxs];
              cbn [pattern.type.app_forall_vars_gen pattern.type.lam_forall_vars_gen List.In].
            { intuition congruence. }
            { repeat first [ progress cbn [List.In] in *
                           | progress specialize_by_assumption
                           | progress split_contravariant_or
                           | progress destruct_head'_ex
                           | progress inversion_option
                           | progress subst
                           | progress intros
                           | progress destruct_head'_or
                           | solve [ eauto ]
                           | match goal with
                             | [ H : forall x, _ = x -> _ |- _ ] => specialize (H _ eq_refl)
                             | [ H : ?x <> None |- _ ]
                               => assert (exists v, x = Some v) by (destruct x; [ eexists; reflexivity | congruence ]); clear H
                             | [ |- ?x <> None <-> ?RHS ]
                               => let v := match x with context[match ?v with None => _ | _ => _ end] => v end in
                                  let f := match (eval pattern v in x) with ?f _ => f end in
                                  change (f v <> None <-> RHS); destruct v eqn:?
                             | [ H : forall t, _ <-> _ |- _ ] => setoid_rewrite H; clear H
                             end
                           | apply conj
                           | congruence ]. }
          Qed.

          Definition deep_rewrite_ruleTP_gen_good_relation
                     {should_do_again with_opt under_lets : bool} {t}
                     (v1 : @deep_rewrite_ruleTP_gen should_do_again with_opt under_lets t)
                     (v2 : var t)
            : Prop
            := let v1 := normalize_deep_rewrite_rule v1 in
               match v1 with
               | None => True
               | Some v1 => UnderLets.interp_related
                              ident_interp
                              (if should_do_again
                                  return (@expr.expr base_type ident (if should_do_again then @value var else var) t) -> _
                               then expr.interp_related_gen ident_interp (fun t => value_interp_related)
                               else expr_interp_related)
                              v1
                              v2
               end.

          Definition rewrite_rule_data_interp_goodT
                     {t} {p : pattern t} (r : @rewrite_rule_data t p)
            : Prop
            := forall x y,
              related_unification_resultT (fun t => value_interp_related) x y
              -> option_eq
                   (fun fx gy
                    => related_sigT_by_eq
                         (fun evm
                          => @deep_rewrite_ruleTP_gen_good_relation
                               (rew_should_do_again r) (rew_with_opt r) (rew_under_lets r) (pattern.type.subst_default t evm))
                         fx gy)
                   (app_with_unification_resultT_cps (rew_replacement r) x _ (@Some _))
                   (app_with_unification_resultT_cps (pattern_default_interp p) y _ (@Some _)).

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
                 (rew_replacement r)
                 (pattern_default_interp p).

          Fixpoint rewrite_rules_interp_goodT_curried_cps_folded
                   (rews : rewrite_rulesT)
                   (specs : list (bool * Prop))
                   (final : Prop)
            := match rews with
               | r :: rews
                 => (snd (hd (true, True) specs)
                     -> rewrite_rule_data_interp_goodT_curried (projT2 r))
                    -> rewrite_rules_interp_goodT_curried_cps_folded rews (tl specs) final
               | nil => final
               end.

          Definition rewrite_rules_interp_goodT_curried_cps
            := Eval cbv [id
                           rewrite_rules_interp_goodT_curried_cps_folded snd hd tl projT1 projT2 rewrite_rule_data_interp_goodT_curried
                           rewrite_rule_data_interp_goodT_curried under_with_unification_resultT_relation_hetero under_with_unification_resultT'_relation_hetero wf_with_unification_resultT under_type_of_list_relation_cps under_type_of_list_relation1_cps pattern.pattern_of_anypattern pattern.type_of_anypattern rew_replacement rew_should_do_again rew_with_opt rew_under_lets wf_with_unification_resultT pattern_default_interp pattern.type.under_forall_vars_relation pattern.type.under_forall_vars_relation1 deep_rewrite_ruleTP_gen with_unification_resultT' pattern.ident.arg_types pattern.type.lam_forall_vars Compilers.pattern.type.lam_forall_vars_gen pattern_default_interp' pattern.collect_vars PositiveMap.empty pattern.type.collect_vars PositiveSet.elements PositiveSet.union pattern.base.collect_vars PositiveSet.empty PositiveSet.xelements lam_type_of_list id pattern.ident.to_typed under_type_of_list_relation_cps deep_rewrite_ruleTP_gen_good_relation normalize_deep_rewrite_rule pattern.type.subst_default PositiveSet.add PositiveSet.rev PositiveSet.rev_append PositiveMap.add option_bind' wf_value value pattern.base.subst_default pattern.base.lookup_default PositiveMap.find rewrite_ruleTP ident.smart_Literal value_interp_related
                           Reify.expr_value_to_rewrite_rule_replacement UnderLets.flat_map reify_expr_beta_iota reflect_expr_beta_iota reflect_ident_iota Compile.reify_to_UnderLets UnderLets.of_expr Compile.Base_value
                           Classes.base Classes.ident Classes.base_interp Classes.ident_interp
                           List.map List.fold_right List.rev list_rect orb List.app
                        ] in
                rewrite_rules_interp_goodT_curried_cps_folded.

          Lemma rewrite_rules_interp_goodT_curried_cps_folded_Proper_impl rews specs
            : Proper (Basics.impl ==> Basics.impl) (rewrite_rules_interp_goodT_curried_cps_folded rews specs).
          Proof using Type.
            cbv [impl]; intros P Q H.
            revert specs; induction rews, specs; cbn; auto.
          Qed.
          Lemma rewrite_rules_interp_goodT_curried_cps_Proper_impl rews specs
            : Proper (Basics.impl ==> Basics.impl) (rewrite_rules_interp_goodT_curried_cps rews specs).
          Proof using Type.
            apply rewrite_rules_interp_goodT_curried_cps_folded_Proper_impl.
          Qed.

          Lemma rewrite_rule_data_interp_goodT_by_curried t p r
            : @rewrite_rule_data_interp_goodT_curried t p r
              -> @rewrite_rule_data_interp_goodT t p r.
          Proof using try_make_transport_base_cps_correct.
            cbv [rewrite_rule_data_interp_goodT rewrite_rule_data_interp_goodT_curried].
            intro H.
            repeat (let x := fresh "x" in intro x; specialize (H x)).
            intros X Y HXY.
            pose proof (related_app_with_unification_resultT _ _ _ _ _ _ ltac:(eassumption) HXY) as H'.
            progress cbv [deep_rewrite_ruleTP_gen] in *.
            match goal with
            | [ H : option_eq ?R ?x ?y |- option_eq ?R' ?x' ?y' ]
              => change (option_eq R' x y); destruct x eqn:?, y eqn:?; cbv [option_eq] in H |- *
            end.
            all: repeat first [ reflexivity
                              | progress inversion_option
                              | exfalso; assumption
                              | assumption ].
          Qed.

          Lemma rewrite_rules_interp_goodT_by_curried rews specs
                (proofs : PrimitiveHList.hlist (@snd bool Prop) specs)
            : rewrite_rules_interp_goodT_curried_cps rews specs (rewrite_rules_interp_goodT rews).
          Proof using try_make_transport_base_cps_correct.
            change rewrite_rules_interp_goodT_curried_cps with rewrite_rules_interp_goodT_curried_cps_folded.
            cbv [rewrite_rules_interp_goodT].
            revert specs proofs.
            induction rews as [|[r p] rews IHrews], specs as [|[? ?] specs];
              cbn [PrimitiveHList.hlist];
              intro proofs; destruct_head' PrimitiveProd.Primitive.prod.
            all: try solve [ cbn; tauto ].
            all: cbn [rewrite_rules_interp_goodT_curried_cps_folded List.In projT2 projT1 Datatypes.fst Datatypes.snd] in *.
            all: intro H; eapply rewrite_rules_interp_goodT_curried_cps_folded_Proper_impl; [ | eapply IHrews ].
            all: repeat first [ progress cbv [impl]
                              | progress destruct_head'_or
                              | progress inversion_sigma
                              | progress subst
                              | progress cbn [eq_rect Datatypes.snd hd tl] in *
                              | solve [ eauto using rewrite_rule_data_interp_goodT_by_curried ]
                              | progress intros ].
          Qed.
        End with_interp.
      End with_var.
    End Compile.

    (** Now we prove the [wf] and [interp] properties about
       definitions used only in reification of rewrite rules, which
       are used to make proving [wf] / [interp] of concrete rewrite
       rules easier. *)
    Module Reify.
      Import Compile.
      Import Rewriter.Compilers.RewriteRules.Compile.
      Import Rewriter.Compilers.RewriteRules.Reify.

      Ltac wf_ctors :=
        repeat first [ match goal with
                       | [ |- UnderLets.wf _ _ (UnderLets.Base _) (UnderLets.Base _) ] => constructor
                       | [ |- expr.wf _ (_ @ _) (_ @ _) ] => constructor
                       | [ |- expr.wf ?seg (#_) (#_) ]
                         => (tryif is_evar seg then instantiate (1:=nil) else idtac);
                            constructor
                       | [ |- expr.wf _ ($_) ($_) ] => constructor
                       | [ |- expr.wf _ (expr.Abs _) (expr.Abs _) ] => constructor; intros
                       | [ |- expr.wf _ (UnderLets.to_expr _) (UnderLets.to_expr _) ] => apply UnderLets.wf_to_expr
                       | [ H : expr.wf ?G ?x ?y |- expr.wf ?seg ?x ?y ] => first [ is_evar seg | constr_eq G seg ]; exact H
                       | [ H : List.Forall2 (expr.wf _) ?x ?y |- List.Forall2 (expr.wf _) ?x ?y ]
                         => eapply Forall2_Proper_impl; [ | reflexivity | reflexivity | exact H ]; repeat intro
                       | [ H : List.Forall2 (expr.wf ?G) ?x ?y |- List.Forall2 (expr.wf ?seg) ?x ?y ]
                         => first [ is_evar seg | constr_eq seg G ]; exact H
                       | [ H : List.Forall2 ?P ?x ?y |- List.Forall2 ?Pe ?x ?y ]
                         => first [ is_evar Pe | constr_eq Pe P ]; exact H
                       | [ H : forall x y, List.In (x, y) ?G -> expr.wf ?G' x y, H' : List.In (?v1, ?v2) ?G |- expr.wf ?seg ?v1 ?v2 ]
                         => first [ is_evar seg | constr_eq seg G' ]; exact (H _ _ H')
                       | [ |- expr.wf _ (reify_list _) (reify_list _) ]
                         => rewrite expr.wf_reify_list
                       | [ H : expr.wf _ (reify_list ?xs) (reify_list ?ys) |- List.Forall2 _ ?xs ?xy ]
                         => rewrite expr.wf_reify_list in H
                       | [ |- ?G ] => tryif has_evar G then fail else solve [ destruct_head'_ex; subst; wf_t ]
                       end ].
      Ltac handle_wf_rec do_try :=
        let tac _
            := solve
                 [ repeat
                     first
                     [ progress wf_ctors
                     | handle_wf_rec do_try
                     | match goal with
                       | [ |- List.In ?v ?seg ] => is_evar seg; unify seg (cons v nil)
                       | [ |- List.In ?v (?seg1 ++ ?seg2) ]
                         => rewrite in_app_iff;
                            first [ is_evar seg1; left
                                  | is_evar seg2; right ]
                       (*| [ |- ?x ++ ?y = ?x ++ ?z ] => apply f_equal2*)
                       | [ |- ?x = ?y ]
                         => is_evar x; tryif has_evar y then fail else reflexivity
                       | [ |- forall t v1 v2, List.In (existT _ t (v1, v2)) (?x ++ ?G1) -> List.In (existT _ t (v1, v2)) (?x ++ ?G2) ]
                         => is_evar G2;
                            tryif first [ has_evar x | has_evar G1 ] then fail else (do 3 intro; exact id)
                       end ] ] in
        match goal with
        | [ H : expr.wf ?segv ?x1 ?x2
            |- UnderLets.wf _ ?Gv (nat_rect _ _ _ _ ?x1) (nat_rect _ _ _ _ ?x2) ]
          => unshelve
               (eapply UnderLets.wf_Proper_list;
                [ | | eapply @UnderLets.wf_nat_rect_arrow with (R' := fun G' => expr.wf G') (seg:=segv) (G:=Gv); intros ];
                [ try (intros; subst; match goal with |- expr.wf _ _ _ => shelve end).. ];
                [ try (intros; subst; match goal with |- UnderLets.wf _ _ _ _ => shelve end).. ];
                [ try match goal with |- _ = _ => shelve end.. ]);
             shelve_unifiable;
             do_try tac
        | [ H : expr.wf ?segv ?x1 ?x2
            |- UnderLets.wf _ ?Gv (list_rect _ _ _ _ ?x1) (list_rect _ _ _ _ ?x2) ]
          => unshelve
               (eapply UnderLets.wf_Proper_list;
                [ | | eapply @UnderLets.wf_list_rect_arrow with (R' := fun G' => expr.wf G') (seg:=segv) (G:=Gv); intros ];
                [ try (intros; subst; match goal with |- expr.wf _ _ _ => shelve end).. ];
                [ try (intros; subst; match goal with |- UnderLets.wf _ _ _ _ => shelve end).. ];
                [ try match goal with |- _ = _ => shelve end.. ]);
             shelve_unifiable;
             do_try tac
        | [ |- UnderLets.wf _ _ ?x ?y ]
          => let f := head x in
             let g := head y in
             is_var f; is_var g;
             unshelve
               (lazymatch goal with
                | [ H : context[UnderLets.wf _ _ (f _) (g _)] |- _ ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H ]
                | [ H : context[UnderLets.wf _ _ (f _ _) (g _ _)] |- _ ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H ]
                | [ H : context[UnderLets.wf _ _ (f _ _ _) (g _ _ _)] |- _ ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H ]
                | [ H : context[UnderLets.wf _ _ (f _ _ _ _) (g _ _ _ _)] |- _ ]
                  => eapply UnderLets.wf_Proper_list; [ | | eapply H ]
                end;
                [ try (intros; subst; match goal with |- expr.wf _ _ _ => shelve end).. ];
                [ try (intros; subst; match goal with |- UnderLets.wf _ _ _ _ => shelve end).. ];
                [ try match goal with |- _ = _ => shelve end.. ]);
             shelve_unifiable;
             do_try tac
        end.

      Ltac reify_wf_t_step :=
        first [ progress subst
              | match goal with
                | [ H : invert_expr.reflect_list ?v = Some _, H' : invert_expr.reflect_list ?v' = None |- _ ]
                  => first [ erewrite <- expr.wf_reflect_list in H' by eassumption
                           | erewrite -> expr.wf_reflect_list in H' by eassumption ];
                     exfalso; clear -H H'; congruence
                end
              | progress inversion_option
              | progress destruct_head'_False
              | progress intros
              | progress cbn [(*invert_expr.invert_Literal invert_expr.ident.invert_Literal*) value' type.interp base.interp (*base.base_interp*)] in *
              | match goal with
                | [ H : ident.ident_Literal _ = ident.ident_Literal _ |- _ ]
                  => pose proof (f_equal invert_expr.invert_ident_Literal H); clear H
                end
              | progress expr.inversion_wf_constr
              | break_innermost_match_hyps_step
              | progress expr.inversion_wf_one_constr
              | progress expr.invert_subst
              | progress expr.inversion_expr
              | progress expr.invert_match
              | progress wf_ctors
              | match goal with
                | [ |- UnderLets.wf _ _ (nat_rect _ _ _ _) (nat_rect _ _ _ _) ]
                  => apply UnderLets.wf_nat_rect; intros
                | [ |- UnderLets.wf _ ?G (list_rect _ _ _ _) (list_rect _ _ _ _) ]
                  => apply @UnderLets.wf_list_rect with (RA := expr.wf G)
                | [ |- UnderLets.wf _ _ (UnderLets.splice _ _) (UnderLets.splice _ _) ]
                  => apply @UnderLets.wf_splice with (P := fun G => expr.wf G); intros; subst
                | [ H : expr.wf _ (reify_list ?l1) (reify_list ?l2)
                    |- expr.wf ?G (nth_default ?d1 ?l1 ?n) (nth_default ?d2 ?l2 ?n) ]
                  => cut (List.Forall2 (expr.wf G) l1 l2 /\ expr.wf G d1 d2);
                     [ rewrite Forall2_forall_iff'';
                       let H := fresh in intro H; apply H
                     | split ]
                | [ |- ?x = ?x ] => reflexivity
                end
              | progress handle_wf_rec ltac:(fun tac => try tac (); tac ()) ].
      Ltac reify_wf_t := repeat reify_wf_t_step.

      Section with_base.
        Context {base : Type}
                {base_beq : base -> base -> bool}.
        Local Notation base_type := (base.type base).
        Local Notation type := (type.type base_type).
        Context {ident : type -> Type}
                {base_interp : base -> Type}
                {ident_interp : forall t, ident t -> type.interp (base.interp base_interp) t}
                {baseTypeHasNat : base.type.BaseTypeHasNatT base}
                {buildIdent : ident.BuildIdentT base_interp ident}
                {buildEagerIdent : ident.BuildEagerIdentT ident}
                {toRestrictedIdent : ident.ToRestrictedIdentT ident}
                {toFromRestrictedIdent : ident.ToFromRestrictedIdentT ident}
                {invertIdent : invert_expr.InvertIdentT base_interp ident}
                {baseHasNatCorrect : base.BaseHasNatCorrectT base_interp}
                {try_make_transport_base_cps : type.try_make_transport_cpsT base}
                {buildInvertIdentCorrect : invert_expr.BuildInvertIdentCorrectT}
                {reflect_base_beq : reflect_rel (@eq base) base_beq}
                {try_make_transport_base_cps_correct : type.try_make_transport_cps_correctT base}.

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Lemma wf_reflect_ident_iota G
            : forall {t} (idc : ident t),
              option_eq
                (wf_value G)
                (reflect_ident_iota (var:=var1) idc)
                (reflect_ident_iota (var:=var2) idc).
          Proof using try_make_transport_base_cps_correct reflect_base_beq buildInvertIdentCorrect.
            cbv [reflect_ident_iota]; intros t idc.
            cbv [ident.eager_ident_rect].
            generalize (ident.transparent_fromToRestrictedIdent_eq idc).
            destruct (toRestrictedIdent t idc); intro H; cbn in H; inversion_option; subst; cbn.
            destruct_head' (@ident.restricted_ident); cbv [option_eq]; try reflexivity.
            all: cbv [wf_value wf_value']; intros; subst; break_innermost_match; cbn [reify reflect] in *;
              lazymatch goal with
              | [ H : invert_expr.reflect_list ?v = Some _, H' : invert_expr.reflect_list ?v' = None |- _ ]
                => first [ erewrite <- expr.wf_reflect_list in H' by eassumption
                         | erewrite -> expr.wf_reflect_list in H' by eassumption ];
                     exfalso; clear -H H'; congruence
              | _ => idtac
              end;
              expr.invert_subst; subst.
            all: reify_wf_t.
          Qed.

          Lemma wf_reflect_expr_beta_iota
                {reflect_ident_iota1 reflect_ident_iota2}
                (Hwf_reflect_ident_iota
                 : forall G {t} (idc : ident t),
                    option_eq
                      (@wf_value _ ident var1 var2 G _)
                      (@reflect_ident_iota1 t idc)
                      (@reflect_ident_iota2 t idc))
                G G'
                (HG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> wf_value G v1 v2)
                {t} e1 e2
                (Hwf : expr.wf G' e1 e2)
            : UnderLets.wf
                (fun G'' => wf_value G'')
                G
                (reflect_expr_beta_iota (var:=var1) reflect_ident_iota1 (t:=t) e1)
                (reflect_expr_beta_iota (var:=var2) reflect_ident_iota2 (t:=t) e2).
          Proof using Type.
            revert G HG'; induction Hwf; cbn [reflect_expr_beta_iota]; intros.
            all: repeat first [ match goal with
                                | [ |- UnderLets.wf _ _ _ _ ] => constructor
                                | [ |- expr.wf _ _ _ ] => constructor
                                | [ |- wf_value' _ (UnderLets.Base _) (UnderLets.Base _) ] => constructor
                                | [ Hwf_reflect_ident_iota : forall G t' idc', option_eq (wf_value G) (?reflect_ident_iota1 t' idc') (?reflect_ident_iota2 t' idc'),
                                      H1 : ?reflect_ident_iota1 ?t ?idc = _, H2 : ?reflect_ident_iota2 ?t ?idc = _ |- _ ]
                                  => let H' := fresh in
                                     pose proof (fun G => Hwf_reflect_ident_iota G t idc) as H';
                                     rewrite H1, H2 in H'; clear H1 H2; cbv [option_eq] in H'
                                | [ H : list _ -> ?T |- _ ] => specialize (H nil)
                                | [ |- UnderLets.wf ?Pv ?Gv (UnderLets.splice _ _) (UnderLets.splice _ _) ]
                                  => apply @UnderLets.wf_splice with (P:=fun G => wf_value G); intros; subst
                                | [ H : context[reflect_expr_beta_iota] |- UnderLets.wf _ _ (reflect_expr_beta_iota _ _) (reflect_expr_beta_iota _ _) ]
                                  => apply H; intros
                                | [ |- wf_value _ (fun x => _) (fun y => _) ] => hnf; intros; subst
                                | [ |- wf_value' _ (splice_under_lets_with_value _ _) (splice_under_lets_with_value _ _) ]
                                  => apply wf_splice_under_lets_with_value
                                | [ |- UnderLets.wf (fun G a1 a2 => wf_value_with_lets G (Base_value a1) (Base_value a2)) ?G' ?x ?y ]
                                  => cut (UnderLets.wf (fun G => wf_value G) G' x y);
                                     [ apply UnderLets.wf_Proper_list_impl; cbv [wf_value_with_lets Base_value]
                                     | ]
                                end
                              | progress destruct_head'_False
                              | progress inversion_option
                              | solve [ auto ]
                              | break_innermost_match_step
                              | apply wf_reflect
                              | apply wf_reify
                              | progress intros
                              | progress cbn [List.In eq_rect fst snd] in *
                              | progress destruct_head'_or
                              | progress inversion_sigma
                              | progress subst
                              | progress inversion_prod
                              | cbn [wf_value wf_value'] in *;
                                handle_wf_rec ltac:(fun tac => try tac (); try eassumption; tac ())
                              | eapply wf_value'_Proper_list; [ | match goal with H : _ |- _ => now eapply H end ]; solve [ destruct_head'_ex; subst; wf_t ]
                              | match goal with
                                | [ H : wf_value _ ?f ?g |- wf_value _ (?f _) (?g _) ]
                                  => eapply wf_value'_Proper_list; revgoals; [ hnf in H; eapply H; revgoals | ]; try eassumption; try reflexivity; now destruct_head'_ex; subst; wf_t
                                end ].
          Qed.

          Lemma wf_reify_expr_beta_iota
                {reflect_ident_iota1 reflect_ident_iota2}
                (Hwf_reflect_ident_iota
                 : forall G {t} (idc : ident t),
                    option_eq
                      (@wf_value _ ident var1 var2 G _)
                      (@reflect_ident_iota1 t idc)
                      (@reflect_ident_iota2 t idc))
                G G'
                (HG' : forall t v1 v2, List.In (existT _ t (v1, v2)) G' -> wf_value G v1 v2)
                {t} e1 e2
                (Hwf : expr.wf G' e1 e2)
            : UnderLets.wf
                (fun G'' => expr.wf G'')
                G
                (reify_expr_beta_iota (var:=var1) reflect_ident_iota1 (t:=t) e1)
                (reify_expr_beta_iota (var:=var2) reflect_ident_iota2 (t:=t) e2).
          Proof using Type.
            cbv [reify_expr_beta_iota reify_to_UnderLets].
            eapply @UnderLets.wf_splice with (P := fun G => wf_value G);
              intros; destruct_head'_ex; subst.
            all: repeat first [ break_innermost_match_step
                              | progress cbn [reflect reify] in *
                              | progress fold (@reflect base ident var1) (@reflect base ident var2)
                              | progress fold (@reify base ident var1) (@reify base ident var2)
                              | progress intros
                              | assumption
                              | apply wf_reify
                              | apply wf_reflect
                              | eapply wf_reflect_expr_beta_iota
                              | match goal with
                                | [ |- List.In ?x ?seg ] => is_evar seg; unify seg (cons x nil); left
                                end
                              | constructor
                              | progress (cbv [wf_value] in *; cbn [wf_value'] in * )
                              | match goal with H : _ |- _ => eapply H; revgoals; clear H end ].
          Qed.

          Lemma wf_expr_value_to_rewrite_rule_replacement_unbundled
                {reflect_ident_iota1 reflect_ident_iota2}
                (Hwf_reflect_ident_iota
                 : forall G {t} (idc : ident t),
                    option_eq
                      (@wf_value _ ident var1 var2 G _)
                      (@reflect_ident_iota1 t idc)
                      (@reflect_ident_iota2 t idc))
                (should_do_again : bool)
                G {t} e1 e2
                (Hwf : @wf_maybe_do_again_expr _ ident var1 var2 t true true G e1 e2)
            : UnderLets.wf
                (fun G' => @wf_maybe_do_again_expr _ ident var1 var2 t should_do_again should_do_again G')
                G
                (@expr_value_to_rewrite_rule_replacement _ ident var1 reflect_ident_iota1 should_do_again t e1)
                (@expr_value_to_rewrite_rule_replacement _ ident var2 reflect_ident_iota2 should_do_again t e2).
          Proof using Type.
            cbv [expr_value_to_rewrite_rule_replacement].
            eapply @UnderLets.wf_splice with (P := @wf_maybe_do_again_expr _ ident var1 var2 _ true true); intros; destruct_head'_ex; subst.
            { destruct Hwf as [G' [HG' Hwf] ].
              eapply UnderLets.wf_flat_map;
                cbv [wf_value] in *;
                eauto using wf_value'_Proper_list, UnderLets.wf_of_expr, wf_reify_expr_beta_iota.
              { intros; eapply wf_reflect; now repeat constructor. } }
            { repeat first [ progress cbv [wf_maybe_do_again_expr] in *
                           | break_innermost_match_step
                           | progress destruct_head'_ex
                           | progress destruct_head'_and
                           | progress subst
                           | eapply wf_reify_expr_beta_iota; try eassumption
                           | constructor
                           | solve [ eauto ] ]. }
          Qed.
        End with_var2.

        Section with_interp.
          Context {buildInterpIdentCorrect : ident.BuildInterpIdentCorrectT ident_interp}
                  {buildInterpEagerIdentCorrect : ident.BuildInterpEagerIdentCorrectT ident_interp}.

          Local Notation var := (type.interp (base.interp base_interp)) (only parsing).
          Local Notation expr := (@expr.expr base_type ident var).
          Local Notation expr_interp := (@expr.interp _ ident _ (@ident_interp)).
          Local Notation expr_interp_related := (@expr.interp_related _ ident _ (@ident_interp)).
          Local Notation UnderLets_interp_related := (@UnderLets.interp_related _ ident _ (@ident_interp) _ _ expr_interp_related).
          Local Notation value_interp_related := (@value_interp_related base ident base_interp (@ident_interp)).

          Local Ltac fin_t :=
            repeat first [ reflexivity
                         | progress intros
                         | progress subst
                         | progress destruct_head'_unit
                         | solve [ eauto ]
                         | match goal with
                           | [ |- expr.interp_related _ (reify_list _) _ ]
                             => rewrite expr.reify_list_interp_related_iff
                           | [ |- ?x = ?y :> Datatypes.unit ] => case x, y; reflexivity
                           | [ |- ?x = Datatypes.tt ] => case x; reflexivity
                           | [ |- Datatypes.tt = ?x ] => case x; reflexivity
                           end
                         | match goal with H : _ |- _ => apply H; clear H end ].

          (** TODO: MOVE ME *)
          Local Ltac specialize_refls H :=
            lazymatch type of H with
            | forall x y : ?T, x = y -> _
              => let H' := fresh in
                 constr:(fun x : T
                         => match H x x eq_refl return _ with
                            | H'
                              => ltac:(let v := specialize_refls H' in
                                       exact v)
                            end)
            | forall x : ?T, _
              => let H' := fresh in
                 constr:(fun x : T
                         => match H x return _ with
                            | H' => ltac:(let v := specialize_refls H' in exact v)
                            end)
            | _ => H
            end.

          Lemma reflect_ident_iota_interp_related {t} (idc : ident t) v1 v2
            : reflect_ident_iota (var:=var) idc = Some v1
              -> ident_interp _ idc == v2
              -> value_interp_related v1 v2.
          Proof using try_make_transport_base_cps_correct buildInvertIdentCorrect buildInterpIdentCorrect buildInterpEagerIdentCorrect.
            cbv [reflect_ident_iota ident.eager_ident_rect].
            generalize (ident.transparent_fromToRestrictedIdent_eq idc).
            destruct (toRestrictedIdent t idc); intro H; cbn in H; inversion_option; subst; cbn;
              [ | discriminate ].
            destruct_head' (@ident.restricted_ident); intro; inversion_option; subst.
            all: repeat
                   first [ progress cbn [ident.fromRestrictedIdent]
                         | progress ident.rewrite_interp_eager ident_interp
                         | progress expr.invert_subst
                         | progress cbn [type.related type.interp base.interp value_interp_related expr.interp_related expr.interp_related_gen reify reflect value'] in *
                         | progress cbv [respectful value] in *
                         | progress intros
                         | progress subst
                         | break_innermost_match_step
                         | progress ident.rewrite_interp ident_interp
                         | progress cbv [ident.literal ident.eagerly] in * ].
            all: cbv [nat_rect_arrow_nodep list_rect_arrow_nodep] in *.
            all: change (@nat_rect_nodep) with (fun P => @nat_rect (fun _ => P)) in *.
            all: change (@list_rect_nodep) with (fun A P => @list_rect A (fun _ => P)) in *.
            all: repeat
                   repeat
                   first [ progress cbn [type.related type.interp base.interp value_interp_related expr.interp_related expr.interp_related_gen reify reflect value'] in *
                         | progress cbv [respectful value] in *
                         | progress intros
                         | progress subst
                         | progress ident.rewrite_interp ident_interp
                         | progress ident.rewrite_interp_eager ident_interp
                         | progress cbv [ident.literal ident.eagerly] in *
                         | match goal with
                           | [ H : List.Forall2 _ ?l1 ?l2, H' : ?R ?v1 ?v2 |- ?R (nth_default ?v1 ?l1 ?x) (nth_default ?v2 ?l2 ?x) ]
                             => apply Forall2_forall_iff''; split; assumption
                           | [ H : context[expr.interp_related _ (reify_list _)] |- _ ]
                             => rewrite expr.reify_list_interp_related_iff in H
                           | [ |- expr.interp_related_gen _ _ (reify_list _) _ ]
                             => rewrite expr.reify_list_interp_related_gen_iff
                           | [ H : context[ident.Thunked.nat_rect _ _ _ _ = ?f _ _ _]
                               |- UnderLets_interp_related (nat_rect _ _ _ _) (?f ?x ?y ?z) ]
                             => erewrite <- H;
                                [ apply UnderLets.nat_rect_interp_related
                                | intros; subst; reflexivity.. ];
                                try solve [ fin_t ]; intros
                           | [ H : context[nat_rect _ _ _ _ _ = ?f _ _ _ _]
                               |- UnderLets_interp_related (nat_rect _ _ _ _ _) (?f ?x ?y ?z ?w) ]
                             => erewrite <- H;
                                [ eapply UnderLets.nat_rect_arrow_interp_related
                                | .. ];
                                try solve [ fin_t ]; intros
                           | [ H : context[ident.Thunked.list_rect _ _ _ _ = ?f _ _ _]
                               |- UnderLets_interp_related (@list_rect ?T (fun _ => ?P) ?N_case _ _) (?f _ _ _) ]
                             => erewrite <- H; cbv [ident.Thunked.list_rect];
                                [ rapply uconstr:(UnderLets.list_rect_interp_related)
                                | .. ]; try solve [ fin_t ]; intros
                           | [ H : context[list_rect _ _ _ _ _ = ?f _ _ _ _]
                               |- UnderLets_interp_related (list_rect _ _ _ _ _) (?f _ _ _ _) ]
                             => erewrite <- H;
                                [ rapply uconstr:(UnderLets.list_rect_arrow_interp_related _)
                                | .. ]; try solve [ fin_t ]; intros
                           | [ H : context[nth_default _ _ _ = ?f _ _ _]
                               |- ?R (nth_default _ _ _) (?f _ _ _) ]
                             => rewrite <- H; clear f H; try solve [ fin_t ]
                           end
                         | rewrite <- UnderLets.to_expr_interp_related_gen_iff
                         | eapply UnderLets.splice_interp_related_of_ex;
                           do 2 eexists; repeat apply conj;
                           [ now eauto | intros | reflexivity ];
                           try solve [ fin_t ]
                         | progress (cbn [UnderLets.interp_related UnderLets.interp_related_gen expr.interp_related expr.interp_related_gen];
                                     repeat (do 2 eexists; repeat apply conj; intros))
                         | solve
                             [ repeat
                                 first
                                 [ progress fin_t
                                 | progress cbn [UnderLets.interp_related UnderLets.interp_related_gen expr.interp_related expr.interp_related_gen type.related]
                                 | progress cbv [respectful]
                                 | progress repeat (do 2 eexists; repeat apply conj; intros) ] ]
                         | match goal with
                           | [ H : context[forall x y, x = y -> _] |- _ ]
                             => let H' := specialize_refls H in
                                specialize H'
                           end ].
            all: match goal with
                 | [ H : forall x x' Hx y y' Hy z z' Hz, UnderLets_interp_related _ (?f _ _ _) |- ?f _ _ _ = ?f _ _ _ ]
                   => etransitivity; [ symmetry | ];
                        apply (fun x x' Hx y y' Hy z z' Hz => UnderLets.eqv_of_interp_related _ (H x x' Hx y y' Hy z z' Hz))
                 | [ H : forall x x' Hx y y' Hy z z' Hz w w' Hw, UnderLets_interp_related _ (?f _ _ _ _) |- ?f _ _ _ _ = ?f _ _ _ _ ]
                   => etransitivity; [ symmetry | ];
                        apply (fun x x' Hx y y' Hy z z' Hz w w' Hw => UnderLets.eqv_of_interp_related _ (H x x' Hx y y' Hy z z' Hz w w' Hw))
                 end.
            all: cbn [type.interp base.interp]; intros.
            all: repeat first [ progress cbn [UnderLets_interp_related UnderLets.interp_related_gen type.related] in *
                              | progress cbv [GallinaReify.Reify_as GallinaReify.reify]
                              | progress subst
                              | match goal with
                                | [ |- expr_interp_related (t:=?T) ?ev ?v ]
                                  => is_evar ev; instantiate (1:= GallinaReify.reify (t:=T) v);
                                     cbn [expr_interp_related expr.interp_related_gen]
                                | [ |- UnderLets_interp_related (?f _) (?g _) ]
                                  => is_evar f;
                                     instantiate (1:=fun e => UnderLets.Base (GallinaReify.reify (t:=type.base _) (g (expr_interp e))))
                                | [ |- expr_interp_related (GallinaReify.base.reify _) _ ]
                                  => apply expr.reify_interp_related
                                | [ H : forall x, ?f x = ?g x |- expr_interp_related _ (?g _) ]
                                  => rewrite <- H
                                | [ H : expr_interp_related _ _ |- _ ] => apply expr.eqv_of_interp_related in H
                                end ].
          Qed.

          Lemma reflect_expr_beta_iota_interp_related
                {reflect_ident_iota}
                (Hreflect_ident_iota
                 : forall t idc v1 v2,
                    reflect_ident_iota t idc = Some v1
                    -> ident_interp _ idc == v2
                    -> value_interp_related v1 v2)
                {t} e v
                (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
            : UnderLets.interp_related
                (@ident_interp) value_interp_related
                (reflect_expr_beta_iota reflect_ident_iota (t:=t) e)
                v.
          Proof using Type.
            revert dependent v; induction e; cbn [reflect_expr_beta_iota]; intros.
            all: repeat first [ assumption
                              | match goal with
                                | [ |- UnderLets.interp_related_gen _ _ _ (UnderLets.splice (reflect_expr_beta_iota _ _) _) _ ]
                                  => eapply UnderLets.splice_interp_related_gen_of_ex;
                                     do 2 eexists; repeat apply conj;
                                     [ match goal with
                                       | [ IH : context[UnderLets.interp_related _ _ (reflect_expr_beta_iota _ _) _] |- _ ]
                                         => eapply IH; eassumption
                                       end
                                     | intros | ]
                                | [ |- UnderLets.interp_related_gen _ _ _ (UnderLets.UnderLet (reify _) _) _ ]
                                  => cbn [UnderLets.interp_related_gen];
                                     do 2 eexists; repeat apply conj;
                                     [ apply reify_interp_related; eassumption
                                     | intros | reflexivity ]
                                | [ |- UnderLets.interp_related _ _ (UnderLets.Base _) _ ]
                                  => cbn [UnderLets.interp_related UnderLets.interp_related_gen]
                                | [ |- value_interp_related (splice_under_lets_with_value _ _) _ ]
                                  => eapply interp_splice_under_lets_with_value_of_ex;
                                     do 2 eexists; repeat apply conj; intros
                                | [ |- value_interp_related (Base_value _) _ ]
                                  => apply interp_Base_value
                                | [ |- value_interp_related (reflect _) _ ] => apply reflect_interp_related
                                end
                              | break_innermost_match_step
                              | solve [ eauto ]
                              | progress cbn [value_interp_related]; intros
                              | progress cbn [expr.interp_related_gen] in *
                              | progress destruct_head'_ex
                              | progress destruct_head'_and
                              | progress subst
                              | progress cbv [UnderLets.interp_related]
                              | solve [ cbn [value_interp_related UnderLets.interp_related_gen] in *; eauto; repeat match goal with H : _ |- _ => eapply H; clear H end ]
                              | reflexivity
                              | match goal with H : _ |- _ => apply H; clear H end ].
          Qed.

          Lemma reify_expr_beta_iota_interp_related
                {reflect_ident_iota}
                (Hreflect_ident_iota
                 : forall t idc v1 v2,
                    reflect_ident_iota t idc = Some v1
                    -> ident_interp _ idc == v2
                    -> value_interp_related v1 v2)
                {t} e v
                (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
            : UnderLets_interp_related
                (reify_expr_beta_iota reflect_ident_iota (t:=t) e)
                v.
          Proof using Type.
            cbv [reify_expr_beta_iota reify_to_UnderLets].
            eapply UnderLets.splice_interp_related_of_ex; do 2 eexists; repeat apply conj;
              [ eapply reflect_expr_beta_iota_interp_related; eauto | | instantiate (1:=fun x => x); reflexivity ]; cbv beta.
            intros; break_innermost_match; cbn [UnderLets.interp_related UnderLets.interp_related_gen value_interp_related] in *; try eassumption.
            apply reify_interp_related; eauto.
          Qed.

          Lemma expr_value_to_rewrite_rule_replacement_interp_related_unbundled
                {reflect_ident_iota}
                (Hreflect_ident_iota
                 : forall t idc v1 v2,
                    reflect_ident_iota t idc = Some v1
                    -> ident_interp _ idc == v2
                    -> value_interp_related v1 v2)
                (should_do_again : bool)
                {t} e v
                (He : expr.interp_related_gen (@ident_interp) (fun t => value_interp_related) e v)
            : UnderLets.interp_related
                (@ident_interp) (if should_do_again
                                    return (@expr.expr base_type ident (if should_do_again then @value _ ident var else var) t) -> type.interp (base.interp base_interp) t -> Prop
                                 then expr.interp_related_gen (@ident_interp) (fun t => value_interp_related)
                                 else expr_interp_related)
                (@expr_value_to_rewrite_rule_replacement _ ident var reflect_ident_iota should_do_again t e)
                v.
          Proof using Type.
            cbv [expr_value_to_rewrite_rule_replacement].
            apply UnderLets.splice_interp_related_of_ex
              with (RA:=expr.interp_related_gen (@ident_interp) (fun t => value_interp_related));
              do 2 eexists; repeat apply conj; intros; [ | | instantiate (2:=fun x => x); reflexivity ]; cbv beta.
            { apply UnderLets.flat_map_interp_related_iff with (R'':=fun t => value_interp_related);
                [ intros; now apply reify_expr_beta_iota_interp_related
                | intros; apply reflect_interp_related; cbn; assumption
                | now rewrite UnderLets.of_expr_interp_related_gen_iff ]. }
            { break_innermost_match; cbn [UnderLets.interp_related UnderLets.interp_related_gen];
                now try apply reify_expr_beta_iota_interp_related. }
          Qed.
        End with_interp.
      End with_base.

      Section with_classes.
        Import Compilers.Classes.
        Context {exprInfo : ExprInfoT}
                {exprExtraInfo : ExprExtraInfoT}.
        Local Notation base_type := (base.type base).
        Local Notation type := (type.type base_type).

        Section with_var2.
          Context {var1 var2 : type -> Type}.

          Lemma wf_expr_value_to_rewrite_rule_replacement
                (should_do_again : bool)
                G {t} e1 e2
                (Hwf : @wf_maybe_do_again_expr _ ident var1 var2 t true true G e1 e2)
            : UnderLets.wf
                (fun G' => @wf_maybe_do_again_expr _ ident var1 var2 t should_do_again should_do_again G')
                G
                (@expr_value_to_rewrite_rule_replacement _ ident var1 (fun t => reflect_ident_iota (var:=var1)) should_do_again t e1)
                (@expr_value_to_rewrite_rule_replacement _ ident var2 (fun t => reflect_ident_iota (var:=var2)) should_do_again t e2).
          Proof using Type.
            apply wf_expr_value_to_rewrite_rule_replacement_unbundled; [ | assumption ].
            intros; apply wf_reflect_ident_iota.
          Qed.
        End with_var2.

        Section with_interp.
          Local Notation var := (type.interp (base.interp base_interp)) (only parsing).

          Lemma expr_value_to_rewrite_rule_replacement_interp_related
                (should_do_again : bool)
                {t} e v
                (He : expr.interp_related_gen ident_interp (fun t => value_interp_related ident_interp) e v)
            : UnderLets.interp_related
                ident_interp
                (if should_do_again
                    return (@expr.expr base_type ident (if should_do_again then @value _ ident var else var) t) -> type.interp (base.interp base_interp) t -> Prop
                 then expr.interp_related_gen ident_interp (fun t => value_interp_related ident_interp)
                 else expr.interp_related ident_interp)
                (@expr_value_to_rewrite_rule_replacement _ ident var (fun t => reflect_ident_iota) should_do_again t e)
                v.
          Proof using Type.
            apply expr_value_to_rewrite_rule_replacement_interp_related_unbundled; [ | assumption ].
            intros; eapply @reflect_ident_iota_interp_related; try eassumption; typeclasses eauto.
          Qed.
        End with_interp.
      End with_classes.
    End Reify.

    Module Import WfTactics.
      Module Export GoalType.
        Import pattern.ident.GoalType.
        Import Compilers.Classes.

        Definition Wf_GoalT {exprInfo : ExprInfoT} {exprExtraInfo : ExprExtraInfoT} {pkg : package} (Rewriter : RewriterT) : Prop
          := forall var1 var2,
            @Compile.rewrite_rules_goodT
              base _ ident pattern_ident arg_types var1 var2
              (Make.GoalType.rewrite_rules (Rewriter_data Rewriter) _)
              (Make.GoalType.rewrite_rules (Rewriter_data Rewriter) _).
      End GoalType.
    End WfTactics.

    Module InterpTactics.
      Import Crypto.Util.ZRange.

      Module Export GoalType.
        Import pattern.ident.GoalType.
        Import Compilers.Classes.
        Local Notation specT rewriter_data
          := (PrimitiveHList.hlist (@snd bool Prop) (List.skipn (dummy_count rewriter_data) (rewrite_rules_specs rewriter_data)))
               (only parsing).

        Local Notation "'plet' x := y 'in' z"
          := (match y return _ with x => z end).

        Definition Interp_GoalT {exprInfo : ExprInfoT} {exprExtraInfo : ExprExtraInfoT} {pkg : package} (Rewriter : RewriterT) : Prop
          := plet data := Rewriter_data Rewriter in
                   specT data
                   -> @Compile.rewrite_rules_interp_goodT
                        base _ ident pattern_ident arg_types to_typed base_interp ident_interp
                        (Make.GoalType.rewrite_rules data _).
      End GoalType.
    End InterpTactics.

    Module GoalType.
      Import Compilers.Basic.GoalType.
      Import Compilers.Classes.

      Record VerifiedRewriter :=
        {
          exprInfo : ExprInfoT;
          exprReifyInfo : ExprReifyInfoT;

          Rewrite : forall {t} (e : expr.Expr (ident:=ident) t), expr.Expr (ident:=ident) t;
          Wf_Rewrite : forall {t} e (Hwf : Wf e), Wf (@Rewrite t e);
          Interp_Rewrite {t} e
          : forall (Hwf : Wf e), expr.Interp ident_interp (@Rewrite t e) == expr.Interp ident_interp e;

          check_wf : forall {t}, expr.Expr (ident:=ident) t -> bool;
          generalize_for_wf : forall {t}, expr.Expr (ident:=ident) t -> expr.Expr (ident:=ident) t;
          prove_Wf : forall {t} (e : expr.Expr (ident:=ident) t), (e = generalize_for_wf e /\ check_wf e = true) -> expr.Wf e;
        }.

      Definition VerifiedRewriter_with_args
                 (basic_package : Basic.GoalType.package)
                 {base ident pkg} (pkg_proofs : @pattern.ProofGoalType.package_proofs base ident pkg)
                 (include_interp : bool)
                 {rewrite_rulesT} (rules_proofs : PrimitiveHList.hlist (@snd bool Prop) rewrite_rulesT)
        := VerifiedRewriter.

      Definition VerifiedRewriter_with_ind_args
                 (scraped_data : ScrapedData.t)
                 (var_like_idents : GallinaIdentList.t)
                 (base : Type)
                 (ident : type.type (base.type base) -> Type)
                 (raw_ident : Type)
                 (pattern_ident : type.type (pattern.base.type base) -> Type)
                 (include_interp : bool)
                 {rewrite_rulesT} (rules_proofs : PrimitiveHList.hlist (@snd bool Prop) rewrite_rulesT)
        := VerifiedRewriter.
    End GoalType.
  End RewriteRules.
End Compilers.
