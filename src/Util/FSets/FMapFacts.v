Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.
Require Import Coq.Classes.RelationPairs.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.Tactics.InHypUnderBindersDo.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.

Local Set Keyed Unification.


Module Type WFacts_funT (E:DecidableTypeOrig)(M:WSfun E) := Nop <+ WFacts_fun E M.
Module WFacts_fun_RemoveHints (E:DecidableTypeOrig)(M:WSfun E) (F : WFacts_funT E M).
  Global Remove Hints
         F.Empty_m_Proper
         F.EqualSetoid
         F.EqualSetoid_Reflexive
         F.EqualSetoid_Symmetric
         F.EqualSetoid_Transitive
         F.EqualSetoid_relation
         F.In_m_Proper
         F.KeySetoid
         F.KeySetoid_Reflexive
         F.KeySetoid_Symmetric
         F.KeySetoid_Transitive
         F.KeySetoid_relation
         F.MapsTo_m_Proper
         F.add_m_Proper
         F.find_m_Proper
         F.is_empty_m_Proper
         F.map_m_Proper
         F.mem_m_Proper
         F.remove_m_Proper
    : typeclass_instances.
End WFacts_fun_RemoveHints.
Module WFacts_RemoveHints (M:WS) (F:WFacts_funT M.E M) := WFacts_fun_RemoveHints M.E M F.
Module Facts_RemoveHints := WFacts_RemoveHints.

Module Type WProperties_funT (E:DecidableTypeOrig)(M:WSfun E) := Nop <+ WProperties_fun E M.
Module WProperties_fun_RemoveHints (E:DecidableTypeOrig)(M:WSfun E) (F : WProperties_funT E M).
  Include WFacts_fun_RemoveHints E M F.F.
  Global Remove Hints
         F.Disjoint_m_Proper
         F.Partition_m_Proper
         F.cardinal_m_Proper
         F.diff_m_Proper
         F.restrict_m_Proper
         F.update_m_Proper
    : typeclass_instances.
End WProperties_fun_RemoveHints.
Module WProperties_RemoveHints (M:WS) (F:WProperties_funT M.E M) := WProperties_fun_RemoveHints M.E M F.
Module Properties_RemoveHints := WProperties_RemoveHints.

Module Type OrdPropertiesT (M:S) := Nop <+ OrdProperties M.
Module OrdProperties_RemoveHints (M:S) (P:OrdPropertiesT M).
  Include OrderedTypeOrigFacts_RemoveHints M.E P.ME.
  Include KeyOrderedType_RemoveHints M.E P.O.
  Include Properties_RemoveHints M P.P.
End OrdProperties_RemoveHints.


Local Ltac t_destr_conj_step :=
  first [ progress subst
        | progress destruct_head'_False
        | progress destruct_head'_and
        | progress destruct_head'_ex
        | progress destruct_head'_True
        | progress destruct_head'_unit
        | progress destruct_head' sig
        | progress inversion_option
        | progress inversion_sigma
        | progress inversion_pair
        | progress cbn [fst snd proj1_sig proj2_sig] in *
        | match goal with
          | [ H : _ :: _ = nil |- _ ] => inversion H
          | [ H : nil = _ :: _ |- _ ] => inversion H
          | [ H : nil = nil |- _ ] => clear H
          | [ H : _ :: _ = _ :: _ |- _ ] => inversion H; clear H
          | [ H : eqlistA _ nil _ |- _ ] => inversion H; clear H
          | [ H : eqlistA _ _ nil |- _ ] => inversion H; clear H
          | [ H : eqlistA _ (_ :: _) _ |- _ ] => inversion H; clear H
          | [ H : eqlistA _ _ (_ :: _) |- _ ] => inversion H; clear H
          | [ H : InA _ _ (_ :: _) |- _ ] => inversion H; clear H
          | [ H : InA _ _ nil |- _ ] => inversion H; clear H
          | [ H : List.In _ (List.map _ _) |- _ ] => rewrite in_map_iff in H
          | [ H : List.In _ (List.flat_map _ _) |- _ ] => rewrite in_flat_map in H
          | [ H : ?x = ?x |- _ ] => clear H
          | [ H : ?T, H' : ?T |- _ ] => clear H
          | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
          | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
          | [ H : Some _ = ?x |- _ ] => symmetry in H
          | [ H : None = ?x |- _ ] => symmetry in H
          end
        | discriminate ].

Local Ltac t_destr_step :=
  first [ t_destr_conj_step
        | progress destruct_head'_or
        | progress destruct_head' option
        | break_innermost_match_hyps_step
        | break_innermost_match_step ].


Module WAdditionalFacts_fun (E:DecidableTypeOrig)(Import M:WSfun E).
  Module Import _WAdditionalFacts_fun.
    Module WFacts := WFacts_fun E M <+ WFacts_fun_RemoveHints E M.
    Module WProperties := WProperties_fun E M <+ WProperties_fun_RemoveHints E M.
  End _WAdditionalFacts_fun.
  Import _WAdditionalFacts_fun.WFacts.
  Import _WAdditionalFacts_fun.WProperties.
  Local Existing Instances
        Empty_m_Proper
        EqualSetoid
        EqualSetoid_Reflexive
        EqualSetoid_Symmetric
        EqualSetoid_Transitive
        EqualSetoid_relation
        In_m_Proper
        KeySetoid
        KeySetoid_Reflexive
        KeySetoid_Symmetric
        KeySetoid_Transitive
        KeySetoid_relation
        MapsTo_m_Proper
        add_m_Proper
        find_m_Proper
        is_empty_m_Proper
        map_m_Proper
        mem_m_Proper
        remove_m_Proper
  .

  Local Instance Proper_eq_key_elt_iff elt
    : Proper (eq ==> RelationPairs.RelProd E.eq eq ==> iff) (@M.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_elt_impl elt
    : Proper (eq ==> RelationPairs.RelProd E.eq eq ==> impl) (@M.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_elt_flip_impl elt
    : Proper (eq ==> RelationPairs.RelProd E.eq eq ==> flip impl) (@M.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_elt_iff' elt
    : Proper (@M.eq_key_elt elt ==> @M.eq_key_elt elt ==> iff) (@M.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_elt_impl' elt
    : Proper (@M.eq_key_elt elt ==> @M.eq_key_elt elt ==> impl) (@M.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_elt_flip_impl' elt
    : Proper (@M.eq_key_elt elt ==> @M.eq_key_elt elt ==> flip impl) (@M.eq_key_elt elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_iff elt
    : Proper (@M.eq_key elt ==> @M.eq_key elt ==> iff) (@M.eq_key elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_impl elt
    : Proper (@M.eq_key elt ==> @M.eq_key elt ==> impl) (@M.eq_key elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Proper_eq_key_flip_impl elt
    : Proper (@M.eq_key elt ==> @M.eq_key elt ==> flip impl) (@M.eq_key elt).
  Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

  Local Instance Equal_Equivalence elt : Equivalence (@M.Equal elt) | 10.
  Proof. split; cbv; firstorder eauto using eq_trans. Qed.

  Global Hint Extern 1 (ProperProxy (@M.Equal _) _) => apply reflexive_proper_proxy : typeclass_instances.

  Local Ltac t_Proper_helper :=
    cbv [M.Equal M.In Proper respectful option_eq];
    repeat first [ progress intros
                 | progress subst
                 | progress destruct_head'_ex
                 | congruence
                 | reflexivity
                 | eassumption
                 | progress break_innermost_match_hyps
                 | progress break_innermost_match
                 | apply M.find_2
                 | match goal with
                   | [ |- M.find ?x ?y = M.find ?x' ?y' ]
                     => destruct (M.find x y) eqn:?, (M.find x' y') eqn:?
                   | [ H : E.eq ?x ?y |- _ ]
                     => (idtac + symmetry in H); eapply M.MapsTo_1 in H; [ | apply M.find_2; eassumption ]
                   | [ H : _ |- _ ] => apply M.find_1 in H
                   | [ |- Some _ = None ] => exfalso
                   | [ |- ?x = None ] => destruct x eqn:?
                   | [ |- _ <-> _ ] => split
                   | [ H : M.find ?k ?m = Some ?v, H' : forall k', M.find k' ?m = M.find k' ?m' |- _ ]
                     => unique assert (M.find k m' = Some v) by now rewrite <- H
                   | [ H : M.find ?k ?m' = Some ?v, H' : forall k', M.find k' ?m = M.find k' ?m' |- _ ]
                     => unique assert (M.find k m = Some v) by now rewrite <- H
                   end
                 | eexists ].

  Local Instance find_Proper_eq elt : Proper (E.eq ==> @M.Equal _ ==> eq) (@M.find elt) | 10.
  Proof. t_Proper_helper. Qed.

  Local Instance MapsTo_Proper_eq_iff elt : Proper (E.eq ==> eq ==> @M.Equal _ ==> iff) (@M.MapsTo elt) | 10.
  Proof. t_Proper_helper. Qed.

  Local Instance In_compat elt : Proper (E.eq ==> @M.Equal _ ==> iff) (@M.In elt) | 10.
  Proof. t_Proper_helper. Qed.

  Local Instance eq_key_equiv elt : Equivalence (@eq_key elt) | 10.
  Proof.
    split; cbv; intros; break_innermost_match; break_innermost_match_hyps; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
  Qed.
  Local Instance eq_key_elt_equiv elt : Equivalence (@eq_key_elt elt) | 10.
  Proof.
    split; cbv; intros; break_innermost_match; break_innermost_match_hyps; destruct_head'_and; split; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
  Qed.

  Lemma find_empty elt x : M.find x (@M.empty elt) = None.
  Proof.
    pose proof (@M.empty_1 elt x) as H.
    cbv in H; setoid_rewrite find_mapsto_iff in H.
    destruct M.find; intuition congruence.
  Qed.

  Local Ltac Proper_equiv_t :=
    cbv; setoid_rewrite find_mapsto_iff;
    repeat split; intros; subst; split_and; eauto.

  Local Instance Proper_Equiv_eq_impl elt
    : Proper ((eq ==> eq ==> impl) ==> eq ==> eq ==> impl) (@M.Equiv elt) | 10.
  Proof. Proper_equiv_t. Qed.
  Local Instance Proper_Equiv_eq_flip_impl elt
    : Proper ((eq ==> eq ==> flip impl) ==> eq ==> eq ==> flip impl) (@M.Equiv elt) | 10.
  Proof. Proper_equiv_t. Qed.
  Local Instance Proper_Equiv_eq_iff elt
    : Proper ((eq ==> eq ==> iff) ==> eq ==> eq ==> iff) (@M.Equiv elt) | 10.
  Proof. Proper_equiv_t. Qed.
  Local Instance Proper_Equiv_eq_impl_pointwise elt
    : Proper (pointwise_relation _ (pointwise_relation _ impl) ==> eq ==> eq ==> impl) (@M.Equiv elt) | 10.
  Proof. Proper_equiv_t. Qed.
  Local Instance Proper_Equiv_eq_flip_impl_pointwise elt
    : Proper (pointwise_relation _ (pointwise_relation _ (flip impl)) ==> eq ==> eq ==> flip impl) (@M.Equiv elt) | 10.
  Proof. Proper_equiv_t. Qed.
  Local Instance Proper_Equiv_eq_iff_pointwise elt
    : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff) (@M.Equiv elt) | 10.
  Proof. Proper_equiv_t. Qed.

  Definition empty_1' elt : forall x y z, False := @M.empty_1 elt.

  Local Ltac t_full_step :=
    first [ t_destr_step
          | progress cbv [M.In not option_map] in *
          | progress intros
          | match goal with
            | [ H : context[M.MapsTo] |- _ ] => setoid_rewrite find_mapsto_iff in H
            | [ |- context[M.MapsTo] ] => setoid_rewrite find_mapsto_iff
            end
          | progress specialize_under_binders_by eapply ex_intro
          | progress specialize_under_binders_by eassumption
          | progress specialize_under_binders_by reflexivity
          | exfalso; assumption
          | progress inversion_option
          | progress subst
          | reflexivity
          | break_innermost_match_step
          | match goal with
            | [ |- context[M.find ?x ?y] ] => destruct (M.find x y) eqn:?
            end ].


  Lemma mapi_o_ex : forall (elt elt':Type)(m: M.t elt)(x:M.key)(f:M.key->elt->elt'), exists y, E.eq y x /\ M.find x (M.mapi f m) = option_map (f y) (M.find x m).
  Proof.
    pose proof M.mapi_1 as H.
    pose proof M.mapi_2 as H'.
    repeat t_full_step.
    all: match goal with
         | [ H : M.find _ (M.mapi _ _) = _ |- _ ]
           => in_hyp_under_binders_do (fun H' => rewrite H in H')
         end.
    all: repeat t_full_step; eauto.
  Qed.

  Lemma mapi_o_ex_impl (elt elt':Type)(m: M.t elt)(f:M.key->elt->elt')(P:_->Prop)
    : (forall x e, M.find x (M.mapi f m) = Some e -> P e)
      -> (forall x, exists y, E.eq y x /\ forall e, option_map (f y) (M.find x m) = Some e -> P e).
  Proof.
    intros H x.
    specialize (H x).
    destruct (@mapi_o_ex _ _ m x f) as [? [H0 H1]].
    eexists; split; [ eassumption | ].
    specialize_under_binders_by rewrite H1.
    intuition congruence.
  Qed.

  Lemma map2_o
    : forall (elt elt' elt'':Type)(m: M.t elt)(m': M.t elt')
	     (x:M.key)(f:option elt->option elt'->option elt''),
      M.find x (M.map2 f m m') = match M.find x m, M.find x m' with
                                 | None, None => None
                                 | x, y => f x y
                                 end.
  Proof.
    intros *.
    pose proof (@M.map2_1 elt elt' elt'' m m' x f) as H.
    pose proof (@M.map2_2 elt elt' elt'' m m' x f) as H'.
    cbv [M.In] in *.
    setoid_rewrite find_mapsto_iff in H.
    setoid_rewrite find_mapsto_iff in H'.
    specialize_under_binders_by eapply ex_intro.
    destruct (M.find x (M.map2 f m m')); break_innermost_match; try reflexivity;
      specialize_by eauto; specialize_under_binders_by reflexivity; eauto.
    firstorder congruence.
  Qed.

  Lemma forall_In_elements_iff elt (P : _ -> Prop) (m : M.t elt)
        (P_Proper : Proper (@M.eq_key_elt _ ==> Basics.flip impl) P)
    : (forall i, List.In i (M.elements m) -> P i)
      <-> (forall k v, M.find k m = Some v -> P (k, v)).
  Proof.
    setoid_rewrite <- find_mapsto_iff.
    setoid_rewrite elements_mapsto_iff.
    setoid_rewrite InA_alt.
    split; intros; destruct_head' prod; repeat t_destr_step; firstorder eauto.
  Qed.
  Lemma forall_In_elements_snd_iff elt (P : _ -> Prop) (m : M.t elt)
    : (forall i, List.In i (M.elements m) -> P (snd i))
      <-> (forall k v, M.find k m = Some v -> P v).
  Proof.
    rewrite forall_In_elements_iff; [ reflexivity | ].
    cbv; repeat intro; repeat t_destr_step; assumption.
  Qed.

  Lemma fold_remove elt A (eqA : relation A)
        {EqvA : Equivalence eqA}
        (f : key -> elt -> A -> A)
        {f_Proper : Proper (E.eq ==> eq ==> eqA ==> eqA) f}
        (Hf : transpose_neqkey eqA f)
        (m : t elt) k e i
        (Hk : find k m = Some e)
    : eqA (fold f m i) (f k e (fold f (remove k m) i)).
  Proof.
    apply fold_Add; try assumption.
    { cbv [In]; setoid_rewrite find_mapsto_iff.
      setoid_rewrite remove_o; break_innermost_match; firstorder (try congruence; auto). }
    { cbv [Add]; intro.
      rewrite add_o, remove_o; break_innermost_match; setoid_subst_rel E.eq; auto. }
  Qed.

  Lemma fold_add_remove elt A (eqA : relation A)
        {EqvA : Equivalence eqA}
        (f : key -> elt -> A -> A)
        {f_Proper : Proper (E.eq ==> eq ==> eqA ==> eqA) f}
        (Hf : transpose_neqkey eqA f)
        (m : t elt) k e i
    : eqA (fold f (add k e m) i) (f k e (fold f (remove k m) i)).
  Proof.
    apply fold_Add; try assumption.
    { cbv [In]; setoid_rewrite find_mapsto_iff.
      setoid_rewrite remove_o; break_innermost_match; firstorder (try congruence; auto). }
    { cbv [Add]; intro.
      rewrite !add_o, remove_o; break_innermost_match; reflexivity. }
  Qed.

  Lemma cardinal_add elt (m : t elt) k v
    : cardinal (add k v m) = if mem k m then cardinal m else S (cardinal m).
  Proof.
    rewrite !cardinal_fold.
    break_innermost_match; rewrite <- ?not_mem_in_iff, ?mem_find_b in *.
    all: try rewrite fold_add by (try exact _; eauto; repeat intro; subst; reflexivity).
    all: try rewrite fold_add_remove by (try exact _; repeat intro; subst; reflexivity).
    all: try reflexivity.
    all: break_innermost_match_hyps; try congruence.
    { symmetry; eapply fold_remove with (f:=fun _ _ => S); repeat split; repeat intro; try eassumption; subst; reflexivity. }
  Qed.
End WAdditionalFacts_fun.

Module WAdditionalFacts (M:WS) := WAdditionalFacts_fun M.E M.

Module OrdAdditionalFacts_fun (E:OrderedTypeOrig)(Import M:Sfun E).
  Global Instance lt_key_Transitive elt : Transitive (@lt_key elt) | 10.
  Proof. cbv; intros *; eapply E.lt_trans. Qed.
End OrdAdditionalFacts_fun.

Module OrdAdditionalFacts (M:S) := OrdAdditionalFacts_fun M.E M.
Module AdditionalFacts (M:S) := WAdditionalFacts M <+ OrdAdditionalFacts M.
