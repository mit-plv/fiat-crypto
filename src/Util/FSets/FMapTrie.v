(* Finite map library.  *)

(** * FMapTrie *)

(** This module implements tries.
    It follows the implementation from Coq's clib, to some extent.
*)
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Structures.Orders.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.FSets.FMapInterface.
Require Import Coq.Classes.RelationPairs.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ListUtil.SetoidList.
Require Import Crypto.Util.ListUtil.SetoidListFlatMap.
Require Import Crypto.Util.ListUtil.StdlibCompat.
Require Import Crypto.Util.Compose.
Require Import Crypto.Util.Logic.Forall.
Require Import Crypto.Util.Logic.Exists.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Relations.
Require Import Crypto.Util.Structures.Equalities.
Require Import Crypto.Util.Structures.Equalities.List.
Require Import Crypto.Util.Structures.Orders.
Require Import Crypto.Util.Structures.Orders.List.
Require Import Crypto.Util.FSets.FMapInterface.
Require Import Crypto.Util.Sorting.Sorted.Proper.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SetEvars.
Require Import Crypto.Util.Tactics.SubstEvars.
Require Import Crypto.Util.Tactics.SpecializeAllWays.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.Tactics.InHypUnderBindersDo.
Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.FSets.FMapTrie.Shape.
Import TrieTactics.
Import EverythingGen.

Local Set Implicit Arguments.
Local Set Primitive Projections.
Local Unset Strict Implicit.
(* TODO: move to global settings *)
Local Set Keyed Unification.
Import ListNotations.
Local Open Scope option_scope.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope type_scope.
Local Open Scope list_scope.

Module ListWSfun_gen (Y : DecidableTypeOrig) (M : WSfun Y) (Import T : Trie Y M).
  Module Type ESig := ListTyp Y <+ HasEq <+ IsEqOrig <+ HasEqDec.
  Module Type ESigCompat (E : ESig).
    Axiom eq_alt : forall x y, E.eq x y <-> eqlistA Y.eq x y.
  End ESigCompat.
  Module Y' <: DecidableTypeBoth := Y <+ UpdateEq.
  Global Remove Hints Y'.eq_refl Y'.eq_sym Y'.eq_trans : core.
  Module ListWSfun_gen (E : ESig) (ECompat : ESigCompat E) <: WSfun E.
    Module E' <: DecidableTypeBoth := E <+ UpdateEq <+ ECompat.
    Global Remove Hints E'.eq_refl E'.eq_sym E'.eq_trans : core.
    Local Hint Resolve Y'.eq_refl Y'.eq_sym Y'.eq_trans
          E'.eq_refl E'.eq_sym E'.eq_trans
      : core.
    Local Instance M_eq_key_equiv elt : Equivalence (@M.eq_key elt) | 10. split; cbv; eauto. Qed.
    Local Instance M_eq_key_elt_equiv elt : Equivalence (@M.eq_key_elt elt) | 10. split; repeat intros [? ?]; cbv in *; subst; eauto. Qed.

    Definition key := E.t.

    Global Hint Transparent key : core.

    Notation t' elt := (option (T.t elt)).
    Notation t'_P m := (True -> match m with None => True | Some m' => recursively_non_empty m' = true end) (only parsing).
    Notation mk m pf := (exist (fun m' => t'_P m') m (fun 'I => pf)).
    Definition t elt := { m : t' elt | t'_P m }.

    Local Ltac t_obgl :=
      repeat first [ progress intros
                   | progress cbv [M.Empty Option.value not option_map] in *
                   | reflexivity
                   | congruence
                   | t_destr_step
                   | match goal with
                     | [ H := _ |- _ ] => subst H
                     | [ H : forall a e, M.MapsTo _ _ (M.add _ _ _) -> False |- _ ]
                       => specialize (H _ _ ltac:(eapply M.add_1; reflexivity))
                     | [ H : context[M.is_empty] |- _ ]
                       => rewrite M.is_empty_1 in H by assumption
                     | [ H : forall a e, M.MapsTo a e (M.mapi ?f ?m) -> False |- _ ]
                       => assert (forall a e, M.MapsTo a e m -> False)
                         by (let H' := fresh in
                             intros ? ? H'; eapply M.mapi_1 in H'; destruct H' as [?[? H']];
                             eapply H, H');
                          clear H
                     | [ H : forall k e, _ = _ -> M.In _ _ \/ M.In _ _ -> False |- _ ]
                       => pose proof (fun k e pf pf' => H k e (pf pf') (or_introl pf'));
                          pose proof (fun k e pf pf' => H k e (pf pf') (or_intror pf'));
                          clear H
                     end
                   | progress subst
                   | progress specialize_under_binders_by eapply M.map_1
                   | progress break_innermost_match_hyps
                   | progress specialize_under_binders_by (match goal with |- M.MapsTo _ _ (M.map2 _ _ _) => idtac end;
                                                           eapply M.find_2;
                                                           rewrite M.map2_1) ].

    Local Ltac pose_MapsTo_as_find lem :=
      let H := fresh in
      first [ pose proof M.find_1 as H;
              guarded_specialize_hyp_under_binders_by guard_nondep H ltac:(eapply lem; try eapply M.find_2)
            | pose proof lem as H;
              guarded_specialize_hyp_under_binders_by guard_nondep H ltac:(eapply M.find_2) ].

    Global Instance fold_ext {elt A}
      : Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq))) ==> eq ==> eq ==> eq)
               (fold (elt:=elt) (A:=A))
    | 10.
    Proof.
      intros f g Hfg ? m -> ? x ->; revert x.
      cbv in Hfg.
      revert f g Hfg.
      induction m as [d m pf IH] using (t_ind (elt:=elt)); intros.
      repeat (autounfold with trie_db; autorewrite with trie_db).
      clear pf.
      break_innermost_match_hyps; try now break_innermost_match; eauto.
      rewrite !M.fold_1.
      erewrite fold_left_ext_in; [ f_equal; try reflexivity; break_innermost_match; eauto | ].
      intros.
      pose_MapsTo_as_find M.elements_2.
      specialize_under_binders_by (rewrite InA_alt; eexists; split; try eassumption; repeat split; try apply Y.eq_refl).
      eapply IH; [ | intros; apply Hfg ]; eassumption.
    Qed.
    Global Instance fold_Proper_eq {elt A}
      : Proper ((eq ==> eq ==> eq ==> eq) ==> eq ==> eq ==> eq)
               (fold (elt:=elt) (A:=A))
    | 10.
    Proof.
      intros f g Hfg; repeat intro; eapply fold_ext; cbv in *; eauto.
    Qed.

    Hint Extern 1 (ProperProxy (@M.Equal _) _) => apply reflexive_proper_proxy : typeclass_instances.


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
                     | [ H : Y.eq ?x ?y |- _ ]
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

    Local Instance M_find_Proper_eq elt : Proper (Y.eq ==> @M.Equal _ ==> eq) (@M.find elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance M_MapsTo_Proper_eq_iff elt : Proper (Y.eq ==> eq ==> @M.Equal _ ==> iff) (@M.MapsTo elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance M_In_compat elt : Proper (Y.eq ==> @M.Equal _ ==> iff) (@M.In elt) | 10.
    Proof. t_Proper_helper. Qed.

    Local Instance Proper_M_eq_key_elt_iff elt
      : Proper (eq ==> RelationPairs.RelProd Y.eq eq ==> iff) (@M.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_elt_impl elt
      : Proper (eq ==> RelationPairs.RelProd Y.eq eq ==> impl) (@M.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_elt_flip_impl elt
      : Proper (eq ==> RelationPairs.RelProd Y.eq eq ==> flip impl) (@M.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_elt_iff' elt
      : Proper (@M.eq_key_elt elt ==> @M.eq_key_elt elt ==> iff) (@M.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_elt_impl' elt
      : Proper (@M.eq_key_elt elt ==> @M.eq_key_elt elt ==> impl) (@M.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_elt_flip_impl' elt
      : Proper (@M.eq_key_elt elt ==> @M.eq_key_elt elt ==> flip impl) (@M.eq_key_elt elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_iff elt
      : Proper (@M.eq_key elt ==> @M.eq_key elt ==> iff) (@M.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_impl elt
      : Proper (@M.eq_key elt ==> @M.eq_key elt ==> impl) (@M.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance Proper_M_eq_key_flip_impl elt
      : Proper (@M.eq_key elt ==> @M.eq_key elt ==> flip impl) (@M.eq_key elt).
    Proof. cbv; repeat intro; subst; destruct_head'_prod; destruct_head'_and; subst; firstorder (subst; eauto). Qed.

    Local Instance M_Equal_Equivalence elt : Equivalence (@M.Equal elt) | 10.
    Proof. split; cbv; firstorder eauto using eq_trans. Qed.

    Lemma M_is_empty_iff elt (m : M.t elt) : M.is_empty m = true <-> M.Empty m.
    Proof. split; first [ apply M.is_empty_1 | apply M.is_empty_2 ]. Qed.
    Lemma M_find_iff elt m x e : @M.MapsTo elt x e m <-> M.find x m = Some e.
    Proof. split; first [ apply M.find_1 | apply M.find_2 ]. Qed.
    Lemma M_find_empty elt x : M.find x (@M.empty elt) = None.
    Proof.
      pose proof (@M.empty_1 elt x) as H.
      cbv in H; setoid_rewrite M_find_iff in H.
      destruct M.find; intuition congruence.
    Qed.

    Local Ltac Proper_equiv_t :=
      cbv;
      setoid_rewrite M_find_iff;
      repeat split; intros; subst; split_and; eauto.

    Local Instance Proper_M_Equiv_eq_impl elt
      : Proper ((eq ==> eq ==> impl) ==> eq ==> eq ==> impl) (@M.Equiv elt) | 10.
    Proof. Proper_equiv_t. Qed.
    Local Instance Proper_M_Equiv_eq_flip_impl elt
      : Proper ((eq ==> eq ==> flip impl) ==> eq ==> eq ==> flip impl) (@M.Equiv elt) | 10.
    Proof. Proper_equiv_t. Qed.
    Local Instance Proper_M_Equiv_eq_iff elt
      : Proper ((eq ==> eq ==> iff) ==> eq ==> eq ==> iff) (@M.Equiv elt) | 10.
    Proof. Proper_equiv_t. Qed.
    Local Instance Proper_M_Equiv_eq_impl_pointwise elt
      : Proper (pointwise_relation _ (pointwise_relation _ impl) ==> eq ==> eq ==> impl) (@M.Equiv elt) | 10.
    Proof. Proper_equiv_t. Qed.
    Local Instance Proper_M_Equiv_eq_flip_impl_pointwise elt
      : Proper (pointwise_relation _ (pointwise_relation _ (flip impl)) ==> eq ==> eq ==> flip impl) (@M.Equiv elt) | 10.
    Proof. Proper_equiv_t. Qed.
    Local Instance Proper_M_Equiv_eq_iff_pointwise elt
      : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> eq ==> eq ==> iff) (@M.Equiv elt) | 10.
    Proof. Proper_equiv_t. Qed.


    Lemma M_elements_iff elt m x e
      : M.MapsTo x e m <-> InA (M.eq_key_elt (elt:=elt)) (x, e) (M.elements m).
    Proof. split; first [ apply M.elements_1 | apply M.elements_2 ]. Qed.
    Lemma M_forall_In_elements_iff elt (P : _ -> Prop) (m : M.t elt)
          (P_Proper : Proper (@M.eq_key_elt _ ==> Basics.flip impl) P)
      : (forall i, List.In i (M.elements m) -> P i)
        <-> (forall k v, M.find k m = Some v -> P (k, v)).
    Proof.
      setoid_rewrite <- M_find_iff.
      setoid_rewrite M_elements_iff.
      setoid_rewrite InA_alt.
      split; intros; destruct_head' prod; repeat t_destr_step; firstorder eauto.
    Qed.
    Lemma M_forall_In_elements_snd_iff elt (P : _ -> Prop) (m : M.t elt)
      : (forall i, List.In i (M.elements m) -> P (snd i))
        <-> (forall k v, M.find k m = Some v -> P v).
    Proof.
      rewrite M_forall_In_elements_iff; [ reflexivity | ].
      cbv; repeat intro; repeat t_destr_step; assumption.
    Qed.

    Lemma M_add_full elt0 m0 v x' y' : @M.find elt0 y' (M.add x' v m0) = if Y.eq_dec x' y' then Some v else M.find y' m0.
    Proof using Type.
      clear.
      pose_MapsTo_as_find M.add_1.
      pose_MapsTo_as_find M.add_2.
      pose_MapsTo_as_find M.add_3.
      repeat match goal with
             | [ |- context[M.find ?x ?m] ]
               => destruct (M.find x m) eqn:?
             end.
      all: break_innermost_match.
      all: specialize_under_binders_by eassumption.
      all: intuition congruence.
    Qed.
    Hint Rewrite M_add_full : list_map_alt.
    Local Ltac t_full_step :=
      first [ t_destr_step
            | progress cbv [M.In not option_map] in *
            | progress intros
            | match goal with
              | [ H : context[M.MapsTo] |- _ ] => setoid_rewrite M_find_iff in H
              | [ |- context[M.MapsTo] ] => setoid_rewrite M_find_iff
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

    Lemma M_remove_full elt0 m0 x' y' : @M.find elt0 y' (M.remove x' m0) = if Y.eq_dec x' y' then None else M.find y' m0.
    Proof using Type.
      clear.
      pose proof (@M.remove_1 elt0 m0 x' y') as H0.
      pose_MapsTo_as_find (@M.remove_2 elt0 m0 x' y').
      pose_MapsTo_as_find (@M.remove_3 elt0 m0 x' y').
      repeat t_full_step.
    Qed.
    Hint Rewrite M_remove_full : list_map_alt.

    Lemma M_mapi_full : forall (elt elt':Type)(m: M.t elt)(x:M.key)(f:M.key->elt->elt'), exists y, Y.eq y x /\ M.find x (M.mapi f m) = option_map (f y) (M.find x m).
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
    Hint Rewrite M_mapi_full : list_map_alt.
    Lemma M_mapi_full_impl (elt elt':Type)(m: M.t elt)(f:M.key->elt->elt')(P:_->Prop)
      : (forall x e, M.find x (M.mapi f m) = Some e -> P e)
        -> (forall x, exists y, Y.eq y x /\ forall e, option_map (f y) (M.find x m) = Some e -> P e).
    Proof.
      intros H x.
      specialize (H x).
      destruct (@M_mapi_full _ _ m x f) as [? [H0 H1]].
      eexists; split; [ eassumption | ].
      specialize_under_binders_by rewrite H1.
      intuition congruence.
    Qed.
    Lemma M_map2_full
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
      setoid_rewrite M_find_iff in H.
      setoid_rewrite M_find_iff in H'.
      specialize_under_binders_by eapply ex_intro.
      destruct (M.find x (M.map2 f m m')); break_innermost_match; try reflexivity;
        specialize_by eauto; specialize_under_binders_by reflexivity; eauto.
      firstorder congruence.
    Qed.
    Hint Rewrite M_map2_full : list_map_alt.

    Create HintDb list_map_non_empty_db discriminated.

    Local Ltac t_non_empty_handle_add_step :=
      first [ match goal with
              | [ H : context[M.find _ (M.add _ _ _)] |- _ ]
                => setoid_rewrite M_add_full in H
              | [ |- context[M.find _ (M.add _ _ _)] ]
                => setoid_rewrite M_add_full
              | [ H : forall k v, (if Y.eq_dec ?x k then @?A k v else @?B k v) = Some v -> @?P k v |- _ ]
                => assert (forall v, A x v = Some v -> P x v)
                  by (let v := fresh in
                      intros v;
                      specialize (H x v);
                      destruct (Y.eq_dec x x);
                      [ exact H | now exfalso; eauto ]);
                   assert (forall k v, (Y.eq x k -> False) -> B k v = Some v -> False)
                     by (let k := fresh in
                         let v := fresh in
                         let H' := fresh in
                         intros k v H';
                         specialize (H k v);
                         destruct (Y.eq_dec x k);
                         [ now exfalso; eauto | exact H ]);
                   clear H
              end ].
    Local Ltac t_non_empty_handle_remove_step :=
      first [ match goal with
              | [ H : context[M.find _ (M.remove _ _)] |- _ ]
                => setoid_rewrite M_remove_full in H
              | [ |- context[M.find _ (M.remove _ _)] ]
                => setoid_rewrite M_remove_full
              end ].
    Local Ltac t_non_empty_handle_mapi_step :=
      first [ match goal with
              | [ H : context[M.find _ (M.mapi _ _)] |- _ ]
                => setoid_rewrite M_mapi_full in H
              | [ |- context[M.find _ (M.mapi _ _)] ]
                => setoid_rewrite M_mapi_full
              | [ H : context[M.find ?k (M.mapi ?f ?m)] |- _ ]
                => let H' := fresh in
                   destruct (@M_mapi_full _ _ m k f) as [? [? H']];
                   rewrite H' in H; rewrite ?H' in *; clear H'; cbv [option_map] in *
              | [ |- context[M.find ?k (M.mapi ?f ?m)] ]
                => let H' := fresh in
                   destruct (@M_mapi_full _ _ m k f) as [? [? H']];
                   rewrite H'; rewrite ?H' in *; clear H'; cbv [option_map] in *
              | [ H : forall x e, M.find x (M.mapi ?f ?m) = Some e -> @?P e |- _ ]
                => pose proof (@M_mapi_full_impl _ _ m f P H);
                   clear H
              end ].
    Local Ltac t_non_empty_handle_map2_step :=
      first [ match goal with
              | [ H : context[M.find _ (M.map2 _ _ _)] |- _ ]
                => setoid_rewrite M_map2_full in H
              | [ |- context[M.find _ (M.map2 _ _ _)] ]
                => setoid_rewrite M_map2_full
              | [ H : context[M.find _ (map_xmap2_l _ _)] |- _ ]
                => setoid_rewrite map_xgmap2_l in H; [ | reflexivity ]
              | [ H : context[M.find _ (map_xmap2_r _ _)] |- _ ]
                => setoid_rewrite map_xgmap2_r in H; [ | reflexivity ]
              end ].
    Local Ltac t_non_empty_extra_step :=
      first [ match goal with
              | [ H : forall k v, M.find k ?m = Some v -> ?f v = true, H' : forall k' v', M.find k' ?m = Some v' -> ?f v' = true -> _ |- _ ]
                => specialize (fun k' v' pf => H' k' v' pf (H _ _ pf))
              | [ H : forall k v, M.find k ?m = Some v -> ?f v = true, H' : forall k' v', M.find k' ?m = Some v' -> _ -> ?f v' = true -> _ |- _ ]
                => specialize (fun k' v' pf pf' => H' k' v' pf pf' (H _ _ pf))
              end ].

    Local Ltac t_non_empty_step :=
      first [ t_destr_conj_step
            | assumption
            | reflexivity
            | progress specialize_under_binders_by exact I
            | progress intros
            | rewrite M.fold_1 in *
            | rewrite <- (fun c => @fold_left_map _ _ c andb), @fold_left_andb_truth_map_iff in *
            | rewrite negb_true_iff, <- not_true_iff_false in *
            | rewrite M_is_empty_iff in *
            | rewrite M_find_empty in *
            | t_destr_step
            | progress cbv [M.Empty not] in *
            | progress cbn [option_map Option.bind] in *
            | progress specialize_under_binders_by (idtac; lazymatch goal with |- True -> _ => idtac end;
                                                    intros _)
            | match goal with
              | [ H : forall x, Some ?y = Some x -> _ |- _ ]
                => specialize (H y eq_refl)
              | [ H : context[M.MapsTo] |- _ ] => setoid_rewrite M_find_iff in H
              | [ |- context[M.MapsTo] ] => setoid_rewrite M_find_iff
              | [ H : context[forall i, List.In i (M.elements _) -> ?f (snd i) = true] |- _ ]
                => setoid_rewrite M_forall_In_elements_snd_iff with (P:=fun e => f e = true) in H
              | [ |- context[forall i, List.In i (M.elements _) -> ?f (snd i) = true] ]
                => setoid_rewrite M_forall_In_elements_snd_iff with (P:=fun e => f e = true)
              end
            | t_non_empty_handle_add_step
            | t_non_empty_handle_remove_step
            | t_non_empty_handle_map2_step
            | t_non_empty_handle_mapi_step
            | t_non_empty_extra_step
            | match goal with
              | [ |- _ /\ _ ] => split
              end
            | solve [ eauto with nocore ] ].

    Section Types.
      Variable elt:Type.
      Definition empty : t elt := mk None I.
      Definition is_empty (m : t elt) : bool := Option.is_None (proj1_sig m).
      Fixpoint add' (x : key) (y : elt) (m : t' elt) {struct x} : T.t elt
        := match x return T.t elt with
           | []
             => Node (Some y) (m <- m; t_case_nd (fun _ m _ => m) m) I
           | x :: xs
             => let add_to d m' m := Node' d (Some (M.add x (add' xs y m') m)) I in
                let default d := add_to d None (@M.empty _) in
                match m return T.t elt with
                | None
                  => default None
                | Some m
                  => t_case_nd
                       (fun d m pf
                        => match m return T.t elt with
                           | None => default d
                           | Some m
                             => add_to d (M.find x m) m
                           end)
                       m
                end
           end.
      Lemma add_non_empty x y m (pf : t'_P m) : t'_P (Some (add' x y m)).
      Proof using Type.
        intros _; specialize (pf I); cbv beta iota.
        revert m pf.
        induction x as [|x xs IH], m as [m|];
          try (induction m as [d m] using (t_case (elt:=elt)));
          cbn [add' Option.bind];
          repeat (break_innermost_match; autounfold with trie_db; autorewrite with trie_db).
        all: repeat t_non_empty_step.
        all: solve [ apply IH; clear IH; repeat t_non_empty_step ].
      Qed.
      Definition add (x : key) (y : elt) (m : t elt) : t elt
        := mk (Some (add' x y (proj1_sig m))) (add_non_empty x y (proj2_sig m) I).
      Fixpoint find' (x : key) (m : t' elt) {struct x} : option elt
        := (m <- m;
            match x with
            | [] => t_case_nd (fun v _ _ => v) m
            | x :: xs
              => t_case_nd
                   (fun v m pf => m <- m; find' xs (M.find x m))
                   m
            end).
      Definition find (x : key) (m : t elt) : option elt
        := find' x (proj1_sig m).
      Fixpoint remove' (k : key) (m : t' elt) {struct k} : t' elt
        := (m <- m;
            match k return _ with
            | []
              => t_case_nd
                   (fun d m pf
                    => match m return _ with
                       | None => None
                       | Some m => Some (Node' None (Some m) I)
                       end)
                   m
            | x :: xs
              => t_case_nd
                   (fun d m pf
                    => let default : t' elt := Some (Node d m pf) in
                       match m return _ with
                       | None => default
                       | Some m
                         => match remove' xs (M.find x m) return _ with
                            | None
                              => oNode_dec_empty d (M.remove x m)
                            | Some m'
                              => Some (Node' d (Some (M.add x m' m)) I)
                            end
                       end)
                   m
            end).
      Lemma remove_non_empty x m (pf : t'_P m) : t'_P (remove' x m).
      Proof using Type.
        intros _; specialize (pf I); cbv beta iota.
        destruct (remove' x m) as [m'|] eqn:H; [ | exact I ].
        revert m m' H pf.
        induction x as [|x xs IH], m as [m|];
          try (induction m as [d m] using (t_case (elt:=elt)));
          cbn [remove' Option.bind];
          intros *;
          repeat match goal with
                 | [ |- Some _ = Some _ -> _ ] => intro; inversion_option; subst
                 | [ |- None = Some _ -> _ ] => intro; inversion_option; subst
                 | _ => break_innermost_match; autounfold with trie_db; autorewrite with trie_db
                 end.
        all: repeat t_non_empty_step.
        all: solve [ eapply IH; [ eassumption | ]; clear IH; repeat t_non_empty_step ].
      Qed.
      Definition remove (x : key) (m : t elt) : t elt
        := mk (remove' x (proj1_sig m)) (remove_non_empty x (proj2_sig m) I).
      Definition mem (x : key) (m : t elt) : bool := Option.is_Some (find x m).
      Variable elt' elt'' : Type.
      Lemma mapi_non_empty (f : key -> elt -> elt') (m : t' elt) (pf : t'_P m) : t'_P (option_map (mapi f) m).
      Proof using Type.
        clear -pf.
        intros _; specialize (pf I); cbv beta iota.
        destruct m as [m|]; cbv [option_map]; [ | exact I ].
        revert f pf.
        induction m as [d m pf IH] using (t_ind (elt:=elt)); intro f;
          repeat (autounfold with trie_db; autorewrite with trie_db).
        all: repeat t_non_empty_step.
        all: repeat match goal with
                    | [ H : context[recursively_non_empty] |- _ ] => clear H
                    end.
        all: exactly_once (idtac; multimatch goal with
                                  | [ H : ?T -> False |- False ]
                                    => apply H; clear H
                                  end).
        all: intros; specialize_all_ways.
        all: repeat t_non_empty_step.
      Qed.
      Definition mapi (f : key -> elt -> elt') (m : t elt) : t elt'
        := mk (option_map (mapi f) (proj1_sig m)) (mapi_non_empty f (proj2_sig m) I).
      Definition map (f : elt -> elt') : t elt -> t elt' := mapi (fun _ => f).
      Definition map2' (f : option elt -> option elt' -> option elt'') (m1 : t' elt) (m2 : t' elt') : t' elt''
        := match m1, m2 with
           | None, None => None
           | Some m1, Some m2 => map2 f m1 m2
           | Some m1, None => map2_l f m1
           | None, Some m2 => map2_r f m2
           end.
      Lemma map2_l_non_empty f m : t'_P (map2_l (elt:=elt) (elt':=elt') (elt'':=elt'') f m).
      Proof using Type.
        clear.
        intros _; cbv beta iota.
        destruct (map2_l f m) as [m'|] eqn:H; [ | exact I ].
        revert m m' H.
        induction m as [d m pf IH] using (t_ind (elt:=_));
          intro m'; induction m' as [d' m' pf'] using (t_case (elt:=_)).
        all: repeat first [ match goal with
                            | [ |- Some _ = Some _ -> _ ] => intro; inversion_option; subst
                            | [ |- None = Some _ -> _ ] => intro; inversion_option; subst
                            end
                          | progress inversion_Node
                          | progress (break_match; autounfold with trie_db; autorewrite with trie_db) ].
        all: repeat t_non_empty_step.
      Qed.
      Lemma map2_r_non_empty f m : t'_P (map2_r (elt:=elt) (elt':=elt') (elt'':=elt'') f m).
      Proof using Type.
        clear.
        intros _; cbv beta iota.
        destruct (map2_r f m) as [m'|] eqn:H; [ | exact I ].
        revert m m' H.
        induction m as [d m pf IH] using (t_ind (elt:=_));
          intro m'; induction m' as [d' m' pf'] using (t_case (elt:=_)).
        all: repeat first [ match goal with
                            | [ |- Some _ = Some _ -> _ ] => intro; inversion_option; subst
                            | [ |- None = Some _ -> _ ] => intro; inversion_option; subst
                            end
                          | progress inversion_Node
                          | progress (break_match; autounfold with trie_db; autorewrite with trie_db) ].
        all: repeat t_non_empty_step.
      Qed.
      Lemma map2_non_empty f m1 m2 : t'_P (map2 (elt:=elt) (elt':=elt') (elt'':=elt'') f m1 m2).
      Proof using Type.
        clear.
        intros _; cbv beta iota.
        destruct (map2 f m1 m2) as [m'|] eqn:H; [ | exact I ].
        revert m1 m2 m' H.
        induction m1 as [d1 m1 pf1 IH1] using (t_ind (elt:=_));
          intro m2; induction m2 as [d2 m2 pf2] using (t_case (elt:=_));
          intro m'; induction m' as [d' m' pf'] using (t_case (elt:=_)).
        all: repeat first [ match goal with
                            | [ |- Some _ = Some _ -> _ ] => intro; inversion_option; subst
                            | [ |- None = Some _ -> _ ] => intro; inversion_option; subst
                            end
                          | progress inversion_Node
                          | progress (break_match; autounfold with trie_db; autorewrite with trie_db) ].
        all: repeat t_non_empty_step.
        all: lazymatch goal with
             | [ H : map2_l ?f ?m = Some _ |- _ ]
               => generalize (@map2_l_non_empty f m I); rewrite H; clear H
             | [ H : map2_r ?f ?m = Some _ |- _ ]
               => generalize (@map2_r_non_empty f m I); rewrite H; clear H
             end.
        all: trivial.
      Qed.
      Lemma map2'_non_empty f m1 m2 : t'_P (map2' f m1 m2).
      Proof using Type.
        clear.
        intros _; cbv beta iota.
        destruct m1 as [m1|], m2 as [m2|]; cbn [map2'];
          try first [ apply map2_l_non_empty | apply map2_r_non_empty | apply map2_non_empty ]; exact I.
      Qed.
      Definition map2 (f : option elt -> option elt' -> option elt'') (m1 : t elt) (m2 : t elt') : t elt''
        := mk (map2' f (proj1_sig m1) (proj1_sig m2)) (map2'_non_empty _ _ _ I).

      Definition fold' A (f : key -> elt -> A -> A) (m : t' elt) (a : A) : A
        := match m with
           | None => a
           | Some m => fold f m a
           end.
      Definition fold A (f : key -> elt -> A -> A) (m : t elt) (a : A) : A
        := fold' f (proj1_sig m) a.
      Definition elements_with_key_prefix_and (m : t' elt) (k_prefix : key) prefix : list (key*elt)
        := List.rev_append (fold' (fun k v rest => (k_prefix ++ k, v) :: rest) m prefix) nil.
      Definition elements' (m : t' elt) : list (key*elt) := elements_with_key_prefix_and m nil nil.
      Definition elements (m : t elt) : list (key*elt) := elements' (proj1_sig m).
      Definition cardinal (m : t elt) : nat := List.length (elements m).
    End Types.

    Definition equal elt (cmp : elt -> elt -> bool) (m1 m2 : t elt) : bool
      := let cmp' x y
           := match x, y with
              | Some x, Some y => Some (cmp x y)
              | Some _, None
              | None, Some _
                => Some false
              | None, None => None
              end in
         fold (fun _ => andb) (map2 cmp' m1 m2) true.
    Definition MapsTo elt (k : key) (v : elt) (m : t elt) : Prop
      := find k m = Some v.
    Definition eq_key elt (p p':key*elt) := E.eq (fst p) (fst p').
    Definition eq_key_elt elt (p p':key*elt) :=
      E.eq (fst p) (fst p') /\ (snd p) = (snd p').

    Definition In elt (k : key) (m : t elt) := exists e, MapsTo k e m.
    Definition Empty elt (m : t elt) := forall a e, ~ MapsTo a e m.
    Definition Equal elt (m m' : t elt) := forall y, find y m = find y m'.
    Definition Equiv elt (eq_elt:elt->elt->Prop) m m' :=
      (forall k, In k m <-> In k m') /\
        (forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
    Definition Equivb elt (cmp: elt->elt->bool) := Equiv (Cmp cmp).

    Create HintDb list_map_alt discriminated.
    Create HintDb list_map_alt1 discriminated.
    Create HintDb list_map_alt2 discriminated.
    Create HintDb list_map_alt3 discriminated.


    Local Ltac t :=
      repeat first [ progress intros
                   | t_destr_step
                   | reflexivity
                   | progress cbv [not] in *
                   | solve [ exfalso; auto with nocore ]
                   | t_specialize_safe_step
                   | progress break_innermost_match
                   | progress break_innermost_match_hyps
                   | progress cbv [Option.is_Some Option.is_None Option.value Option.bind M.eq_key_elt] in *
                   | progress autounfold with list_map_alt in *
                   | progress autounfold with trie_db in *
                   | match goal with
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
                     | [ H : proj1_sig ?x = _ |- _ ] => is_var x; destruct x
                     | [ H : Some _ = ?x |- _ ] => symmetry in H
                     | [ H : None = ?x |- _ ] => symmetry in H
                     end
                   | progress autorewrite with list_map_alt in *
                   | progress autorewrite with trie_db in *
                   | solve [ eauto using ex_intro, eq_refl with nocore ]
                   | progress specialize_under_binders_by reflexivity
                   | progress specialize_under_binders_by progress autorewrite with trie_db
                   | progress specialize_under_binders_by progress autorewrite with list_map_alt
                   | progress cbn in * ].

    Lemma find'_None elt k : @find' elt k None = None.
    Proof. case k; t. Qed.
    Hint Rewrite find'_None : list_map_alt.
    Lemma find_None elt k pf : @find elt k (mk None pf) = None.
    Proof. case k; t. Qed.
    Hint Rewrite find_None : list_map_alt.

    Definition Empty_alt elt (m : t elt) : Prop := proj1_sig m = None.

    Lemma Empty_alt_iff elt (s : t elt) : Empty s <-> Empty_alt s.
    Proof.
      cbv [Empty Empty_alt MapsTo M.Empty not key M.key E.t find proj1_sig].
      split; repeat intro; destruct_head' t; destruct_head' option; try reflexivity; inversion_option;
        exfalso;
        try solve [ destruct_one_head list; inversion_option ].
      let t := match goal with H : T.t _ |- _ => H end in
      induction t as [d m pf] using (t_ind (elt:=elt)).
      let H := match goal with H : forall a e, find' a _ = Some e -> False |- _ => H end in
      pose proof (H nil); pose proof (fun x y => H (x :: y)); clear H.
      cbn [find' Option.bind] in *.
      repeat (autounfold with trie_db in *; autorewrite with trie_db in * ).
      specialize_under_binders_by rewrite t_case_beta.
      repeat t_non_empty_step.
      let rec tac _ :=
        first [ t_non_empty_step
              | match goal with
                | [ H : _ = Some _ |- _ ]
                  => progress specialize_under_binders_by rewrite H;
                     solve [ repeat tac () ]
                | [ H : _ |- _ ] => apply H; clear H; solve [ repeat tac () ]
                end ] in
      tac ().
    Qed.

    Local Instance eq_key_equiv elt : Equivalence (@eq_key elt) | 10.
    Proof.
      split; cbv; intros; break_innermost_match; break_innermost_match_hyps; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
    Qed.
    Local Instance eq_key_elt_equiv elt : Equivalence (@eq_key_elt elt) | 10.
    Proof.
      split; cbv; intros; break_innermost_match; break_innermost_match_hyps; destruct_head'_and; split; try ((idtac + symmetry + etransitivity + exfalso); (eassumption + reflexivity)).
    Qed.


    Global
      Hint Unfold
      (*In_alt*)
      empty
      is_empty
      mem
      add
      (*find*)
      (*remove*)
      mem
      map
      mapi
      map2
      elements
      cardinal
      fold
      equal
      MapsTo
      In
      Empty
      Empty_alt
      (*Equiv_alt*)
      (*Equivb_alt*)
      eq_key
      eq_key_elt
      M.eq_key
      M.eq_key_elt
      option_map
      RelProd
      relation_conjunction
      predicate_intersection
      pointwise_extension
      RelCompFun
      Option.is_Some
      Option.is_None
      Option.bind
      option_map
      Option.value
      not
      Node'
      oNode_dec_empty
      : list_map_alt.

    Hint Rewrite Empty_alt_iff (*Equiv_alt_iff*)
         M.cardinal_1
         M.fold_1
         M_find_iff
         M_find_empty
         E'.eq_alt
         Bool.andb_true_iff
         InA_app_iff
         map_length
         app_length
         fold_left_map
         fold_left_app
         in_map_iff
         in_flat_map
         ECompat.eq_alt
      : list_map_alt.

    Definition M_empty_1' elt : forall x y z, False := @M.empty_1 elt.

    Global Hint Resolve
           M.MapsTo_1
           M.mem_1
           M.empty_1
           M_empty_1'
           M.is_empty_1
           M.add_1
           M.remove_1
           M.find_1
           M.elements_1
           M.equal_1
           M.map_1
           M.mapi_1
           M.map2_1
      : list_map_alt1.
    Global Hint Resolve
           M.mem_2
           M.is_empty_2
           M.add_2
           M.remove_2
           M.find_2
           M.elements_2
           M.equal_2
           M.map_2
           M.mapi_2
           M.map2_2
      : list_map_alt2.
    Global Hint Resolve
           M.add_3
           M.remove_3
           M.elements_3w
      : list_map_alt3.

    Hint Constructors ex and or
      : list_map_alt1 list_map_alt2 list_map_alt3.
    Hint Extern 10
         => progress unfold M.In in *
             : list_map_alt1 list_map_alt2 list_map_alt3.


    Local Ltac spec_t_step_quick
      := first [ progress intros
               | progress cbn [fst snd proj1_sig] in *
               | apply (f_equal2 (@pair _ _))
               | progress destruct_head'_False
               | rewrite <- andb_lazy_alt
               | progress repeat autorewrite with list_map_alt in *
               | progress change Y.t with M.key in *
               | progress repeat autounfold with list_map_alt in *
               | match goal with H : _ |- _ => refine H end
               | congruence
               | reflexivity
               | progress auto
               | exact _
               | progress destruct_head'_and
               | progress destruct_head'_ex
               | progress break_innermost_match_hyps
               | progress break_innermost_match
               | progress destruct_head'_or
               | progress specialize_under_binders_by eassumption
               | progress inversion_option
               | progress subst
               | match goal with
                 | [ H : M.MapsTo ?k ?v ?m, H' : context[M.find ?k ?m] |- _ ]
                   => erewrite M.find_1 in H' by exact H
                 end
               | progress specialize_under_binders_by apply conj ].

    Global Hint Extern 100
           => spec_t_step_quick
             : list_map_alt1 list_map_alt2 list_map_alt3.

    Local Ltac saturate_find_step :=
      let cleanup :=
        repeat match goal with
               | [ H : ?T, H' : ?T |- _ ] => clear H'
               end in
      first [ progress inversion_option
            | progress subst
            | exfalso; assumption
            | progress cleanup
            | progress (specialize_under_binders_by (idtac; match goal with |- _ -> False => eauto with nocore end); cleanup)
            | match goal with
              | [ H : Y.eq _ _ |- _ ]
                => unique pose proof (Y.eq_sym H)
              | [ H : Y.eq _ _, H' : context[Y.eq _ _ -> False] |- _ ]
                => lazymatch type of H' with | _ -> False => fail | _ => idtac end;
                   clear H'
              | [ H : Y.eq _ _ |- _ ] => progress (specialize_all_ways_under_binders_by exact H; cleanup)
              | [ H : context[forall a, M.find _ _ = _], H' : M.find _ _ = _ |- _ ]
                => let H'' := fresh in
                   pose proof H' as H'';
                   rewrite H in H'' by fail;
                   let T := type of H'' in
                   lazymatch T with
                   | Some _ = Some _
                     => progress inversion_option; progress subst
                   | Some _ = None => inversion_option
                   | None = Some _ => inversion_option
                   | _
                     => revert H'';
                        lazymatch goal with
                        | [ H : T |- _ ] => fail
                        | _ => idtac T; intro
                        end
                   end
              end
            | progress (specialize_gen_under_binders_by' true ltac:(eauto with nocore); cleanup)
            | match goal with
              | [ H : M.find _ _ = Some _ |- _ ] => progress (specialize_all_ways_under_binders_by exact H; cleanup)
              end ].
    Local Ltac saturate_find := repeat saturate_find_step.

    Local Hint Extern 2 => Proper_compose_hint : typeclass_instances.

    Local Ltac spec_t_nosubst_step_quick :=
      first [ progress intros
            | t_destr_step
            | reflexivity
            | progress destruct_head' t
            | progress destruct_head' key
            | t_specialize_safe_step ].
    Local Ltac spec_t_nosubst_step :=
      first [ spec_t_nosubst_step_quick
            | progress autorewrite with trie_db in *
            | progress autounfold with trie_db in *
            | progress autorewrite with list_map_alt in *
            | progress autounfold with list_map_alt in *
            | progress cbn [find add'] in *
            | setoid_rewrite M_find_iff
            | match goal with
              | [ H : context[M.MapsTo] |- _ ] => setoid_rewrite M_find_iff in H
              end
            | progress break_innermost_match
            | progress break_innermost_match_hyps
            | match goal with
              | [ |- iff _ _ ] => split
              end
            | congruence
            | solve [ eauto ]
            | match goal with
              | [ |- context[@M.find ?elt ?x ?m] ] => destruct (@M.find elt x m) eqn:?
              end
            (*| (* should figure out how to generalize these into lemmas *)
              match goal with
              | [ H : M.is_empty (M.remove ?k ?m) = true, H' : M.find ?k' ?m = Some _, H'' : E2.eq ?k ?k' -> False |- _ ]
                => exfalso; clear -H H' H'';
                   apply M.is_empty_2 in H;
                   cbv [M.Empty] in H;
                   setoid_rewrite M_find_iff in H;
                   specialize (H k')
              | [ H : M2.is_empty (M2.remove ?k ?m) = true, H' : M2.find ?k' ?m = Some _, H'' : E2.eq ?k ?k' -> False |- _ ]
                => exfalso; clear -H H' H'';
                   apply M2.is_empty_2 in H;
                   cbv [M2.Empty] in H;
                   setoid_rewrite M2_find_iff in H;
                   specialize (H k')
              end*) ].
    Local Ltac spec_t_step :=
      first [ spec_t_nosubst_step
            | progress setoid_subst_rel Y.eq ].

    Local Ltac spec_t := repeat spec_t_step.

    Section Spec.

      Variable elt:Type.
      Variable elt' elt'' : Type.
      Variable m m' m'' : t elt.
      Variable x y z : key.
      Variable e e' : elt.
      Lemma MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.
      Proof using Type.
        clear.
        cbv [MapsTo find].
        destruct m as [m' pf]; cbn [proj1_sig]; clear m pf.
        revert x y m'.
        induction x as [|x' xs IH], y as [|y' ys], m' as [m|]; clear x y m';
          try specialize (IH ys);
          try (induction m as [d m'] using (t_case (elt:=elt)); clear m).
        all: t.
        all: pose_MapsTo_as_find M.MapsTo_1.
        all: repeat match goal with
                    | [ H : context[find' _ (@M.find ?a ?b ?c)] |- _ ]
                      => destruct (@M.find a b c) eqn:?
                    | [ |- context[find' _ (@M.find ?a ?b ?c)] ]
                      => destruct (@M.find a b c) eqn:?
                    end.
        all: specialize_under_binders_by eassumption.
        all: t.
      Qed.
      Lemma mem_1 : In x m -> mem x m = true.
      Proof using Type. clear; t. Qed.
      Lemma mem_2 : mem x m = true -> In x m.
      Proof using Type. clear; t. Qed.
      Lemma empty_1 : Empty (@empty elt).
      Proof using Type. clear; pose proof M.empty_1; spec_t. Qed.
      Lemma is_empty_1 : Empty m -> is_empty m = true.
      Proof using Type. clear; pose proof M.is_empty_1; spec_t. Qed.
      Lemma is_empty_2 : is_empty m = true -> Empty m.
      Proof using Type. clear; pose proof M.is_empty_2; spec_t. Qed.
      Lemma find'_iff elt0 k v m0 : @MapsTo elt0 k v m0 <-> find' k (proj1_sig m0) = Some v.
      Proof using Type. clear; spec_t. Qed.
      Lemma find_iff elt0 k v m0 : @MapsTo elt0 k v m0 <-> find k m0 = Some v.
      Proof using Type. clear; spec_t. Qed.
      Lemma find_1 : MapsTo x e m -> find x m = Some e.
      Proof using Type. apply find_iff. Qed.
      Lemma find_2 : find x m = Some e -> MapsTo x e m.
      Proof using Type. apply find_iff. Qed.
      Hint Rewrite fold_left_flat_map fold_left_map : list_map_alt.
      Lemma elements_alt_1 (m0 : t' elt) k_prefix i : elements_with_key_prefix_and m0 k_prefix (List.rev i) = fold' (fun k v rest => rest ++ [(k_prefix ++ k, v)]) m0 i.
      Proof using Type.
        clear.
        pose proof (_ : forall A, Proper (eq ==> eq ==> eq) (@cons A)).
        cbv [elements elements_with_key_prefix_and fold'].
        rewrite <- rev_alt; destruct m0 as [m'|]; [ | rewrite rev_involutive; reflexivity ].
        revert i k_prefix.
        induction m' as [d m pf IH] using (t_ind (elt:=elt)); clear m'; intros.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        destruct m; try (now destruct d; cbn [List.rev]; rewrite rev_involutive); [].
        rewrite !M.fold_1.
        setoid_rewrite (@app_cons_app_app _ k_prefix).
        etransitivity;
          [
          | apply fold_left_ext_in; intros;
            pose_MapsTo_as_find M.elements_2;
            specialize_under_binders_by (rewrite InA_alt; eexists; split; try eassumption; repeat split; try apply Y.eq_refl);
            eapply IH; eassumption ].
        clear IH pf.
        set (i1 := match d with None => i | _ => _ end).
        set (i2 := match d with None => List.rev i | _ => _ end).
        replace i2 with (List.rev i1)
          by (subst i1 i2; break_innermost_match; cbn [rev]; rewrite ?rev_app_distr; cbn [rev List.app]; reflexivity).
        clearbody i1.
        clear i2 i.
        revert i1.
        set (ls := M.elements _).
        induction ls as [|? ? IH]; cbn [fold_left]; intros;
          [ | rewrite <- IH ]; now rewrite rev_involutive.
      Qed.
      Lemma elements_with_key_prefix_and_cps_id (m0 : t' elt) k_prefix prefix : elements_with_key_prefix_and m0 k_prefix prefix = (List.rev prefix) ++ elements_with_key_prefix_and m0 k_prefix nil.
      Proof using Type.
        clear.
        pose proof (_ : forall A, Proper (eq ==> eq ==> eq) (@cons A)).
        set (n := nil); change n with (List.rev n); subst n.
        rewrite <- (List.rev_involutive prefix), !elements_alt_1, List.rev_involutive.
        cbv [fold'].
        destruct m0 as [m'|]; [ | now rewrite ?app_nil_r ].
        generalize (List.rev prefix); clear prefix; intro prefix.
        revert prefix k_prefix.
        induction m' as [d m pf IH] using (t_ind (elt:=elt)); clear m'; intros.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        destruct m; try (now destruct d; rewrite ?app_nil_r, ?app_nil_l); [].
        rewrite !M.fold_1.
        setoid_rewrite (@app_cons_app_app _ k_prefix).
        etransitivity;
          [ apply fold_left_ext_in; intros;
            pose_MapsTo_as_find M.elements_2;
            specialize_under_binders_by (rewrite InA_alt; eexists; split; try eassumption; repeat split; try apply Y.eq_refl);
            eapply IH; eassumption
          | ].
        etransitivity;
          [
          | apply f_equal;
            apply fold_left_ext_in; intros;
            pose_MapsTo_as_find M.elements_2;
            specialize_under_binders_by (rewrite InA_alt; eexists; split; try eassumption; repeat split; try apply Y.eq_refl);
            symmetry; eapply IH; eassumption ].
        clear IH pf.
        set (i1 := match d with None => prefix | _ => _ end).
        set (i2 := match d with None => nil | _ => _ end).
        replace i1 with (prefix ++ i2)
          by (subst i1 i2; break_innermost_match; cbn [List.app]; now rewrite ?app_nil_r).
        clearbody i2.
        clear i1 d.
        revert i2.
        set (ls := M.elements _).
        induction ls as [|? ? IH]; cbn [fold_left]; intros;
          [ reflexivity | ].
        now rewrite <- IH, ?app_assoc.
      Qed.
      Lemma elements_with_key_prefix_alt (m0 : t' elt) k_prefix prefix
        : elements_with_key_prefix_and m0 k_prefix (List.rev prefix)
          = prefix
              ++ match m0 with
                 | None => []
                 | Some m
                   => t_case_nd
                        (fun d m pf
                         => match d with
                            | Some d => [(k_prefix ++ [], d)]
                            | None => []
                            end
                              ++ (List.flat_map
                                    (fun km => elements_with_key_prefix_and (Some (snd km)) (k_prefix ++ [fst km]) nil)
                                    match m with
                                    | Some m => M.elements m
                                    | None => []
                                    end))
                        m
                 end.
      Proof using Type.
        clear.
        pose proof (_ : forall A, Proper (eq ==> eq ==> eq) (@cons A)).
        rewrite elements_with_key_prefix_and_cps_id, rev_involutive.
        apply f_equal.
        change (@nil ?A) with (List.rev (@nil A)) at 1.
        rewrite elements_alt_1.
        cbv [fold'].
        destruct m0 as [m'|]; [ | now rewrite ?app_nil_r ].
        induction m' as [d m pf] using (t_case (elt:=elt)); clear m'.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        destruct m as [m'|]; [ | break_innermost_match; cbn; now rewrite ?app_nil_r ].
        cbn [List.app].
        clear pf.
        set (d' := match d with None => nil | Some _ => _ end).
        rewrite !M.fold_1.
        setoid_rewrite (@app_cons_app_app _ k_prefix).
        set (ls := M.elements _).
        clearbody d'; clear d.
        revert d'.
        induction ls as [|?? IH]; cbn -[elements_with_key_prefix_and]; intros;
          [ now rewrite ?app_nil_r | ].
        rewrite IH, !app_assoc, ?app_nil_r.
        apply f_equal2; [ | reflexivity ].
        rewrite <- (List.rev_involutive d'), <- elements_with_key_prefix_and_cps_id, elements_alt_1, rev_involutive; reflexivity.
      Qed.
      Lemma map_elements_with_key_prefix_and k_prefix (m0 : t' elt)
        : List.map
            (fun '(ks, v) => (k_prefix ++ ks, v))
            (elements' m0)
          = elements_with_key_prefix_and m0 k_prefix nil.
      Proof using Type.
        clear.
        pose proof (_ : forall A, Proper (eq ==> eq ==> eq) (@cons A)).
        cbv [elements'].
        set (i := nil) at 2 3.
        etransitivity; [ | set_evars; rewrite <- (app_nil_r k_prefix); subst_evars; reflexivity ].
        set (k_prefix' := nil).
        change i with (List.rev i) at 1.
        change i with (List.rev (List.map (fun '(ks, v) => (k_prefix ++ ks, v)) i)) at 2.
        rewrite !elements_with_key_prefix_alt.
        destruct m0 as [m'|]; [ | reflexivity ].
        rewrite map_app.
        apply f_equal.
        clearbody i k_prefix'.
        clear.
        revert k_prefix k_prefix'.
        induction m' as [d m pf IH] using (t_ind (elt:=elt)); clear m'; intros.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        destruct m as [m'|]; [ | break_innermost_match; cbn; now rewrite ?app_nil_r ].
        rewrite map_app.
        apply f_equal2;
          [ now break_innermost_match; cbn; rewrite ?app_nil_r
          | ].
        rewrite map_flat_map.
        apply ListUtil.flat_map_ext; intros.
        rewrite <- app_assoc.
        change (@nil ?A) with (List.rev (@nil A)).
        rewrite !elements_with_key_prefix_alt; cbn.
        pose_MapsTo_as_find M.elements_2.
        specialize_under_binders_by (rewrite InA_alt; eexists; split; try eassumption; repeat split; try apply Y.eq_refl).
        eapply IH; eassumption.
      Qed.
      Lemma elements'_alt (m0 : t' elt)
        : elements' m0
          = match m0 with
            | None => []
            | Some m
              => t_case_nd
                   (fun d m pf
                    => match d with
                       | Some d => [([], d)]
                       | None => []
                       end
                         ++ (List.flat_map
                               (fun '(k, m) => List.map
                                                 (fun '(ks, v) => (k :: ks, v))
                                                 (elements' (Some m)))
                               match m with
                               | Some m => M.elements m
                               | None => []
                               end))
                   m
            end.
      Proof using Type.
        clear.
        unfold elements' at 1.
        change (@nil ?A) with (List.rev (@nil A)) at 2.
        rewrite elements_with_key_prefix_alt; cbn -[elements'].
        destruct m0 as [m'|]; [ | reflexivity ].
        induction m' as [d m pf] using (t_case (elt:=elt)); clear m'.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        repeat (f_equiv; []; repeat intro).
        break_innermost_match.
        rewrite (@map_elements_with_key_prefix_and [_]).
        reflexivity.
      Qed.
      Lemma fold_1 :
        forall (A : Type) (i : A) (f : key -> elt -> A -> A),
          fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.
      Proof using Type.
        clear.
        intros A i f.
        cbv [fold fold' elements].
        destruct m as [[m'|] pf']; clear m; [ | reflexivity ].
        cbn [proj1_sig] in *; clear pf'.
        revert f i.
        induction m' as [d m pf IH] using (t_ind (elt:=elt)); clear m'; intros.
        rewrite elements'_alt.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        destruct m as [m'|]; [ | now break_innermost_match ].
        specialize_under_binders_by (apply M.find_1, M.elements_2; rewrite InA_alt; eexists; repeat split; try reflexivity).
        clear pf.
        rewrite M.fold_1.
        rewrite fold_left_app, fold_left_flat_map.
        etransitivity; [ apply fold_left_ext_in | f_equal; try reflexivity; break_innermost_match; cbn; reflexivity ]; cbn.
        intros.
        break_innermost_match.
        erewrite IH by eassumption.
        rewrite fold_left_map; f_equiv; repeat intro; subst; break_innermost_match; reflexivity.
      Qed.

      Lemma add'_full m0 v x' y' : @find' elt y' (Some (add' x' v m0)) = if E.eq_dec x' y' then Some v else find' y' m0.
      Proof using Type.
        clear.
        revert x' y' m0.
        induction x' as [|x xs IH], y' as [|y ys], m0 as [m|];
          first [ specialize (IH ys) | try clear IH ];
          try (induction m as [d m'] using (t_case (elt:=elt)); clear m).
        all: repeat first [ progress invlist eqlistA
                          | progress cbn [find' add' Option.bind]
                          | progress cbv [not] in *
                          | progress autounfold with trie_db
                          | reflexivity
                          | progress specialize_under_binders_by apply eqlistA_cons
                          | match goal with
                            | [ IH : forall m, find' ?k (Some (add' ?xs ?v m)) = _ |- context[find' ?k (Some (add' ?xs ?v ?m'))] ]
                              => rewrite IH
                            end
                          | progress break_innermost_match_step
                          | progress autorewrite with trie_db list_map_alt in *
                          | progress setoid_subst_rel Y.eq ].
        all: t.
      Qed.
      Lemma add_1 : E.eq x y -> MapsTo y e (add x e m).
      Proof using Type. clear; cbv [find add]; intros; rewrite !find'_iff, !add'_full in *; spec_t. Qed.
      Lemma add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
      Proof using Type. clear; cbv [find add]; intros; rewrite !find'_iff, !add'_full in *; spec_t. Qed.
      Lemma add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.
      Proof using Type. clear; cbv [find add]; intros; rewrite !find'_iff, !add'_full in *; spec_t. Qed.
      Lemma remove'_full m0 x' y'
        : @find' elt y' (remove' x' m0) = if E.eq_dec x' y' then None else find' y' m0.
      Proof using Type.
        clear.
        revert x' y' m0.
        induction x' as [|x xs IH], y' as [|y ys], m0 as [m|];
          first [ specialize (IH ys) | try clear IH ];
          try (induction m as [d m'] using (t_case (elt:=elt)); clear m).
        all: repeat first [ progress intros
                          | progress subst
                          | progress inversion_option
                          | progress inversion_sigma
                          | progress invlist eqlistA
                          | progress cbn [find' remove' Option.bind]
                          | progress cbv [not] in *
                          | progress autounfold with trie_db
                          | progress split_iff
                          | reflexivity
                          | exfalso; assumption
                          | progress specialize_under_binders_by assumption
                          | progress specialize_under_binders_by apply eqlistA_nil
                          | progress specialize_under_binders_by apply eqlistA_cons
                          | match goal with
                            | [ H : forall m, find' ?ys (remove' ?xs m) = _, H' : remove' ?xs _ = Some ?v |- context[Some ?v] ]
                              => rewrite <- H', H
                            | [ H : forall m, find' ?ys (remove' ?xs m) = find' ?ys m, H' : remove' ?xs ?m' = None |- context[find' ?ys ?m'] ]
                              => rewrite <- H, H'
                            | [ H : context[@M.is_empty_1 ?a ?b] |- _ ]
                              => generalize dependent (@M.is_empty_1 a b)
                            end
                          | progress break_innermost_match_step
                          | progress autorewrite with trie_db list_map_alt in *
                          | progress cbv [dec_empty_cps] in *
                          | apply conj
                          | progress break_innermost_match_hyps
                          | progress setoid_subst_rel Y.eq
                          | match goal with
                            | [ H : M.is_empty (M.remove ?x ?m) = true |- context[M.find ?y ?m] ]
                              => destruct (Y.eq_dec x y); specialize_under_binders_by assumption;
                                 setoid_subst_rel Y.eq;
                                 apply M.is_empty_2 in H;
                                 cbv [M.Empty not] in H;
                                 try now exfalso
                            | [ |- None = find' _ (@M.find ?a ?b ?c) ]
                              => destruct (@M.find a b c) eqn:?
                            end ].
        all: specialize_all_ways.
        all: t.
      Qed.
      Lemma remove_1 : E.eq x y -> ~ In y (remove x m).
      Proof using Type. clear; cbv [In]; setoid_rewrite find_iff; setoid_rewrite remove'_full; spec_t. Qed.
      Lemma remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
      Proof using Type. clear; cbv [In]; setoid_rewrite find_iff; setoid_rewrite remove'_full; spec_t. Qed.
      Lemma remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.
      Proof using Type. clear; cbv [In]; setoid_rewrite find_iff; setoid_rewrite remove'_full; spec_t. Qed.

      Lemma elements_iff :
        MapsTo x e m <-> InA (@eq_key_elt _) (x,e) (elements m).
      Proof using Type.
        clear; cbv [MapsTo].
        rewrite InA_alt.
        cbv [eq_key_elt]; cbn [fst snd].
        destruct m as [m' pf]; clear m.
        cbv [find elements proj1_sig]; clear pf; rename m' into m.
        revert m; induction x as [|?? IH];
          (intros [m'|];
           [ induction m' as [d m pf] using (t_case (elt:=elt)); clear m'
           | now rewrite elements'_alt; destruct x; cbn; split; intros; inversion_option; firstorder ]).
        all: rewrite elements'_alt.
        all: repeat (autounfold with trie_db; autorewrite with trie_db).
        all: destruct m as [m'|].
        all: setoid_rewrite in_app_iff.
        all: setoid_rewrite in_flat_map.
        all: cbn [find' Option.bind].
        all: repeat (cbn [Option.bind]; autounfold with trie_db; autorewrite with trie_db).
        1-2: now split; intros; subst; t;
        eexists (_, _); cbn; repeat esplit; try reflexivity; eauto.
        all: try (rewrite IH; clear IH).
        all: split; intros; inversion_option.
        all: repeat first [ progress destruct_head'_ex
                          | progress destruct_head'_and
                          | progress destruct_head'_or
                          | progress destruct_head'_False
                          | progress subst
                          | progress cbn [List.In fst snd] in *
                          | progress cbv [M.eq_key_elt] in *
                          | rewrite ECompat.eq_alt in *
                          | rewrite in_map_iff in *
                          | rewrite InA_alt in *
                          | progress invlist eqlistA
                          | break_innermost_match_hyps_step
                          | apply conj
                          | apply eqlistA_cons
                          | eassumption
                          | erewrite M.find_1
                            by (apply M.elements_2; rewrite InA_alt; eexists; split; [ | eassumption ]; repeat esplit; eassumption)
                          | reflexivity
                          | match goal with
                            | [ H : M.find _ _ = Some _ |- _ ] => apply M.find_2, M.elements_1 in H
                            | [ |- False \/ _ ] => right
                            | [ |- ((nil, _) = (cons _ _, _) \/ False) \/ _ ] => right
                            | [ H : List.In _ (elements' (M.find ?k ?m)) |- _ ]
                              => destruct (M.find k m) eqn:?
                            | [ H : context[elements' None] |- _ ]
                              => cbn in H
                            end
                          | eexists (_, _)
                          | rewrite <- surjective_pairing ].
      Qed.
      Lemma elements_1 :
        MapsTo x e m -> InA (@eq_key_elt _) (x,e) (elements m).
      Proof using Type. apply elements_iff. Qed.
      Lemma elements_2 :
        InA (@eq_key_elt _) (x,e) (elements m) -> MapsTo x e m.
      Proof using Type. apply elements_iff. Qed.
      Lemma elements_3w : NoDupA (@eq_key _) (elements m).
      Proof using Type.
        clear.
        cbv [elements proj1_sig]; destruct m as [[m'|] _]; clear m;
          [ | now constructor ].
        induction m' as [d m pf IH] using (t_ind (elt:=elt)); clear m'.
        rewrite elements'_alt.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        apply NoDupA_app; try exact _; break_innermost_match; repeat constructor;
          intros *; try (rewrite !InA_alt; cbv [eq_key]); cbn [fst snd List.In proj1_sig] in *; clear pf.
        all: repeat first [ intro
                          | progress cbn [fst snd proj1_sig] in *
                          | progress destruct_head'_ex
                          | progress destruct_head'_and
                          | progress destruct_head'_False
                          | progress subst
                          | progress destruct_head'_or
                          | rewrite in_flat_map in *
                          | rewrite in_map_iff in *
                          | break_innermost_match_hyps_step
                          | progress destruct_head' prod
                          | progress setoid_subst_rel E.eq
                          | rewrite ECompat.eq_alt in *
                          | progress invlist eqlistA ].
        all: [ > ].
        let x := match goal with |- NoDupA _ (flat_map _ (M.elements ?m)) => m end in
        pose proof (M.elements_3w x).
        specialize_under_binders_by (apply M.find_1, M.elements_2; rewrite InA_alt; eexists; repeat split; try reflexivity).
        eapply @NoDupA_flat_map; try eassumption; try exact _.
        { rewrite Forall_map, Forall_forall; intros; break_innermost_match.
          eapply NoDupA_map_inv'; [ | eapply IH; eassumption ].
          spec_t. }
        { cbv [eq_key M.eq_key]; intros; rewrite !InA_alt in *.
          repeat match goal with
                 | [ H : context[M.elements _] |- _ ] => clear H
                 | [ H : context[@elements' ?A] |- _ ] => generalize dependent (@elements' A); intros
                 | [ H : ~M.Empty _ |- _ ] => clear H
                 | [ H : option _ |- _ ] => clear H
                 end.
          repeat first [ t_destr_step
                       | progress destruct_head' prod
                       | progress setoid_subst_rel Y.eq
                       | rewrite ECompat.eq_alt in *
                       | t_specialize_safe_step ]. }
      Qed.
      Lemma cardinal_1 : cardinal m = length (elements m).
      Proof using Type. clear; spec_t. Qed.


      Variable cmp : elt -> elt -> bool.

      Lemma M_equal_iff elt0 cmp0 m0 m'0 : @M.equal elt0 cmp0 m0 m'0 = true <-> M.Equivb cmp0 m0 m'0.
      Proof using Type. split; first [ apply M.equal_1 | apply M.equal_2 ]. Qed.
    End Spec.

    Lemma mapi_full : forall (elt elt':Type)(m: t elt)(x:key)(f:key->elt->elt'), exists y, E.eq y x /\ find x (mapi f m) = option_map (f y) (find x m).
    Proof.
      cbv [mapi find].
      intros elt elt' [[m|] pf]; [ | intros [|]; eexists; split; reflexivity ].
      cbn [proj1_sig]; clear pf.
      induction m as [d m pf IH] using (t_ind (elt:=elt)).
      intros [|x xs] f.
      all: cbn [find']; cbn [option_map Option.bind].
      all: repeat (autounfold with trie_db; autorewrite with trie_db).
      all: try (eexists; split; reflexivity).
      all: [ > ].
      destruct m as [m|]; [ | now cbn; eauto ].
      cbn [option_map proj1_sig Option.bind] in *.
      clear pf.
      edestruct M_mapi_full as [? [HY H]]; rewrite H.
      destruct (M.find x m) eqn:H'; rewrite ?find'_None; cbn [option_map] in *.
      1: specialize_under_binders_by eassumption.
      1: do 2 (let t := open_constr:(_) in evar (v : t); specialize (IH v); subst v).
      1: destruct IH as [? [? IH]].
      1: rewrite IH.
      all: clear IH H H'.
      all: eexists; rewrite ECompat.eq_alt in *; repeat constructor; try eassumption; reflexivity.
    Qed.
    Lemma map_full : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'), find x (map f m) = option_map f (find x m).
    Proof.
      cbv [map].
      intros.
      edestruct mapi_full as [? [? H]].
      rewrite H; reflexivity.
    Qed.
    Lemma map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
        MapsTo x e m -> MapsTo x (f e) (map f m).
    Proof. intros *; rewrite !find_iff, map_full; cbv [option_map]; break_innermost_match; spec_t. Qed.
    Lemma map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
        In x (map f m) -> In x m.
    Proof. intros *; cbv [In]; setoid_rewrite find_iff; setoid_rewrite map_full; cbv [option_map]; break_innermost_match; spec_t. Qed.
    Lemma mapi_1 (elt elt':Type)(m: t elt)(x:key)(e:elt)
          (f:key->elt->elt')
      : MapsTo x e m ->
        exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
    Proof.
      setoid_rewrite find_iff.
      edestruct mapi_full as [?[? H]]; rewrite H.
      intros ->.
      repeat esplit; eassumption.
    Qed.
    Lemma mapi_2
      : forall (elt elt':Type)(m: t elt)(x:key)
               (f:key->elt->elt'), In x (mapi f m) -> In x m.
    Proof.
      intros *; cbv [In].
      setoid_rewrite find_iff.
      edestruct mapi_full as [?[? ->]].
      destruct find; cbn; intros; repeat t_destr_step; eauto.
    Qed.
    Lemma map2'_full
      : forall (elt elt' elt'':Type)(m: t' elt)(m': t' elt')
	       (x:key)(f:option elt->option elt'->option elt''),
        find' x (map2' f m m') = match find' x m, find' x m' with
                                 | None, None => None
                                 | x, y => f x y
                                 end.
    Proof.
      intros elt elt' elt'' m m' x f.
      revert m m'.
      induction x as [|x xs IH].
      { cbv [map2' find' Option.bind]; intros.
        repeat first [ t_destr_conj_step
                     | reflexivity
                     | break_innermost_match_step
                     | break_innermost_match_hyps_step
                     | progress break_match_hyps
                     | progress autounfold with trie_db in *
                     | progress inversion_Node
                     | match goal with
                       | [ |- context[t_case _ ?v] ]
                         => is_var v; induction v using (t_case (elt:=_));
                            autorewrite with trie_db in *
                       end
                     | progress autorewrite with trie_db in * ]. }
      intros [m|] [m'|]; try reflexivity;
        try induction m as [d [m|] pf] using (t_case (elt:=elt));
        try induction m' as [d' [m'|] pf'] using (t_case (elt:=elt'));
        first [ specialize (IH (M.find x m)) | specialize (IH None) ];
        first [ specialize (IH (M.find x m')) | specialize (IH None) ].
      all: rewrite ?find'_None in *.
      all: cbn [find']; cbv [map2' Option.bind] in *.
      all: repeat first [ reflexivity
                        | progress repeat (autounfold with trie_db in *; autorewrite with trie_db in * )
                        | progress break_match
                        | match goal with
                          | [ |- context[t_case _ ?v] ]
                            => is_var v; induction v using (t_case (elt:=_));
                               autorewrite with trie_db in *
                          end ].
      all: repeat first [ t_destr_conj_step
                        | reflexivity
                        | progress inversion_Node
                        | match goal with
                          | [ H : M.is_empty _ = true |- _ ]
                            => apply M.is_empty_2 in H
                          | [ H : M.Empty (M.map2 _ _ _) |- _ ]
                            => cbv [M.Empty not] in H;
                               setoid_rewrite M_find_iff in H;
                               setoid_rewrite M_map2_full in H;
                               specialize (H x)
                          | [ H : M.Empty (map_xmap2_l _ _) |- _ ]
                            => cbv [M.Empty not] in H;
                               specialize (H x);
                               setoid_rewrite M_find_iff in H;
                               rewrite map_xgmap2_l in H by reflexivity
                          | [ H : M.Empty (map_xmap2_r _ _) |- _ ]
                            => cbv [M.Empty not] in H;
                               specialize (H x);
                               setoid_rewrite M_find_iff in H;
                               rewrite map_xgmap2_r in H by reflexivity
                          | [ H : forall e, ?x = Some e -> False |- _ ]
                            => destruct x eqn:?; [ specialize (H _ eq_refl); exfalso; exact H | clear H ]
                          end
                        | rewrite M_map2_full
                        | rewrite map_xgmap2_l by reflexivity
                        | rewrite map_xgmap2_r by reflexivity
                        | rewrite find'_None in *
                        | break_innermost_match_step
                        | break_innermost_match_hyps_step
                        | progress break_match_hyps
                        | congruence ].
    Qed.
    Lemma map2_1
      : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	       (x:key)(f:option elt->option elt'->option elt''),
        In x m \/ In x m' ->
        find x (map2 f m m') = f (find x m) (find x m').
    Proof.
      cbv [In]; intros *.
      setoid_rewrite find'_iff.
      cbv [find map2 proj1_sig]; intros *.
      destruct m as [m _], m' as [m' _].
      rewrite !map2'_full.
      break_innermost_match; try reflexivity.
      firstorder congruence.
    Qed.
    Lemma map2_2
      : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
	       (x:key)(f:option elt->option elt'->option elt''),
        In x (map2 f m m') -> In x m \/ In x m'.
    Proof.
      cbv [In]; intros *.
      setoid_rewrite find'_iff.
      cbv [find map2 proj1_sig]; intros *.
      destruct m as [m _], m' as [m' _].
      rewrite !map2'_full.
      break_innermost_match; firstorder; inversion_option; eauto.
    Qed.

    Section Spec_equal.
      Variable elt:Type.
      Variable m m' : t elt.
      Variable cmp : elt -> elt -> bool.

      Lemma equal_iff : equal cmp m m' = true <-> Equivb cmp m m'.
      Proof using Type.
        clear; cbv [equal Equivb] in *.
        cbv [Equiv In Cmp].
        setoid_rewrite find_iff.
        rewrite fold_1, <- fold_left_rev_right, <- fold_right_map, fold_right_andb_true_map_iff.
        setoid_rewrite <- in_rev.
        repeat split; intros; repeat t_destr_step.
        all: lazymatch goal with
             | [ |- exists e, ?x = Some e ] => destruct x eqn:?; eauto
             | _ => idtac
             end.
        all: lazymatch goal with
             | [ H : forall i, List.In i ?ls -> snd i = true |- _ ]
               => assert (forall i, InA (@eq_key_elt _) i ls -> snd i = true);
                  [ let i := fresh "i" in
                    intro i; rewrite InA_alt; cbv [eq_key_elt snd]; intros;
                    specialize (fun i0 => H (i0, snd i));
                    repeat t_destr_conj_step;
                    break_innermost_match_hyps; subst;
                    cbn [snd] in *;
                    eapply H; eassumption
                  | clear H ]
             | [ H : List.In ?i ?ls |- _ ]
               => assert (InA (@eq_key_elt _) i ls);
                  [ let i := fresh "i" in
                    rewrite InA_alt; cbv [eq_key_elt];
                    eexists; repeat esplit; try eassumption; reflexivity
                  | clear H ]
             end.
        all: specialize_under_binders_by (apply elements_1, find_2; setoid_rewrite map2'_full).
        all: destruct_head' t; cbv [proj1_sig find] in *.
        all: repeat match goal with
                    | [ H : _ = Some _ |- _ ]
                      => progress specialize_under_binders_by rewrite H
                    | [ H : _ = None |- _ ]
                      => progress specialize_under_binders_by rewrite H
                    end.
        all: specialize_under_binders_by reflexivity.
        all: cbn [snd] in *.
        all: try congruence.
        all: destruct_head' prod.
        all: specialize_all_ways.
        all: split_iff.
        all: lazymatch goal with
             | [ H : InA _ _ (elements (map2 _ _ _)) |- _ ]
               => apply elements_2, find_1 in H;
                  setoid_rewrite map2'_full in H
             end.
        all: cbv [proj1_sig] in *.
        all: break_innermost_match_hyps; specialize_under_binders_by eapply ex_intro.
        all: specialize_under_binders_by reflexivity.
        all: repeat t_destr_conj_step.
        all: specialize_under_binders_by eassumption.
        all: eassumption.
      Qed.
      Lemma equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
      Proof using Type. apply equal_iff. Qed.
      Lemma equal_2 : equal cmp m m' = true -> Equivb cmp m m'.
      Proof using Type. apply equal_iff. Qed.
    End Spec_equal.
  End ListWSfun_gen.
End ListWSfun_gen.

Module ListWSfun (Y : DecidableTypeOrig) (M : WSfun Y) (Import T : Trie Y M).
  Module _ListWSfun.
    Module Outer := ListWSfun_gen Y M T.
    Module E := ListDecidableTypeOrig Y.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> eqlistA Y.eq x y.
      Proof. cbv [E.eq]; reflexivity. Qed.
    End ECompat.
    Module Inner <: WSfun E := Outer.ListWSfun_gen E ECompat.
  End _ListWSfun.
  Include _ListWSfun.Inner.
End ListWSfun.

Module ListUsualWeakMap (M : UsualWS) (Import T : Trie M.E M) <: UsualWS.
  Module Outer := ListWSfun_gen M.E M T.
  Module E := ListUsualDecidableTypeOrig M.E.
  Module ECompat <: Outer.ESigCompat E.
    Lemma eq_alt : forall x y, E.eq x y <-> eqlistA M.E.eq x y.
    Proof. cbv; intros; rewrite eqlistA_eq_iff; intuition. Qed.
  End ECompat.
  Module Inner <: WSfun E := Outer.ListWSfun_gen E ECompat.
  Include Inner.
End ListUsualWeakMap.

Module ListWeakMap (M : WS) (T : Trie M.E M) <: WS.
  Include ListWSfun M.E M T.
  Module E := _ListWSfun.E.
End ListWeakMap.

Module ListSfun_gen (Y : OrderedTypeOrig) (M : Sfun Y) (Import T : Trie Y M).
  Module ListWSfun := ListWSfun_gen Y M T.
  Module P := ListHasLt Y.
  Module Type ESig := ListWSfun.ESig <+ HasLt <+ HasMiniOrderedType.
  Module Type ESigCompat (E : ESig).
    Include ListWSfun.ESigCompat E.
    Axiom lt_alt : forall x y, E.lt x y <-> P.lt x y.
  End ESigCompat.
  Module ListSfun_gen (E : ESig) (ECompat : ESigCompat E) <: Sfun E.
    Include ListWSfun.ListWSfun_gen E ECompat.
    Module Y' := Y <+ UpdateEq <+ UpdateStrOrder.
    Global Remove Hints Y'.eq_refl Y'.eq_sym Y'.eq_trans : core.
    Module P' := ListStrOrder Y'.
    Local Existing Instances eq_key_equiv eq_key_elt_equiv.
    Local Instance M_lt_key_Transitive elt' : Transitive (@M.lt_key elt') | 10.
    Proof. cbv; intros *; eapply Y.lt_trans. Qed.
    Section elt.
      Variable elt:Type.
      Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').

      Lemma elements_3 m : sort lt_key (elements m).
      Proof using Type.
        pose proof Y'.lt_compat.
        pose proof P'.lt_compat.
        destruct m as [[m|] pfm]; [ | constructor ].
        cbv [elements proj1_sig].
        clear pfm.
        induction m as [d m pf IH] using (t_ind (elt:=elt)).
        rewrite elements'_alt.
        repeat (autounfold with trie_db; autorewrite with trie_db).
        destruct m as [m|]; [ | now break_innermost_match; cbn; repeat constructor ].
        eapply @SortA_app with (eqA:=@eq_key_elt _); try exact _.
        all: try solve [ break_innermost_match; repeat constructor ].
        all: try solve [
                 intros *; rewrite !InA_alt; cbv [eq_key_elt]; break_innermost_match;
                 cbn [List.In]; intros;
                 destruct_head' prod;
                 repeat t_destr_step;
                 cbv [lt_key]; cbn;
                 rewrite ECompat.eq_alt, ECompat.lt_alt in *;
                 repeat t_destr_step; cbn; auto ].
        cbn [proj1_sig] in *; clear pf d.
        eapply @SortA_flat_map with (eqA:=@eq_key _) (eqB:=eq); try eassumption; try eapply M.elements_3; try rewrite Forall_map, Forall_forall; try exact _.
        all: [ >
             | cbv [M.lt_key lt_key eq_key]; setoid_rewrite InA_alt; intros;
               destruct_head' prod;
               repeat t_destr_step;
               rewrite ECompat.eq_alt, ECompat.lt_alt in *;
               repeat t_destr_step; cbn;
               repeat match goal with
                      | [ H : List.In _ _ |- _ ] => clear H
                      end;
               setoid_subst_rel Y.eq;
               setoid_subst_rel (eqlistA Y.eq);
               now eauto ].
        match goal with
        | [ |- context[Sorted] ]
          => intros; break_innermost_match; rewrite Sorted_map_iff
        end.
        eassert (H' : InA _ _ (M.elements m));
          [ rewrite InA_alt
          | eapply M.elements_2, M.find_1 in H' ];
          [ repeat esplit; try eassumption; reflexivity
          | ].
        specialize (IH _ _ H').
        eapply Sorted_Proper_impl; [ | | eapply IH ]; [ | reflexivity ];
          repeat intro; break_innermost_match; cbv [lt_key eq_key_elt] in *; rewrite ECompat.lt_alt; cbn [fst snd P.lt] in *;
          destruct_head'_and; subst;
          rewrite ECompat.eq_alt, ECompat.lt_alt in *.
        right; split; try reflexivity.
        repeat match goal with
               | [ H : M.find _ _ = _ |- _ ] => clear H
               | [ H : List.In _ _ |- _ ] => clear H
               | [ H : Sorted _ _ |- _ ] => clear H
               | [ H : ~M.Empty _ |- _ ] => clear H
               end.
        setoid_subst_rel (eqlistA Y.eq).
        assumption.
      Qed.
    End elt.
  End ListSfun_gen.
End ListSfun_gen.

Module ListSfun (Y : OrderedTypeOrig) (M : Sfun Y) (T : Trie Y M).
  Module _ListSfun.
    Module Outer := ListSfun_gen Y M T.
    Module E := ListOrderedTypeOrig Y.
    Module ECompat <: Outer.ESigCompat E.
      Lemma eq_alt : forall x y, E.eq x y <-> eqlistA Y.eq x y.
      Proof. cbv [E.eq]; reflexivity. Qed.
      Lemma lt_alt : forall x y, E.lt x y <-> E.lt x y.
      Proof. cbv [E.lt]; reflexivity. Qed.
    End ECompat.
    Module Inner <: Sfun E := Outer.ListSfun_gen E ECompat.
  End _ListSfun.
  Include _ListSfun.Inner.
End ListSfun.

Module ListUsualMap (M : UsualS) (T : Trie M.E M) <: UsualS.
  Module Outer := ListSfun_gen M.E M T.
  Module E := ListUsualOrderedTypeOrig M.E.
  Module ECompat <: Outer.ESigCompat E.
    Lemma eq_alt : forall x y, E.eq x y <-> eqlistA M.E.eq x y.
    Proof. cbv; intros; rewrite eqlistA_eq_iff; intuition. Qed.
    Lemma lt_alt : forall x y, E.lt x y <-> E.lt x y.
    Proof. cbv [E.lt]; reflexivity. Qed.
  End ECompat.
  Module Inner <: Sfun E := Outer.ListSfun_gen E ECompat.
  Include Inner.
End ListUsualMap.

Module ListMap (M : S) (T : Trie M.E M) <: S.
  Include ListSfun M.E M T.
  Module E := _ListSfun.E.
End ListMap.

(* TODO:
Module IsoSord (S' : Sord) (Data' : IsoMiniOrderedType S'.Data) (E : IsoMiniOrderedType S'.MapS.E) (S'_iso : IsoMiniOrderedType S') <: Sord <: IsoOrderedType S'.
  Module Data <: IsoOrderedType S'.Data := Data' <+ OT_of_MOT.
  Module MapS <: S := IsoS S'.MapS E.
  Import MapS.

  Definition t := MapS.t Data.t.

  Definition eq : t -> t -> Prop.
    refine (_ S'.eq).
    compute.
    pose MapS.E.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. [Data.compare] is a total ordering
      used to compare data associated with equal keys in the two maps. *)


  Include S.
  Include OT_of_MOT.
End IsoSord.
  Definition t := MapS.t Data.t.

  Print IsoMiniOrderedType.
  Definition eq : t -> t -> Prop := S'.eq.
  Parameter lt : t -> t -> Prop.

  Axiom eq_refl : forall m : t, eq m m.
  Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
  Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
  Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
  Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

  Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

  Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
  Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

  Parameter compare : forall m1 m2, Compare lt eq m1 m2.
  (** Total ordering between maps. [Data.compare] is a total ordering
      used to compare data associated with equal keys in the two maps. *)

End Sord.

*)
