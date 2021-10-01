Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Lists.List. (* after SeparationLogic *)
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Proofs.VarnameSet.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.

(* for [eauto with lia] *)
Require Import Crypto.Util.ZUtil.Hints.Core.

Import API.Compilers.
Import ListNotations Types.Notations.

Section UsedVarnames.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.
  Local Existing Instance Types.rep.Z.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.
  Local Notation varname := String.string.

  Definition used_varnames nextn nvars : set varname :=
    of_list (map varname_gen (seq nextn nvars)).

  Lemma used_varnames_iff nextn nvars v :
    used_varnames nextn nvars v <->
    (exists n,
        v = varname_gen n /\ nextn <= n < nextn + nvars)%nat.
  Proof.
    cbv [used_varnames of_list]. revert nextn v.
    induction nvars; intros; cbn [seq map In];
      [ split; try tauto; intros; cleanup; lia | ].
    rewrite IHnvars.
    split; intros;
      repeat match goal with
             | _ => progress cleanup
             | _ => progress subst
             | H : _ \/ _ |- _ => destruct H
             | |- exists _, _ => eexists; solve [eauto with lia]
             end; [ ].
    match goal with H : _ <= _ |- _ =>
                    apply le_lt_or_eq in H; destruct H; [right | left]
    end.
    { eexists; eauto with lia. }
    { congruence. }
  Qed.

  Lemma used_varnames_disjoint n1 n2 l1 l2 :
    n1 + l1 <= n2 ->
    disjoint (used_varnames n1 l1) (used_varnames n2 l2).
  Proof.
    cbv [used_varnames].
    revert n1 n2 l2; induction l1; cbn [map seq]; intros;
      rewrite ?of_list_nil, ?of_list_cons;
      eauto using disjoint_empty_l.
    rewrite add_union_singleton.
    apply disjoint_union_l_iff; split; eauto with lia; [ ].
    apply disjoint_not_in. intro.
    repeat match goal with
           | _ => progress cleanup
           | H : In _ (map _ _) |- _ => rewrite in_map_iff in H
           | H : In _ (seq _ _) |- _ => rewrite in_seq in H
           | H : varname_gen _ = varname_gen _ |- _ =>
             apply varname_gen_unique in H
           | _ => lia
           end.
  Qed.

  Lemma used_varnames_succ_high n l :
    sameset (used_varnames n (S l))
            (add (used_varnames n l) (varname_gen (n + l))).
  Proof.
    intros. cbv [used_varnames].
    rewrite seq_snoc, map_app. cbn [map].
    rewrite of_list_app, of_list_cons.
    rewrite !add_union_singleton, of_list_nil, union_empty_r.
    apply union_comm.
  Qed.

  Lemma used_varnames_succ_low n m :
    PropSet.sameset (used_varnames n (S m))
                    (PropSet.add (used_varnames (S n) m)
                                 (varname_gen n)).
  Proof.
    apply sameset_iff. cbn. firstorder idtac.
  Qed.

  Lemma used_varnames_1 n :
    PropSet.sameset (used_varnames n 1)
                    (PropSet.singleton_set (varname_gen n)).
  Proof.
    apply sameset_iff. cbn. firstorder idtac.
  Qed.

  Lemma used_varnames_subset n1 n2 l1 l2 :
    (n2 <= n1)%nat ->
    (n1 + l1 <= n2 + l2)%nat ->
    PropSet.subset (used_varnames n1 l1)
                   (used_varnames n2 l2).
  Proof.
    cbv [PropSet.subset PropSet.elem_of];
      intros; rewrite !used_varnames_iff in *.
    cleanup; subst.
    eexists; split; [ reflexivity | lia ].
  Qed.

  Lemma used_varnames_union n m l :
    sameset (used_varnames n (m + l))
            (union (used_varnames n m) (used_varnames (n + m) l)).
  Proof.
    cbv [used_varnames].
    revert n m; induction l; cbn [map seq]; intros;
      rewrite ?Nat.add_0_r, ?of_list_nil, ?union_empty_r;
      try reflexivity; [ ].
    rewrite of_list_cons, add_union_singleton, union_assoc.
    rewrite <-Nat.add_succ_comm. rewrite IHl.
    rewrite seq_snoc, map_app. cbn [map].
    rewrite of_list_app, of_list_cons.
    rewrite !add_union_singleton, of_list_nil, union_empty_r.
    rewrite Nat.add_succ_r.
    reflexivity.
  Qed.

  Lemma used_varnames_shift n m l :
    subset (used_varnames (n + m) l)
           (used_varnames n (m + l)).
  Proof.
    cbv [subset]. intros.
    match goal with H : _ |- _ =>
                    apply used_varnames_iff in H end.
    apply used_varnames_iff.
    cleanup; subst. eexists; split; eauto.
    lia.
  Qed.

  Lemma used_varnames_subset_singleton n m l :
    n <= m < n + l ->
    subset (singleton_set (varname_gen m))
           (used_varnames n l).
  Proof.
    cbv [subset singleton_set elem_of]. intros.
    apply used_varnames_iff; subst.
    eexists; split; eauto; lia.
  Qed.

  Implicit Types l : locals.

  Lemma only_differ_zero nextn l :
    map.only_differ l (used_varnames nextn 0) l.
  Proof.
    cbv [map.only_differ used_varnames of_list elem_of].
    tauto.
  Qed.

  Lemma only_differ_succ nextn nvars l1 l2 v :
    map.only_differ (map.put l1 (varname_gen nextn) v)
                    (used_varnames (S nextn) nvars) l2 ->
    map.only_differ l1 (used_varnames nextn (S nvars)) l2.
  Proof.
    intros.
    eapply Proper_only_differ;
      [ reflexivity | | reflexivity | eapply only_differ_trans;
         solve [eauto using @only_differ_sym, @only_differ_put with typeclass_instances ] ].
    eapply sameset_iff; intros.
    cbv [used_varnames of_list elem_of union singleton_set].
    cbn [seq map In].
    tauto.
  Qed.

  Lemma only_differ_step nvars nvars' nextn l1 l2 l3 :
    map.only_differ l1 (used_varnames nextn nvars) l2 ->
    map.only_differ l2 (used_varnames (nextn + nvars) nvars') l3 ->
    map.only_differ l1 (used_varnames nextn (nvars + nvars')) l3.
  Proof.
    cbv [map.only_differ used_varnames of_list
                         elem_of].
    let H1 := fresh in
    let H2 := fresh in
    let x := fresh "x" in
    intros H1 H2 x; specialize (H1 x); specialize (H2 x).
    repeat match goal with
           | _ => progress cleanup
           | _ => progress subst
           | H : _ \/ _ |- _ => destruct H
           | |- context [In _ (map _ _)] => rewrite in_map_iff
           | H : In _ (map _ _) |- _ => apply in_map_iff in H
           | H : In _ (seq _ _) |- _ => apply in_seq in H
           | H : varname_gen _ = varname_gen _ |- _ =>
             apply varname_gen_unique in H
           | _ => solve [right; congruence]
           | _ => solve [left; eexists;
                         rewrite in_seq, varname_gen_unique; split;
                         eauto with lia ]
           end.
  Qed.

  Lemma disjoint_used_varnames_lt n nvars (vset : set varname) :
    (forall x, n <= x -> ~ vset (varname_gen x)) ->
    disjoint (used_varnames n nvars) vset.
  Proof.
    cbv [disjoint elem_of]; intros.
    apply Decidable.imp_simp.
    { cbv [used_varnames Decidable.decidable of_list ].
      match goal with
        |- In ?x ?l \/ ~ In ?x ?l =>
        destruct (in_dec string_dec x l); [left|right]
      end; tauto. }
    rewrite used_varnames_iff.
    intros; cleanup; subst.
    eauto with lia.
  Qed.

  Lemma disjoint_used_varnames_singleton n nvars m :
    m < n ->
    disjoint (used_varnames n nvars)
             (singleton_set (varname_gen m)).
  Proof.
    cbv [singleton_set elem_of]; intros.
    eapply disjoint_used_varnames_lt. intros.
    rewrite varname_gen_unique. lia.
  Qed.
End UsedVarnames.
