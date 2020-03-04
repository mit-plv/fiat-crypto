Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.PropSet.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Coq.Lists.List. (* after SeparationLogic *)
Import ListNotations.

(* This file contains general-purpose lemmas about other libraries that should
   eventually be moved to those libraries or to coqutil *)

Section Lists.
  Context {A : Type}.

  Lemma hd_map {B} (f : A -> B) x l :
    hd (f x) (map f l) = f (hd x l).
  Proof. destruct l; reflexivity. Qed.

  Lemma hd_skipn_nth_default (d:A) l i :
    nth_default d l i = hd d (skipn i l).
  Proof.
    revert i; induction l; destruct i; try reflexivity.
    rewrite nth_default_cons_S, skipn_cons_S. eauto.
  Qed.

  Lemma firstn_length_firstn n (l : list A) :
    firstn (length (firstn n l)) l = firstn n l.
  Proof.
    revert l; induction n; destruct l;
      cbn [firstn length]; rewrite ?IHn; reflexivity.
  Qed.

  Lemma skipn_length_firstn n (l : list A) :
    skipn (length (firstn n l)) l = skipn n l.
  Proof.
    revert l; induction n; destruct l;
      cbn [skipn firstn length]; rewrite ?IHn; reflexivity.
  Qed.

  Lemma NoDup_app_iff (l1 l2 : list A) :
    NoDup (l1 ++ l2) <-> (NoDup l1 /\ NoDup l2
                          /\ (forall x, In x l1 -> ~ In x l2)
                          /\ (forall x, In x l2 -> ~ In x l1)).
  Proof.
    revert l2; induction l1;
      repeat match goal with
             | _ => progress (intros; subst)
             | _ => progress cbn [In]
             | _ => rewrite app_nil_l
             | _ => rewrite <-app_comm_cons
             | _ => split
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H: ~ In _ (_ ++ _) |- _ =>
               rewrite in_app_iff in H;
                 apply Decidable.not_or in H
             | H: NoDup (_ ++ _) |- _ =>
               apply IHl1 in H
             | H: NoDup (_ :: _) |- _ =>
               inversion H; clear H; subst
             | |- ~ (_ \/ _) => intro
             | |- ~ In _ (_ ++_) =>
               rewrite in_app_iff
             | |- NoDup (_ ++ _) => apply IHl1
             | |- NoDup (_ :: _) => constructor
             | |- NoDup [] => constructor
             | H1 : (forall x (H:In x ?l), _),
                    H2 : In _ ?l |- _ => apply H1 in H2; tauto
             | H : forall x (_:?a = x \/ _), _ |- _ =>
               specialize (H a ltac:(tauto)); tauto
             | _ => solve [eauto]
             | _ => tauto
             end.
  Qed.
End Lists.

Section Sets.
  Context {E : Type}.

  Lemma disjoint_union_l_iff (s1 s2 s3 : set E) :
    disjoint (union s1 s2) s3 <-> disjoint s1 s3 /\ disjoint s2 s3.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_union_r_iff (s1 s2 s3 : set E) :
    disjoint s1 (union s2 s3) <-> disjoint s1 s2 /\ disjoint s1 s3.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_cons (s : set E) x l :
    disjoint s (of_list (x :: l)) ->
    disjoint s (of_list l) /\ disjoint s (singleton_set x).
  Proof. firstorder idtac. Qed.

  Lemma disjoint_singleton_r_iff
        (x : E) (s : set E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}):
    ~ s x <->
    disjoint s (singleton_set x).
  Proof.
    intros. split; [|firstorder idtac].
    intros. intro y.
    destruct (eq_dec x y);
      subst; try firstorder idtac.
  Qed.

  Lemma disjoint_singleton_singleton
        (x y : E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}):
    y <> x ->
    disjoint (singleton_set x) (singleton_set y).
  Proof.
    intros.
    apply disjoint_singleton_r_iff;
      firstorder congruence.
  Qed.

  Lemma disjoint_sameset (s1 s2 s3 : set E) :
    sameset s3 s1 ->
    disjoint s1 s2 ->
    disjoint s3 s2.
  Proof. firstorder idtac. Qed.

  Global Instance disjoint_sym : Symmetric (@disjoint E).
  Proof. firstorder idtac. Defined.
  Global Instance disjoint_Proper
    : Proper (sameset ==> sameset ==> iff) (@disjoint E).
  Proof. firstorder idtac. Defined.

  Global Instance sameset_sym : Symmetric (@sameset E).
  Proof. firstorder idtac. Defined.
  Global Instance sameset_trans : Transitive (@sameset E).
  Proof. firstorder idtac. Defined.
  Global Instance sameset_ref : Reflexive (@sameset E).
  Proof. firstorder idtac. Defined.

  Lemma sameset_iff (s1 s2 : set E) :
    sameset s1 s2 <-> (forall e, s1 e <-> s2 e).
  Proof. firstorder idtac. Qed.

  Lemma not_union_iff (s1 s2 : set E) x :
    ~ union s1 s2 x <-> ~ s1 x /\ ~ s2 x.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_not_in x (l : list E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}) :
    ~ In x l ->
    disjoint (singleton_set x) (of_list l).
  Proof.
    intros. symmetry. apply disjoint_singleton_r_iff; eauto.
  Qed.

  Lemma NoDup_disjoint (l1 l2 : list E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}) :
    NoDup (l1 ++ l2) ->
    disjoint (of_list l1) (of_list l2).
  Proof.
    revert l2; induction l1; intros *;
      rewrite ?app_nil_l, <-?app_comm_cons;
      [ solve [firstorder idtac] | ].
    inversion 1; intros; subst.
    rewrite PropSet.of_list_cons.
    apply disjoint_union_l_iff; split; eauto.
    apply disjoint_not_in; eauto.
    rewrite in_app_iff in *. tauto.
  Qed.
End Sets.

Section Maps.
  Context {key value} {key_eqb}
          {map : map.map key value}
          {key_eq_dec :
             forall x y : key,
               BoolSpec (x = y) (x <> y) (key_eqb x y)}
          {map_ok : map.ok map}.

  Lemma only_differ_sym m1 m2 ks :
    map.only_differ m1 ks m2 ->
    map.only_differ m2 ks m1.
  Proof. firstorder congruence. Qed.

  Lemma only_differ_trans m1 m2 m3 ks1 ks2 :
    map.only_differ m2 ks1 m1 ->
    map.only_differ m3 ks2 m2 ->
    map.only_differ m3 (union ks1 ks2) m1.
  Proof. firstorder congruence. Qed.

  Global Instance Proper_only_differ :
    Proper (eq ==> sameset ==> eq ==> iff) map.only_differ.
  Proof. firstorder congruence. Qed.

  Lemma only_differ_put m k v :
    map.only_differ (map.put m k v) (singleton_set k) m.
  Proof.
    cbv [map.only_differ elem_of singleton_set].
    intro x; destr (key_eqb k x); subst;
      rewrite ?map.get_put_same, ?map.get_put_diff by congruence;
      tauto.
  Qed.

  Lemma putmany_of_list_zip_app_l m ks1 ks2 vs :
    map.putmany_of_list_zip (ks1 ++ ks2) vs m =
    Option.bind
      (map.putmany_of_list_zip
         ks1 (List.firstn (Datatypes.length ks1) vs) m)
      (map.putmany_of_list_zip
         ks2 (List.skipn (Datatypes.length ks1) vs)).
  Admitted.

  Lemma putmany_of_list_zip_bind_comm m ks1 ks2 vs1 vs2 :
    Option.bind
      (map.putmany_of_list_zip ks1 vs1 m)
      (map.putmany_of_list_zip ks2 vs2) =
    Option.bind
      (map.putmany_of_list_zip ks2 vs2 m)
      (map.putmany_of_list_zip ks1 vs1).
  Admitted.
End Maps.

(* These lemmas should be moved to bedrock2, not coqutil *)
Section Separation.
  Context `{map_ok : map.ok}
           {key_eqb : forall H H0 : key, bool}
           {key_eq_dec :
              forall x y : key,
                BoolSpec (x = y) (x <> y) (key_eqb x y)}.
  Lemma sep_empty_iff (q r : map.rep -> Prop) :
    sep q r map.empty <-> q map.empty /\ r map.empty.
  Proof.
    cbv [sep].
    repeat match goal with
           | _ => progress (intros; subst)
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : _ |- _ => apply map.split_empty in H
           | _ => rewrite map.split_empty
           | _ => exists map.empty
           | _ => tauto
           | _ => split
           end.
  Qed.
End Separation.
