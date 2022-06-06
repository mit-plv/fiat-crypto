Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.SetoidList.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SpecializeUnderBindersBy.
Require Import Crypto.Util.ListUtil.StdlibCompat.

Import ListNotations.

Lemma NoDupA_flat_map {B A} {eqB : relation B} {eqA : relation A}
      {eqvA : Equivalence eqA}
      {rB : Reflexive eqB}
      (f : B -> list A) (ls : list B)
  : Forall (NoDupA eqA) (List.map f ls)
    -> NoDupA eqB ls
    -> (forall x y, ~eqB x y -> InA eqB x ls -> InA eqB y ls -> forall x', InA eqA x' (f x) -> InA eqA x' (f y) -> False)
    -> NoDupA eqA (flat_map f ls).
Proof.
  rewrite Forall_map.
  induction 1; inversion 1; subst; cbn [flat_map]; intro H'; [ constructor | ].
  apply NoDupA_app; eauto; [].
  invlist NoDupA.
  intros.
  rewrite ?InA_alt in *.
  cbv [not] in *.
  specialize_under_binders_by rewrite InA_alt.
  specialize_under_binders_by eapply ex_intro.
  specialize_under_binders_by apply conj.
  destruct_head'_ex.
  destruct_head'_and.
  rewrite in_flat_map in *.
  destruct_head'_ex.
  destruct_head'_and.
  cbn [In] in *.
  eauto.
Qed.

Lemma SortA_flat_map {B A} {eqB ltB : relation B} {eqA ltA : relation A}
      {eqvA : Equivalence eqA}
      {rB : Reflexive eqB}
      {rlB : Transitive ltB}
      (f : B -> list A) (ls : list B)
  : Forall (Sorted ltA) (List.map f ls)
    -> Sorted ltB ls
    -> (forall x y, ltB x y -> InA eqB x ls -> InA eqB y ls -> forall x' y', InA eqA x' (f x) -> InA eqA y' (f y) -> ltA x' y')
    -> Sorted ltA (flat_map f ls).
Proof.
  rewrite Forall_map.
  induction 1; inversion 1; subst; cbn [flat_map]; intro H'; [ constructor | ].
  eapply SortA_app; eauto; [].
  invlist Sorted.
  intros.
  rewrite ?InA_alt in *.
  cbv [not] in *.
  specialize_under_binders_by rewrite InA_alt.
  specialize_under_binders_by eapply ex_intro.
  specialize_under_binders_by apply conj.
  destruct_head'_ex.
  destruct_head'_and.
  rewrite in_flat_map in *.
  destruct_head'_ex.
  destruct_head'_and.
  cbn [In] in *.
  eauto.
  eapply H';
    [ | multimatch goal with H : _ |- _ => exact H end + idtac .. ];
    [ | solve [ eauto ] .. ].
  match goal with
  | [ H0 : Sorted ltB ?l, H1 : HdRel ltB ?x ?l, H2 : In ?y ?l, H3 : Transitive ltB |- ltB ?x ?y ]
    => clear -H0 H1 H2 H3;
       revert dependent x; induction H0; cbn [In] in *; try solve [ exfalso; assumption ]
  end.
  intros; destruct_head'_or; subst; invlist HdRel; eauto.
Qed.
