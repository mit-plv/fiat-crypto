Require Import Coq.micromega.Lia.
Require Import Coq.Program.Basics.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Lists.List.
Require Import Coq.Lists.SetoidList.
Import ListNotations.
Local Open Scope list_scope.

Lemma SortA_rev A R ls
  : @Sorted A (flip R) ls -> @Sorted A R (List.rev ls).
Proof.
  induction 1; cbn; [ constructor 1 | ].
  let H := match goal with H : HdRel _ _ _ |- _ => H end in
  destruct H; cbn in *; try solve [ repeat constructor ].
  let l := match goal with |- Sorted _ ((rev ?l ++ _) ++ _) => l end in
  induction (List.rev l) as [|x xs IH]; [ repeat constructor; assumption | ].
  cbn in *.
  invlist Sorted.
  constructor; eauto.
  set (ls := xs ++ _) in *.
  assert (List.length ls > 0)
    by (subst ls; rewrite app_length; cbn; lia).
  let H := match goal with H : HdRel _ _ ls |- HdRel _ _ (ls ++ _) => H end in
  destruct H; cbn in *; try solve [ repeat constructor; assumption ]; try lia.
Qed.

Lemma SortA_rev_iff A R ls
  : @Sorted A R (List.rev ls) <-> @Sorted A (flip R) ls.
Proof.
  rewrite <- (rev_involutive ls);
    split; intro; apply SortA_rev; rewrite ?rev_involutive in *;
    assumption.
Qed.
