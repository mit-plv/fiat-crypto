From Stdlib Require Import List Sorted Permutation.
Require Import Crypto.Util.ListUtil.Repeat.
Import ListNotations.

Lemma Sorted_repeat [A] R (R_refl : forall x:A, R x x) x n : Sorted R (repeat x n).
Proof.
  apply StronglySorted_Sorted.
  induction n; cbn [repeat]; constructor; auto using Forall_repeat.
Qed.

#[local] Hint Constructors StronglySorted : core.
Lemma StronglySorted_app [A] R (xs ys : list A) :
  StronglySorted R (xs ++ ys) <->
  Forall (fun x => Forall (R x) ys) xs /\ StronglySorted R xs /\ StronglySorted R ys.
Proof.
  split.
  { intros H; remember (xs++ys); generalize dependent ys; revert xs; induction H.
    { intros ? ? []%eq_sym%app_eq_nil; subst; eauto. }
    intros [|x xs] ys E; cbn [app] in *; subst; eauto.
    injection E; clear E; intros; subst.
    specialize (IHStronglySorted xs ys eq_refl) as (?&?&?).
    rewrite Forall_app in *; intuition eauto. }
  { apply and_ind; induction 1; apply and_ind; trivial.
  inversion_clear 1; cbn; constructor; eauto.
  eapply Forall_app; eauto. }
Qed.

Lemma NoDup_StronglySorted {A} R xs (R_irrefl : forall x:A, ~R x x)
  (H : StronglySorted R xs) : NoDup xs.
Proof.
  induction H; constructor; trivial.
  intro; eapply (R_irrefl a), Forall_forall; eauto.
Qed.

Lemma HdRel_map {A B} (f : A -> B) R x xs :
  HdRel R (f x) (map f xs) <-> HdRel (fun a b => R (f a) (f b)) x xs.
Proof.
  induction xs as [|??[]]; split; inversion_clear 1; cbn [map]; constructor; eauto.
Qed.

Lemma Sorted_map {A B} (f : A -> B) R xs :
  Sorted R (map f xs) <-> Sorted (fun a b => R (f a) (f b)) xs.
Proof.
  induction xs as [|??[]]; split; inversion_clear 1; cbn [map];
    constructor; try eapply HdRel_map; eauto.
Qed.

Lemma StronglySorted_Permutation_unique [A] (R : A -> A -> Prop)
  (R_asym : forall x y, R x y -> R y x -> x = y) xs ys
  : StronglySorted R xs -> StronglySorted R ys -> Permutation xs ys -> xs = ys.
Proof.
  intros H; revert ys; induction H as [|x xs Hxs IH].
  { intros ? ? ?%Permutation_nil; congruence. }
  intros [|y ys].
  { intros ? ?%Permutation_sym%Permutation_nil; congruence. }
  inversion_clear 1; intros.
  enough (x = y) as <- by (f_equal; eauto using Permutation_cons_inv); clear IH.
  assert (Forall (fun v => x = v \/ R x v) (y::ys)) as E. {
    eapply Permutation_Forall; try eassumption.
    constructor. left. trivial. eauto using Forall_impl. }
  inversion_clear E as []; intuition try congruence.
  assert (Forall (fun v => y = v \/ R y v) (x::xs)) as E. {
    eapply Permutation_Forall; try symmetry; try eassumption.
    constructor. left. trivial. eauto using Forall_impl. }
  inversion_clear E; intuition try congruence; eauto.
Qed.

Lemma Sorted_Permutation_unique [A] (R : A -> A -> Prop)
  (R_trans : Relations_1.Transitive R) (R_asym : forall x y, R x y -> R y x -> x = y)
  xs ys : Sorted R xs -> Sorted R ys -> Permutation xs ys -> xs = ys.
Proof.
  intros. eapply StronglySorted_Permutation_unique;
    eauto using Sorted_StronglySorted.
Qed.
