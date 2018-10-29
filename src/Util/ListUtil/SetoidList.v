Require Import Coq.Lists.List.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Lists.SetoidList.
Require Import Crypto.Util.Option.

Import ListNotations.

Lemma list_elementwise_eqlistA : forall {T R} (l1 l2 : list T),
  (forall i, option_eq R (nth_error l1 i) (nth_error l2 i)) -> eqlistA R l1 l2.
Proof.
  induction l1, l2; intros H; try solve [ constructor ];
    pose proof (H 0%nat) as Hfirst; cbn in Hfirst; try solve [ inversion Hfirst ].
  constructor; [ assumption | ].
  apply IHl1.
  intros i; specialize (H (S i)).
  assumption.
Qed.

Lemma nth_error_Proper_eqlistA {T R}
  : Proper (eqlistA R ==> eq ==> option_eq R) (@nth_error T).
Proof.
  intros ls1 ls2 Hls n n' ?; subst n'.
  revert ls1 ls2 Hls.
  induction n; intros ls1 ls2 Hls; destruct Hls; cbn; auto.
Qed.

Lemma eqlistA_eq_iff {A}
  : forall ls1 ls2, eqlistA (@eq A) ls1 ls2 <-> ls1 = ls2.
Proof.
  induction ls1 as [|x xs IHxs], ls2 as [|y ys IHys].
  all: split; intro H; inversion_clear H; repeat constructor; subst; f_equal; try reflexivity.
  apply IHxs; assumption.
Qed.
