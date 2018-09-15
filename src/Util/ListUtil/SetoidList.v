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
