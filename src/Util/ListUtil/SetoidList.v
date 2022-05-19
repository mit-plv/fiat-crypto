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
  induction ls1 as [|x xs IHxs], ls2 as [|y ys].
  all: split; intro H; inversion_clear H; repeat constructor; subst; f_equal; try reflexivity.
  apply IHxs; assumption.
Qed.

Lemma InA_map_strict A B (f : A -> B) (eqA eqB : relation _) a b l
      (f_Proper_a_b : forall v, List.In v l -> eqA a v -> eqB b (f v))
  : InA eqA a l -> InA eqB b (List.map f l).
Proof.
  rewrite !InA_alt.
  intros [v H]; exists (f v); split; [ now apply f_Proper_a_b | now apply in_map ].
Qed.

Lemma InA_map_strict' A B (f : A -> B) (eqA eqB : relation _) a b l
      (f_Proper_a_b : forall v, List.In v l -> eqB b (f v) -> eqA a v)
  : InA eqB b (List.map f l) -> InA eqA a l.
Proof using Type.
  rewrite !InA_alt.
  intros [? [? H']].
  rewrite in_map_iff in H'.
  destruct H' as [? [? ?]].
  subst.
  eexists; eauto.
Qed.

Lemma InA_map_iff_strict A B (f : A -> B) (eqA eqB : relation _) a b l
      (f_Proper_a_b : forall v, List.In v l -> eqA a v <-> eqB b (f v))
  : InA eqB b (List.map f l) <-> InA eqA a l.
Proof.
  split; (apply InA_map_strict + apply InA_map_strict'); apply f_Proper_a_b.
Qed.

Lemma InA_map_strict_InA A B (f : A -> B) (eqA eqB : relation _) a b l
      {_ : Reflexive eqA}
      (f_Proper_a_b : forall v, InA eqA v l -> eqA a v -> eqB b (f v))
  : InA eqA a l -> InA eqB b (List.map f l).
Proof.
  apply InA_map_strict; intros; eapply f_Proper_a_b; try assumption.
  rewrite InA_alt; eauto.
Qed.

Lemma InA_map_strict_InA' A B (f : A -> B) (eqA eqB : relation _) a b l
      {_ : Reflexive eqA}
      (f_Proper_a_b : forall v, InA eqA v l -> eqB b (f v) -> eqA a v)
  : InA eqB b (List.map f l) -> InA eqA a l.
Proof.
  apply InA_map_strict'; intros; eapply f_Proper_a_b; try assumption.
  rewrite InA_alt; eauto.
Qed.

Lemma InA_map_iff_strict_InA A B (f : A -> B) (eqA eqB : relation _) a b l
      {_ : Reflexive eqA}
      (f_Proper_a_b : forall v, InA eqA v l -> eqA a v <-> eqB b (f v))
  : InA eqB b (List.map f l) <-> InA eqA a l.
Proof.
  apply InA_map_iff_strict; intros; eapply f_Proper_a_b; try assumption.
  rewrite InA_alt; eauto.
Qed.

Lemma InA_map_strict_InA_PER A B (f : A -> B) (eqA eqB : relation _) a b l
      {_ : Symmetric eqA} {_ : Transitive eqA}
      (f_Proper_a_b : forall v, InA eqA v l -> eqA a v -> eqB b (f v))
  : InA eqA a l -> InA eqB b (List.map f l).
Proof.
  apply InA_map_strict; intros; eapply f_Proper_a_b; try assumption.
  rewrite InA_alt; eauto.
Qed.

Lemma InA_map A B (f : A -> B) (eqA eqB : relation _) a b l
      (f_Proper_a_b : forall v, eqA a v -> eqB b (f v))
  : InA eqA a l -> InA eqB b (List.map f l).
Proof. apply InA_map_strict; eauto. Qed.

Lemma InA_map' A B (f : A -> B) (eqA eqB : relation _) a b l
      (f_Proper_a_b : forall v, eqB b (f v) -> eqA a v)
  : InA eqB b (List.map f l) -> InA eqA a l.
Proof. apply InA_map_strict'; eauto. Qed.

Lemma InA_map_iff A B (f : A -> B) (eqA eqB : relation _) a b l
      (f_Proper_a_b : forall v, eqA a v <-> eqB b (f v))
  : InA eqB b (List.map f l) <-> InA eqA a l.
Proof. apply InA_map_iff_strict; eauto. Qed.

Lemma NoDupA_map_inv A B (f : A -> B) (eqA eqB : relation _) (l : list A)
      {f_Proper : Proper (eqA ==> eqB) f}
  : NoDupA eqB (List.map f l) -> NoDupA eqA l.
Proof.
  induction l as [|? ? IH]; cbn [List.map]; intro H; inversion_clear H;
    [ constructor | ].
  specialize (IH ltac:(assumption)).
  constructor; [ | assumption ].
  let H := match goal with H : ~ InA _ _ _ |- _ => H end in
  intro H'; apply H; clear H.
  eapply InA_map; [ | eassumption ].
  intro; apply f_Proper.
Qed.

Lemma NoDupA_map_inv' A B (f : A -> B) (eqA eqB : relation _) (l : list A)
      (f_Proper : forall a v : A, eqB (f a) (f v) -> eqA a v)
  : NoDupA eqA l -> NoDupA eqB (List.map f l).
Proof.
  induction l as [|? ? IH]; cbn [List.map]; intro H; inversion_clear H;
    [ constructor | ].
  specialize (IH ltac:(assumption)).
  constructor; [ | assumption ].
  let H := match goal with H : ~ InA _ _ _ |- _ => H end in
  intro H'; apply H; clear H.
  eapply InA_map'; [ | eassumption ].
  intro; apply f_Proper.
Qed.

Global Instance InA_Proper_impl {A} {eqA : relation A}
       {eqA_Proper : Proper (eqA ==> eqA ==> Basics.impl) eqA}
  : Proper (eqA ==> eqlistA eqA ==> Basics.impl) (@InA A eqA) | 10.
Proof.
  cbv [Basics.impl] in *.
  intros a a' Ha l l' Hl.
  induction Hl as [|?????? IH].
  { intro H'; inversion H'. }
  { intro H'; inversion_clear H';
      try solve [ constructor; eapply eqA_Proper; eassumption
                | constructor; eauto ]. }
Qed.

Global Instance InA_Proper_flip_impl {A} {eqA : relation A}
       {eqA_Proper : Proper (eqA ==> eqA ==> Basics.flip Basics.impl) eqA}
  : Proper (eqA ==> eqlistA eqA ==> Basics.flip Basics.impl) (@InA A eqA) | 10.
Proof.
  cbv [Basics.impl] in *.
  intros a a' Ha l l' Hl.
  induction Hl as [|?????? IH].
  { intro H'; inversion H'. }
  { intro H'; inversion_clear H';
      try solve [ constructor; eapply eqA_Proper; eassumption
                | constructor; eauto ]. }
Qed.

(** We could just use [now typeclasses eauto with core] in Coq >= 8.10, but it doesn't work in 8.9 :-( *)
Local Ltac grepeat_eapply :=
  multimatch goal with
  | [ H : _ |- _ ] => eapply H; clear H
  end;
  solve [ grepeat_eapply ].

Global Instance InA_Proper_iff {A} {eqA : relation A}
       {eqA_Proper : Proper (eqA ==> eqA ==> iff) eqA}
  : Proper (eqA ==> eqlistA eqA ==> iff) (@InA A eqA) | 10.
Proof.
  unshelve (split; (eapply InA_Proper_impl + eapply InA_Proper_flip_impl); assumption).
  all: repeat intro; solve [ edestruct eqA_Proper; grepeat_eapply ].
Qed.

Global Instance NoDupA_Proper_eqlistA_impl {A eqA}
       {eqA_Proper : Proper (eqA ==> eqA ==> flip impl) eqA}
  : Proper (eqlistA eqA ==> impl) (@NoDupA A eqA) | 10.
Proof.
  cbv [flip impl].
  intros l1 l2 Hl.
  induction Hl as [|? ? ? ? ? ? IH].
  { constructor. }
  { intro H'; inversion_clear H'; constructor; eauto.
    all: match goal with
         | [ H : ~InA _ _ _ |- ~ InA _ _ _ ] => intro H'; apply H; clear H
         end.
    eapply InA_Proper_flip_impl; eassumption. }
Qed.

Global Instance NoDupA_Proper_eqlistA_flip_impl {A eqA}
       {eqA_Proper : Proper (eqA ==> eqA ==> impl) eqA}
  : Proper (eqlistA eqA ==> flip impl) (@NoDupA A eqA) | 10.
Proof.
  cbv [flip impl].
  intros l1 l2 Hl.
  induction Hl as [|? ? ? ? ? ? IH].
  { constructor. }
  { intro H'; inversion_clear H'; constructor; eauto.
    all: match goal with
         | [ H : ~InA _ _ _ |- ~ InA _ _ _ ] => intro H'; apply H; clear H
         end.
    eapply InA_Proper_impl; eassumption. }
Qed.

Global Instance NoDupA_Proper_eqlistA_iff {A eqA}
       {eqA_Proper : Proper (eqA ==> eqA ==> iff) eqA}
  : Proper (eqlistA eqA ==> iff) (@NoDupA A eqA) | 10.
Proof.
  unshelve (split; (eapply NoDupA_Proper_eqlistA_impl + eapply NoDupA_Proper_eqlistA_flip_impl); assumption).
  all: repeat intro; solve [ edestruct eqA_Proper; grepeat_eapply ].
Qed.
