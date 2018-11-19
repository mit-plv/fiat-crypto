Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Import EqNotations.

Definition related_sigT_by_eq {A P1 P2} (R : forall x : A, P1 x -> P2 x -> Prop)
           (x : @sigT A P1) (y : @sigT A P2)
  : Prop
  := { pf : projT1 x = projT1 y
     | R _ (rew pf in projT2 x) (projT2 y) }.

Definition map_related_sigT_by_eq {A P1 P2} {R1 R2 : forall x : A, P1 x -> P2 x -> Prop}
           (HR : forall x v1 v2, R1 x v1 v2 -> R2 x v1 v2)
           (x : @sigT A P1) (y : @sigT A P2)
  : @related_sigT_by_eq A P1 P2 R1 x y -> @related_sigT_by_eq A P1 P2 R2 x y.
Proof using Type.
  destruct x, y; cbv [related_sigT_by_eq projT1 projT2].
  intro H; exists (proj1_sig H); apply HR, (proj2_sig H).
Qed.

Global Instance related_sigT_by_eq_Reflexive {A P}
       {R : forall x : A, relation (P x)}
       {R_Reflexive : forall x : A, Reflexive (R x)}
  : Reflexive (@related_sigT_by_eq A P P R) | 10.
Proof.
  cbv [related_sigT_by_eq Reflexive projT1 projT2]; intros [? ?].
  exists eq_refl; cbn; reflexivity.
Qed.

Lemma related_sigT_by_eq_sym_gen {A P1 P2 R1 R2 x y}
      (HR : forall x X Y, (R1 x X Y : Prop) -> (R2 x Y X : Prop))
  : @related_sigT_by_eq A P1 P2 R1 x y
    -> @related_sigT_by_eq A P2 P1 R2 y x.
Proof.
  destruct x, y; cbv [related_sigT_by_eq projT1 projT2].
  intros [? H]; subst; exists eq_refl; cbn in *.
  apply HR; assumption.
Qed.

Lemma related_sigT_by_eq_sym_flip_iff {A P1 P2 R x y}
  : @related_sigT_by_eq A P1 P2 R x y
    <-> @related_sigT_by_eq A P2 P1 (fun x => Basics.flip (R x)) y x.
Proof.
  split; apply related_sigT_by_eq_sym_gen; cbv [Basics.flip]; trivial.
Qed.

Lemma related_sigT_by_eq_sym_iff {A P R x y}
      (R_sym : forall x, Symmetric (R x))
  : @related_sigT_by_eq A P P R x y
    <-> @related_sigT_by_eq A P P R y x.
Proof.
  split; apply related_sigT_by_eq_sym_gen; trivial.
Qed.

Global Instance related_sigT_by_eq_Symmetric {A P R}
       {R_Symmetric : forall x, Symmetric (R x)}
  : Symmetric (@related_sigT_by_eq A P P R) | 10
  := fun x y => proj1 (related_sigT_by_eq_sym_iff _).

Lemma related_sigT_by_eq_trans {A P1 P2 P3 R1 R2 R3 x y z}
      (R_trans : forall a x y z, (R1 a x y : Prop) -> (R2 a y z : Prop) -> (R3 a x z : Prop))
  : @related_sigT_by_eq A P1 P2 R1 x y
    -> @related_sigT_by_eq A P2 P3 R2 y z
    -> @related_sigT_by_eq A P1 P3 R3 x z.
Proof.
  destruct x, y, z; cbv [related_sigT_by_eq projT1 projT2];
    intros [? ?] [? ?]; subst; exists eq_refl; cbn in *.
  eauto.
Qed.

Global Instance related_sigT_by_eq_Transitive {A P R}
       {R_Transitive : forall x : A, Transitive (R x)}
  : Transitive (@related_sigT_by_eq A P P R) | 10
  := fun x y z => related_sigT_by_eq_trans R_Transitive.

Global Instance existT_Proper_related_sigT_by_eq {A P R x}
  : Proper (R x ==> @related_sigT_by_eq A P P R) (@existT A P x) | 10.
Proof.
  cbv [Proper respectful related_sigT_by_eq projT1 projT2].
  exists eq_refl; assumption.
Qed.
