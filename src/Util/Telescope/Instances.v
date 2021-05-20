Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions Coq.Classes.Morphisms.
Require Import Crypto.Util.Telescope.Core.

Module Export Telescope.
  Definition flattenT_R_lift {X : Type} {t : Telescope} (P : forall A, relation A -> Prop)
             (R : relation X)
             (H : P _ R)
             (H_forall : forall A T (R' : forall a : A, relation (T a)),
                           (forall a : A, P _ (R' a))
                           -> P _ (forall_relation R'))
  : P _ (@flattenT_R_relation X R t).
  Proof.
    repeat intro; induction t; simpl in *.
    { assumption. }
    { eauto with nocore. }
  Defined.

  Global Instance flattenT_R_Reflexive {t X R} {_ : @Reflexive X R}
  : Reflexive (@flattenT_R_relation X R t).
  Proof.
  refine (flattenT_R_lift (@Reflexive) R _ _).
  lazy; eauto with nocore.
  Defined.

  Global Instance flattenT_R_Symmetric {t X R} {_ : @Symmetric X R}
  : Symmetric (@flattenT_R_relation X R t).
  Proof.
  refine (flattenT_R_lift (@Symmetric) R _ _).
  lazy; eauto with nocore.
  Defined.

  Global Instance flattenT_R_Transitive {t X R} {_ : @Transitive X R}
  : Transitive (@flattenT_R_relation X R t).
  Proof.
  refine (flattenT_R_lift (@Transitive) R _ _).
  lazy; eauto with nocore.
  Defined.

  Global Instance flattenT_R_relation_flip_impl_Proper {t X R}
         {H : Proper (Basics.flip R ==> R ==> Basics.flip Basics.impl)
                     R}
  : Proper (Basics.flip (flattenT_R_relation R) ==> flattenT_R_relation R ==> Basics.flip Basics.impl)
           (@flattenT_R_relation X R t).
  Proof.
  refine (@flattenT_R_lift X t (fun A R => Proper (Basics.flip R ==> R ==> Basics.flip Basics.impl) R) _ H _).
    unfold Proper, respectful, Basics.flip, Basics.impl, forall_relation in *; intros.
    eauto with nocore.
  Defined.

  Global Instance flattenT_eq_Reflexive {t : Telescope} {X : Type}
  : Reflexive (@flattenT_eq X t)
    := flattenT_R_Reflexive.

  Global Instance flattenT_eq_Symmetric {t : Telescope} {X : Type}
  : Symmetric (@flattenT_eq X t)
    := flattenT_R_Symmetric.

  Global Instance flattenT_eq_Transitive {t : Telescope} {X : Type}
  : Transitive (@flattenT_eq X t)
    := flattenT_R_Transitive.

  Global Instance flatten_forall_eq_relation_Reflexive {t P}
  : Reflexive (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ reflexivity | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_Symmetric {t P}
  : Symmetric (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ symmetry; assumption | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_Transitive {t P}
  : Transitive (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ etransitivity; eassumption | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_Reflexive {t P}
  : Reflexive (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Reflexive.

  Global Instance flatten_forall_eq_Symmetric {t P}
  : Symmetric (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Symmetric.

  Global Instance flatten_forall_eq_Transitive {t P}
  : Transitive (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Transitive.

  Global Instance flatten_forall_eq_relation_with_assumption_Reflexive {t P Q}
  : Reflexive (@flatten_forall_eq_relation_with_assumption t P Q).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ reflexivity | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_with_assumption_Symmetric {t P Q}
  : Symmetric (@flatten_forall_eq_relation_with_assumption t P Q).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ symmetry; eauto with nocore | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_with_assumption_Transitive {t P Q}
  : Transitive (@flatten_forall_eq_relation_with_assumption t P Q).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ etransitivity; eauto with nocore | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_with_assumption_Reflexive {t P Q}
  : Reflexive (@flatten_forall_eq_with_assumption t P Q)
    := flatten_forall_eq_relation_with_assumption_Reflexive.

  Global Instance flatten_forall_eq_with_assumption_Symmetric {t P Q}
  : Symmetric (@flatten_forall_eq_with_assumption t P Q)
    := flatten_forall_eq_relation_with_assumption_Symmetric.

  Global Instance flatten_forall_eq_with_assumption_Transitive {t P Q}
  : Transitive (@flatten_forall_eq_with_assumption t P Q)
    := flatten_forall_eq_relation_with_assumption_Transitive.

  Lemma flatten_append_forall_Proper {B P Q}
  : forall f g,
      @flatten_forall_eq B P f g
      -> @flatten_append_forall B P Q f
      -> @flatten_append_forall B P Q g.
  Proof.
    induction B; simpl in *; eauto with nocore.
    intros; subst; assumption.
  Defined.

  Global Instance flattenT_unapply_Proper {t X}
  : Proper (pointwise_relation _ eq ==> flattenT_eq)
           (@flattenT_unapply t X).
  Proof.
    repeat intro; unfold pointwise_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flattenT_apply_Proper {t X}
  : Proper (flattenT_eq ==> pointwise_relation _ eq)
           (@flattenT_apply t X).
  Proof.
    repeat intro; unfold pointwise_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_unapply_Proper {t P}
  : Proper (forall_relation (fun _ => eq) ==> flatten_forall_eq)
           (@flatten_forall_unapply t P).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_apply_Proper {t P}
  : Proper (flatten_forall_eq ==> forall_relation (fun _ => eq))
           (@flatten_forall_apply t P).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_eq_rect_Proper {t P Q H}
  : Proper (flatten_forall_eq ==> flatten_forall_eq)
           (@flatten_forall_eq_rect t P Q H).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore;
    subst; simpl; reflexivity.
  Defined.
End Telescope.
