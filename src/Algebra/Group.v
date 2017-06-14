Require Import Coq.Classes.Morphisms Crypto.Util.Relations (*Crypto.Util.Tactics*).
Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.Monoid.

Section BasicProperties.
  Context {T eq op id inv} `{@group T eq op id inv}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "*" := op.
  Local Infix "=" := eq : eq_scope.
  Local Open Scope eq_scope.

  Lemma cancel_left : forall z x y, z*x = z*y <-> x = y.
  Proof using Type*. eauto using Monoid.cancel_left, left_inverse. Qed.
  Lemma cancel_right : forall z x y, x*z = y*z <-> x = y.
  Proof using Type*. eauto using Monoid.cancel_right, right_inverse. Qed.
  Lemma inv_inv x : inv(inv(x)) = x.
  Proof using Type*. eauto using Monoid.inv_inv, left_inverse. Qed.
  Lemma inv_op_ext x y : (inv y*inv x)*(x*y) =id.
  Proof using Type*. eauto using Monoid.inv_op, left_inverse. Qed.

  Lemma inv_unique x ix : ix * x = id -> ix = inv x.
  Proof using Type*.
    intro Hix.
    cut (ix*x*inv x = inv x).
    - rewrite <-associative, right_inverse, right_identity; trivial.
    - rewrite Hix, left_identity; reflexivity.
  Qed.

  Lemma inv_bijective x y : inv x = inv y <-> x = y.
  Proof using Type*.
    split; intro Hi; rewrite ?Hi; try reflexivity.
    assert (Hii:inv (inv x) = inv (inv y)) by (rewrite Hi; reflexivity).
    rewrite 2inv_inv in Hii; exact Hii.
  Qed.

  Lemma inv_op x y : inv (x*y) = inv y*inv x.
  Proof using Type*.
    symmetry. etransitivity.
    2:eapply inv_unique.
    2:eapply inv_op_ext.
    reflexivity.
  Qed.

  Lemma inv_id : inv id = id.
  Proof using Type*. symmetry. eapply inv_unique, left_identity. Qed.

  Lemma inv_id_iff x : inv x = id <-> x = id.
  Proof using Type*.
    split; intro Hi; rewrite ?Hi, ?inv_id; try reflexivity.
    rewrite <-inv_id, inv_bijective in Hi; exact Hi.
  Qed.

  Lemma inv_nonzero_nonzero x : x <> id <-> inv x <> id.
  Proof using Type*. setoid_rewrite inv_id_iff; reflexivity. Qed.

  Lemma eq_r_opp_r_inv a b c : a = op c (inv b) <-> op a b = c.
  Proof using Type*.
    split; intro Hx; rewrite Hx || rewrite <-Hx;
      rewrite <-!associative, ?left_inverse, ?right_inverse, right_identity;
      reflexivity.
  Qed.

  Section ZeroNeqOne.
    Context {one} `{is_zero_neq_one T eq id one}.
    Lemma opp_one_neq_zero : inv one <> id.
    Proof using Type*. setoid_rewrite inv_id_iff. exact one_neq_zero. Qed.
    Lemma zero_neq_opp_one : id <> inv one.
    Proof using Type*. intro Hx. symmetry in Hx. eauto using opp_one_neq_zero. Qed.
  End ZeroNeqOne.
End BasicProperties.

Section Homomorphism.
  Context {G EQ OP ID INV} {groupG:@group G EQ OP ID INV}.
  Context {H eq op id inv} {groupH:@group H eq op id inv}.
  Context {phi:G->H}`{homom:@Monoid.is_homomorphism G EQ OP H eq op phi}.
  Local Infix "=" := eq. Local Infix "=" := eq : type_scope.

  Lemma homomorphism_id : phi ID = id.
  Proof using Type*.
    assert (Hii: op (phi ID) (phi ID) = op (phi ID) id) by
        (rewrite <- Monoid.homomorphism, left_identity, right_identity; reflexivity).
    rewrite cancel_left in Hii; exact Hii.
  Qed.

  Lemma homomorphism_inv x : phi (INV x) = inv (phi x).
  Proof using Type*.
    apply inv_unique.
    rewrite <- Monoid.homomorphism, left_inverse, homomorphism_id; reflexivity.
  Qed.
End Homomorphism.

Section GroupByIsomorphism.
  Context {G} {EQ:G->G->Prop} {OP:G->G->G} {ID:G} {INV:G->G}.
  Context {H} {eq : H -> H -> Prop} {op : H -> H -> H} {id : H} {inv : H -> H}.
  Context {phi:G->H} {phi':H->G}.
  Local Infix "=" := EQ. Local Infix "=" := EQ : type_scope.

  Class isomorphic_groups :=
    {
      isomorphic_groups_group_G :> @group G EQ OP ID INV;
      isomorphic_groups_group_H :> @group H eq op id inv;
      isomorphic_groups_hom_GH :> @Monoid.is_homomorphism G EQ OP H eq op phi;
      isomorphic_groups_hom_HG :> @Monoid.is_homomorphism H eq op G EQ OP phi';
    }.

  Lemma group_by_isomorphism
        (groupG:@group G EQ OP ID INV)
        (phi'_phi_id : forall A, phi' (phi A) = A)
        (phi'_eq : forall a b, EQ (phi' a) (phi' b) <-> eq a b)
        (phi'_op : forall a b, phi' (op a b) = OP (phi' a) (phi' b))
        (phi'_inv : forall a, phi' (inv a) = INV (phi' a))
        (phi'_id : phi' id = ID)
    : isomorphic_groups.
  Proof using Type*.
    repeat match goal with
           | [ H : _/\_ |- _ ] => destruct H; try clear H
           | [ H : commutative_group |- _ ] => destruct H; try clear H
           | [ H : group |- _ ] => destruct H; try clear H
           | [ H : monoid |- _ ] => destruct H; try clear H
           | [ H : is_commutative |- _ ] => destruct H; try clear H
           | [ H : is_associative |- _ ] => destruct H; try clear H
           | [ H : is_left_identity |- _ ] => destruct H; try clear H
           | [ H : is_right_identity |- _ ] => destruct H; try clear H
           | [ H : Equivalence _ |- _ ] => destruct H; try clear H
           | [ H : is_left_inverse |- _ ] => destruct H; try clear H
           | [ H : is_right_inverse |- _ ] => destruct H; try clear H
           | _ => intro
           | _ => split
           | [ H : eq _ _ |- _ ] => apply phi'_eq in H
           | [ |- eq _ _ ] => apply phi'_eq
           | [ H : EQ _ _ |- _ ] => rewrite H
           | _ => progress erewrite ?phi'_op, ?phi'_inv, ?phi'_id, ?phi'_phi_id by reflexivity
           | [ H : _ |- _ ] => progress erewrite ?phi'_op, ?phi'_inv, ?phi'_id in H by reflexivity
           | _ => solve [ eauto ]
           end.
  Qed.
End GroupByIsomorphism.

Section CommutativeGroupByIsomorphism.
  Context {G} {EQ:G->G->Prop} {OP:G->G->G} {ID:G} {INV:G->G}.
  Context {H} {eq : H -> H -> Prop} {op : H -> H -> H} {id : H} {inv : H -> H}.
  Context {phi:G->H} {phi':H->G}.
  Local Infix "=" := EQ. Local Infix "=" := EQ : type_scope.

  Class isomorphic_commutative_groups :=
    {
      isomorphic_commutative_groups_group_G :> @commutative_group G EQ OP ID INV;
      isomorphic_commutative_groups_group_H :> @commutative_group H eq op id inv;
      isomorphic_commutative_groups_hom_GH :> @Monoid.is_homomorphism G EQ OP H eq op phi;
      isomorphic_commutative_groups_hom_HG :> @Monoid.is_homomorphism H eq op G EQ OP phi';
    }.

  Lemma commutative_group_by_isomorphism
        (groupG:@commutative_group G EQ OP ID INV)
        (phi'_phi_id : forall A, phi' (phi A) = A)
        (phi'_eq : forall a b, EQ (phi' a) (phi' b) <-> eq a b)
        (phi'_op : forall a b, phi' (op a b) = OP (phi' a) (phi' b))
        (phi'_inv : forall a, phi' (inv a) = INV (phi' a))
        (phi'_id : phi' id = ID)
    : isomorphic_commutative_groups.
  Proof using Type*.
    repeat match goal with
           | [ H : _/\_ |- _ ] => destruct H; try clear H
           | [ H : commutative_group |- _ ] => destruct H; try clear H
           | [ H : group |- _ ] => destruct H; try clear H
           | [ H : monoid |- _ ] => destruct H; try clear H
           | [ H : is_commutative |- _ ] => destruct H; try clear H
           | [ H : is_associative |- _ ] => destruct H; try clear H
           | [ H : is_left_identity |- _ ] => destruct H; try clear H
           | [ H : is_right_identity |- _ ] => destruct H; try clear H
           | [ H : Equivalence _ |- _ ] => destruct H; try clear H
           | [ H : is_left_inverse |- _ ] => destruct H; try clear H
           | [ H : is_right_inverse |- _ ] => destruct H; try clear H
           | _ => intro
           | _ => split
           | [ H : eq _ _ |- _ ] => apply phi'_eq in H
           | [ |- eq _ _ ] => apply phi'_eq
           | [ H : EQ _ _ |- _ ] => rewrite H
           | _ => progress erewrite ?phi'_op, ?phi'_inv, ?phi'_id, ?phi'_phi_id by reflexivity
           | [ H : _ |- _ ] => progress erewrite ?phi'_op, ?phi'_inv, ?phi'_id in H by reflexivity
           | _ => solve [ eauto ]
           end.
  Qed.
End CommutativeGroupByIsomorphism.
