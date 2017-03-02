Require Import Coq.Classes.Morphisms.
Require Import Crypto.Algebra Crypto.Algebra.Monoid Crypto.Algebra.ScalarMult.

Section BasicProperties.
  Context {T eq op id inv} `{@group T eq op id inv}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "*" := op.
  Local Infix "=" := eq : eq_scope.
  Local Open Scope eq_scope.

  Lemma cancel_left : forall z x y, z*x = z*y <-> x = y.
  Proof. eauto using Monoid.cancel_left, left_inverse. Qed.
  Lemma cancel_right : forall z x y, x*z = y*z <-> x = y.
  Proof. eauto using Monoid.cancel_right, right_inverse. Qed.
  Lemma inv_inv x : inv(inv(x)) = x.
  Proof. eauto using Monoid.inv_inv, left_inverse. Qed.
  Lemma inv_op_ext x y : (inv y*inv x)*(x*y) =id.
  Proof. eauto using Monoid.inv_op, left_inverse. Qed.

  Lemma inv_unique x ix : ix * x = id -> ix = inv x.
  Proof.
    intro Hix.
    cut (ix*x*inv x = inv x).
    - rewrite <-associative, right_inverse, right_identity; trivial.
    - rewrite Hix, left_identity; reflexivity.
  Qed.

  Lemma move_leftL x y : inv y * x = id -> x = y.
  Proof.
    intro; rewrite <- (inv_inv y), (inv_unique x (inv y)), inv_inv by assumption; reflexivity.
  Qed.

  Lemma move_leftR x y : x * inv y = id -> x = y.
  Proof.
    intro; rewrite (inv_unique (inv y) x), inv_inv by assumption; reflexivity.
  Qed.

  Lemma move_rightR x y : id = y * inv x -> x = y.
  Proof.
    intro; rewrite <- (inv_inv x), (inv_unique (inv x) y), inv_inv by (symmetry; assumption); reflexivity.
  Qed.

  Lemma move_rightL x y : id = inv x * y -> x = y.
  Proof.
    intro; rewrite <- (inv_inv x), (inv_unique y (inv x)), inv_inv by (symmetry; assumption); reflexivity.
  Qed.

  Lemma inv_op x y : inv (x*y) = inv y*inv x.
  Proof.
    symmetry. etransitivity.
    2:eapply inv_unique.
    2:eapply inv_op_ext.
    reflexivity.
  Qed.

  Lemma inv_id : inv id = id.
  Proof. symmetry. eapply inv_unique, left_identity. Qed.

  Lemma inv_nonzero_nonzero : forall x, x <> id -> inv x <> id.
  Proof.
    intros ? Hx Ho.
    assert (Hxo: x * inv x = id) by (rewrite right_inverse; reflexivity).
    rewrite Ho, right_identity in Hxo. intuition.
  Qed.

  Lemma neq_inv_nonzero : forall x, x <> inv x -> x <> id.
  Proof.
    intros ? Hx Hi; apply Hx.
    rewrite Hi.
    symmetry; apply inv_id.
  Qed.

  Lemma inv_neq_nonzero : forall x, inv x <> x -> x <> id.
  Proof.
    intros ? Hx Hi; apply Hx.
    rewrite Hi.
    apply inv_id.
  Qed.

  Lemma inv_zero_zero : forall x, inv x = id -> x = id.
  Proof.
    intros.
    rewrite <-inv_id, <-H0.
    symmetry; apply inv_inv.
  Qed.

  Lemma eq_r_opp_r_inv a b c : a = op c (inv b) <-> op a b = c.
  Proof.
    split; intro Hx; rewrite Hx || rewrite <-Hx;
      rewrite <-!associative, ?left_inverse, ?right_inverse, right_identity;
      reflexivity.
  Qed.

  Section ZeroNeqOne.
    Context {one} `{is_zero_neq_one T eq id one}.
    Lemma opp_one_neq_zero : inv one <> id.
    Proof. apply inv_nonzero_nonzero, one_neq_zero. Qed.
    Lemma zero_neq_opp_one : id <> inv one.
    Proof. intro Hx. symmetry in Hx. eauto using opp_one_neq_zero. Qed.
  End ZeroNeqOne.
End BasicProperties.

Section Homomorphism.
  Context {G EQ OP ID INV} {groupG:@group G EQ OP ID INV}.
  Context {H eq op id inv} {groupH:@group H eq op id inv}.
  Context {phi:G->H}`{homom:@Monoid.is_homomorphism G EQ OP H eq op phi}.
  Local Infix "=" := eq. Local Infix "=" := eq : type_scope.

  Lemma homomorphism_id : phi ID = id.
  Proof.
    assert (Hii: op (phi ID) (phi ID) = op (phi ID) id) by
        (rewrite <- Monoid.homomorphism, left_identity, right_identity; reflexivity).
    rewrite cancel_left in Hii; exact Hii.
  Qed.

  Lemma homomorphism_inv x : phi (INV x) = inv (phi x).
  Proof.
    apply inv_unique.
    rewrite <- Monoid.homomorphism, left_inverse, homomorphism_id; reflexivity.
  Qed.

  Section ScalarMultHomomorphism.
    Context {MUL} {MUL_is_scalarmult:@ScalarMult.is_scalarmult G EQ OP ID MUL }.
    Context {mul} {mul_is_scalarmult:@ScalarMult.is_scalarmult H eq op id mul }.
    Lemma homomorphism_scalarmult n P : phi (MUL n P) = mul n (phi P).
    Proof. eapply ScalarMult.homomorphism_scalarmult, homomorphism_id. Qed.

    Import ScalarMult.
    Lemma opp_mul : forall n P, inv (mul n P) = mul n (inv P).
    Proof.
      induction n; intros.
      { rewrite !scalarmult_0_l, inv_id; reflexivity. }
      { rewrite <-NPeano.Nat.add_1_l, Plus.plus_comm at 1.
        rewrite scalarmult_add_l, scalarmult_1_l, inv_op, scalarmult_S_l, cancel_left; eauto. }
    Qed.
  End ScalarMultHomomorphism.
End Homomorphism.

Section Homomorphism_rev.
  Context {G EQ OP ID INV} {groupG:@group G EQ OP ID INV}.
  Context {H} {eq : H -> H -> Prop} {op : H -> H -> H} {id : H} {inv : H -> H}.
  Context {phi:G->H} {phi':H->G}.
  Local Infix "=" := EQ. Local Infix "=" := EQ : type_scope.
  Context (phi'_phi_id : forall A, phi' (phi A) = A)
          (phi'_eq : forall a b, EQ (phi' a) (phi' b) <-> eq a b)
          (phi'_op : forall a b, phi' (op a b) = OP (phi' a) (phi' b))
          {phi'_inv : forall a, phi' (inv a) = INV (phi' a)}
          {phi'_id : phi' id = ID}.

  Local Instance group_from_redundant_representation
    : @group H eq op id inv.
  Proof.
    repeat match goal with
           | [ H : group |- _ ] => destruct H; try clear H
           | [ H : monoid |- _ ] => destruct H; try clear H
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
           | _ => progress erewrite ?phi'_op, ?phi'_inv, ?phi'_id by reflexivity
           | [ H : _ |- _ ] => progress erewrite ?phi'_op, ?phi'_inv, ?phi'_id in H by reflexivity
           | _ => solve [ eauto ]
           end.
  Qed.

  Definition homomorphism_from_redundant_representation
    : @Monoid.is_homomorphism G EQ OP H eq op phi.
  Proof.
    split; repeat intro; apply phi'_eq; rewrite ?phi'_op, ?phi'_phi_id; easy.
  Qed.
End Homomorphism_rev.

Section GroupByHomomorphism.
  Lemma surjective_homomorphism_from_group
        {G EQ OP ID INV} {groupG:@group G EQ OP ID INV}
        {H eq op id inv}
        {Equivalence_eq: @Equivalence H eq} {eq_dec: forall x y, {eq x y} + {~ eq x y} }
        {Proper_op:Proper(eq==>eq==>eq)op}
        {Proper_inv:Proper(eq==>eq)inv}
        {phi iph} {Proper_phi:Proper(EQ==>eq)phi} {Proper_iph:Proper(eq==>EQ)iph}
        {surj:forall h, eq (phi (iph h)) h}
        {phi_op : forall a b, eq (phi (OP a b)) (op (phi a) (phi b))}
        {phi_inv : forall a, eq (phi (INV a)) (inv (phi a))}
        {phi_id : eq (phi ID) id}
  : @group H eq op id inv.
  Proof.
    repeat split; eauto with core typeclass_instances; intros;
      repeat match goal with
               |- context[?x] =>
               match goal with
               | |- context[iph x] => fail 1
               | _ => unify x id; fail 1
               | _ => is_var x; rewrite <- (surj x)
               end
             end;
      repeat rewrite <-?phi_op, <-?phi_inv, <-?phi_id;
      f_equiv; auto using associative, left_identity, right_identity, left_inverse, right_inverse.
  Qed.

  Lemma isomorphism_to_subgroup_group
        {G EQ OP ID INV}
        {Equivalence_EQ: @Equivalence G EQ} {eq_dec: forall x y, {EQ x y} + {~ EQ x y} }
        {Proper_OP:Proper(EQ==>EQ==>EQ)OP}
        {Proper_INV:Proper(EQ==>EQ)INV}
        {H eq op id inv} {groupG:@group H eq op id inv}
        {phi}
        {eq_phi_EQ: forall x y, eq (phi x) (phi y) -> EQ x y}
        {phi_op : forall a b, eq (phi (OP a b)) (op (phi a) (phi b))}
        {phi_inv : forall a, eq (phi (INV a)) (inv (phi a))}
        {phi_id : eq (phi ID) id}
    : @group G EQ OP ID INV.
  Proof.
    repeat split; eauto with core typeclass_instances; intros;
      eapply eq_phi_EQ;
      repeat rewrite ?phi_op, ?phi_inv, ?phi_id;
      auto using associative, left_identity, right_identity, left_inverse, right_inverse.
  Qed.
End GroupByHomomorphism.

Section HomomorphismComposition.
  Context {G EQ OP ID INV} {groupG:@group G EQ OP ID INV}.
  Context {H eq op id inv} {groupH:@group H eq op id inv}.
  Context {K eqK opK idK invK} {groupK:@group K eqK opK idK invK}.
  Context {phi:G->H} {phi':H->K}
          {Hphi:@Monoid.is_homomorphism G EQ OP H eq op phi}
          {Hphi':@Monoid.is_homomorphism H eq op K eqK opK phi'}.
  Lemma is_homomorphism_compose
        {phi'':G->K}
        (Hphi'' : forall x, eqK (phi' (phi x)) (phi'' x))
    : @Monoid.is_homomorphism G EQ OP K eqK opK phi''.
  Proof.
    split; repeat intro; rewrite <- !Hphi''.
    { rewrite !Monoid.homomorphism; reflexivity. }
    { apply Hphi', Hphi; assumption. }
  Qed.

  Global Instance is_homomorphism_compose_refl
    : @Monoid.is_homomorphism G EQ OP K eqK opK (fun x => phi' (phi x))
    := is_homomorphism_compose (fun x => reflexivity _).
End HomomorphismComposition.