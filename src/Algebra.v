Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.Decidable.

Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Require Coq.setoid_ring.Field_theory.
Require Crypto.Tactics.Algebra_syntax.Nsatz.
Require Coq.Numbers.Natural.Peano.NPeano.

Local Close Scope nat_scope. Local Close Scope type_scope. Local Close Scope core_scope.

Module Import ModuloCoq8485.
  Import NPeano Nat.
  Infix "mod" := modulo.
End ModuloCoq8485.

Section Algebra.
  Context {T:Type} {eq:T->T->Prop}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.

  Section SingleOperation.
    Context {op:T->T->T}.

    Class is_associative := { associative : forall x y z, op x (op y z) = op (op x y) z }.

    Context {id:T}.

    Class is_left_identity := { left_identity : forall x, op id x = x }.
    Class is_right_identity := { right_identity : forall x, op x id = x }.

    Class monoid :=
      {
        monoid_is_associative : is_associative;
        monoid_is_left_identity : is_left_identity;
        monoid_is_right_identity : is_right_identity;

        monoid_op_Proper: Proper (respectful eq (respectful eq eq)) op;
        monoid_Equivalence : Equivalence eq
      }.
    Global Existing Instance monoid_is_associative.
    Global Existing Instance monoid_is_left_identity.
    Global Existing Instance monoid_is_right_identity.
    Global Existing Instance monoid_Equivalence.
    Global Existing Instance monoid_op_Proper.

    Context {inv:T->T}.
    Class is_left_inverse := { left_inverse : forall x, op (inv x) x = id }.
    Class is_right_inverse := { right_inverse : forall x, op x (inv x) = id }.

    Class group :=
      {
        group_monoid : monoid;
        group_is_left_inverse : is_left_inverse;
        group_is_right_inverse : is_right_inverse;

        group_inv_Proper: Proper (respectful eq eq) inv
      }.
    Global Existing Instance group_monoid.
    Global Existing Instance group_is_left_inverse.
    Global Existing Instance group_is_right_inverse.
    Global Existing Instance group_inv_Proper.

    Class is_commutative := { commutative : forall x y, op x y = op y x }.

    Record abelian_group :=
      {
        abelian_group_group : group;
        abelian_group_is_commutative : is_commutative
      }.
    Existing Class abelian_group.
    Global Existing Instance abelian_group_group.
    Global Existing Instance abelian_group_is_commutative.
  End SingleOperation.

  Section AddMul.
    Context {zero one:T}. Local Notation "0" := zero. Local Notation "1" := one.
    Context {opp:T->T}. Local Notation "- x" := (opp x).
    Context {add:T->T->T} {sub:T->T->T} {mul:T->T->T}.
    Local Infix "+" := add. Local Infix "-" := sub. Local Infix "*" := mul.

    Class is_left_distributive := { left_distributive : forall a b c, a * (b + c) =  a * b + a * c }.
    Class is_right_distributive := { right_distributive : forall a b c, (b + c) * a = b * a + c * a }.


    Class ring :=
      {
        ring_abelian_group_add : abelian_group (op:=add) (id:=zero) (inv:=opp);
        ring_monoid_mul : monoid (op:=mul) (id:=one);
        ring_is_left_distributive : is_left_distributive;
        ring_is_right_distributive : is_right_distributive;

        ring_sub_definition : forall x y, x - y = x + opp y;

        ring_mul_Proper : Proper (respectful eq (respectful eq eq)) mul;
        ring_sub_Proper : Proper(respectful eq (respectful eq eq)) sub
      }.
    Global Existing Instance ring_abelian_group_add.
    Global Existing Instance ring_monoid_mul.
    Global Existing Instance ring_is_left_distributive.
    Global Existing Instance ring_is_right_distributive.
    Global Existing Instance ring_mul_Proper.
    Global Existing Instance ring_sub_Proper.

    Class commutative_ring :=
      {
        commutative_ring_ring : ring;
        commutative_ring_is_commutative : is_commutative (op:=mul)
      }.
    Global Existing Instance commutative_ring_ring.
    Global Existing Instance commutative_ring_is_commutative.

    Class is_zero_product_zero_factor :=
      { zero_product_zero_factor : forall x y, x*y = 0 -> x = 0 \/ y = 0 }.

    Class is_zero_neq_one := { zero_neq_one : zero <> one }.

    Class integral_domain :=
      {
        integral_domain_commutative_ring : commutative_ring;
        integral_domain_is_zero_product_zero_factor : is_zero_product_zero_factor;
        integral_domain_is_zero_neq_one : is_zero_neq_one
      }.
    Global Existing Instance integral_domain_commutative_ring.
    Global Existing Instance integral_domain_is_zero_product_zero_factor.
    Global Existing Instance integral_domain_is_zero_neq_one.

    Context {inv:T->T} {div:T->T->T}.
    Class is_left_multiplicative_inverse := { left_multiplicative_inverse : forall x, x<>0 -> (inv x) * x = 1 }.

    Class field :=
      {
        field_commutative_ring : commutative_ring;
        field_is_left_multiplicative_inverse : is_left_multiplicative_inverse;
        field_is_zero_neq_one : is_zero_neq_one;

        field_div_definition : forall x y , div x y = x * inv y;

        field_inv_Proper : Proper (respectful eq eq) inv;
        field_div_Proper : Proper (respectful eq (respectful eq eq)) div
      }.
    Global Existing Instance field_commutative_ring.
    Global Existing Instance field_is_left_multiplicative_inverse.
    Global Existing Instance field_is_zero_neq_one.
    Global Existing Instance field_inv_Proper.
    Global Existing Instance field_div_Proper.
  End AddMul.
End Algebra.

Section ZeroNeqOne.
  Context {T eq zero one} `{@is_zero_neq_one T eq zero one} `{Equivalence T eq}.

  Lemma one_neq_zero : not (eq one zero).
  Proof.
    intro HH; symmetry in HH. auto using zero_neq_one.
  Qed.
End ZeroNeqOne.

Module Monoid.
  Section Monoid.
    Context {T eq op id} {monoid:@monoid T eq op id}.
    Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "*" := op.
    Local Infix "=" := eq : eq_scope.
    Local Open Scope eq_scope.

    Lemma cancel_right z iz (Hinv:op z iz = id) :
      forall x y, x * z = y * z <-> x = y.
    Proof.
      split; intros.
      { assert (op (op x z) iz = op (op y z) iz) as Hcut by (f_equiv; assumption).
        rewrite <-associative in Hcut.
        rewrite <-!associative, !Hinv, !right_identity in Hcut; exact Hcut. }
      { f_equiv; assumption. }
    Qed.

    Lemma cancel_left z iz (Hinv:op iz z = id) :
      forall x y, z * x = z * y <-> x = y.
    Proof.
      split; intros.
      { assert (op iz (op z x) = op iz (op z y)) as Hcut by (f_equiv; assumption).
        rewrite !associative, !Hinv, !left_identity in Hcut; exact Hcut. }
      { f_equiv; assumption. }
    Qed.

    Lemma inv_inv x ix iix : ix*x = id -> iix*ix = id -> iix = x.
    Proof.
      intros Hi Hii.
      assert (H:op iix id = op iix (op ix x)) by (rewrite Hi; reflexivity).
      rewrite associative, Hii, left_identity, right_identity in H; exact H.
    Qed.

    Lemma inv_op x y ix iy : ix*x = id -> iy*y = id -> (iy*ix)*(x*y) =id.
    Proof.
      intros Hx Hy.
      cut (iy * (ix*x) * y = id); try intro H.
      { rewrite <-!associative; rewrite <-!associative in H; exact H. }
      rewrite Hx, right_identity, Hy. reflexivity.
    Qed.

  End Monoid.

  Section Homomorphism.
    Context {T  EQ OP ID} {monoidT:  @monoid T  EQ OP ID }.
    Context {T' eq op id} {monoidT': @monoid T' eq op id }.
    Context {phi:T->T'}.
    Local Infix "=" := eq. Local Infix "=" := eq : type_scope.
    Class is_homomorphism :=
      {
        homomorphism : forall a b,  phi (OP a b) = op (phi a) (phi b);

        is_homomorphism_phi_proper : Proper (respectful EQ eq) phi
      }.
    Global Existing Instance is_homomorphism_phi_proper.
  End Homomorphism.
End Monoid.

Module ScalarMult.
  Section ScalarMultProperties.
    Context {G eq add zero} `{monoidG:@monoid G eq add zero}.
    Context {mul:nat->G->G}.
    Local Infix "=" := eq : type_scope. Local Infix "=" := eq.
    Local Infix "+" := add. Local Infix "*" := mul.
    Class is_scalarmult :=
      {
        scalarmult_0_l : forall P, 0 * P = zero;
        scalarmult_S_l : forall n P, S n * P = P + n * P;

        scalarmult_Proper : Proper (Logic.eq==>eq==>eq) mul
      }.
    Global Existing Instance scalarmult_Proper.
    Context `{mul_is_scalarmult:is_scalarmult}.

    Fixpoint scalarmult_ref (n:nat) (P:G) {struct n} :=
      match n with
      | O => zero
      | S n' => add P (scalarmult_ref n' P)
      end.

    Global Instance Proper_scalarmult_ref : Proper (Logic.eq==>eq==>eq) scalarmult_ref.
    Proof.
      repeat intro; subst.
      match goal with [n:nat |- _ ] => induction n; simpl @scalarmult_ref; [reflexivity|] end.
      repeat match goal with [H:_ |- _ ] => rewrite H end; reflexivity.
    Qed.

    Lemma scalarmult_ext : forall n P, mul n P = scalarmult_ref n P.
      induction n; simpl @scalarmult_ref; intros; rewrite <-?IHn; (apply scalarmult_0_l || apply scalarmult_S_l).
    Qed.

    Lemma scalarmult_1_l : forall P, 1*P = P.
    Proof. intros. rewrite scalarmult_S_l, scalarmult_0_l, right_identity; reflexivity. Qed.

    Lemma scalarmult_add_l : forall (n m:nat) (P:G), ((n + m)%nat * P = n * P + m * P).
    Proof.
      induction n; intros;
        rewrite ?scalarmult_0_l, ?scalarmult_S_l, ?plus_Sn_m, ?plus_O_n, ?scalarmult_S_l, ?left_identity, <-?associative, <-?IHn; reflexivity.
    Qed.

    Lemma scalarmult_zero_r : forall m, m * zero = zero.
    Proof. induction m; rewrite ?scalarmult_S_l, ?scalarmult_0_l, ?left_identity, ?IHm; try reflexivity. Qed.

    Lemma scalarmult_assoc : forall (n m : nat) P, n * (m * P) = (m * n)%nat * P.
    Proof.
      induction n; intros.
      { rewrite <-mult_n_O, !scalarmult_0_l. reflexivity. }
      { rewrite scalarmult_S_l, <-mult_n_Sm, <-Plus.plus_comm, scalarmult_add_l.
        rewrite IHn. reflexivity. }
    Qed.

    Lemma scalarmult_times_order : forall l B, l*B = zero -> forall n, (l * n) * B = zero.
    Proof. intros ? ? Hl ?. rewrite <-scalarmult_assoc, Hl, scalarmult_zero_r. reflexivity. Qed.

    Lemma scalarmult_mod_order : forall l B, l <> 0%nat -> l*B = zero -> forall n, n mod l * B = n * B.
    Proof.
      intros ? ? Hnz Hmod ?.
      rewrite (NPeano.Nat.div_mod n l Hnz) at 2.
      rewrite scalarmult_add_l, scalarmult_times_order, left_identity by auto. reflexivity.
    Qed.
  End ScalarMultProperties.

  Section ScalarMultHomomorphism.
      Context {G EQ ADD ZERO} {monoidG:@monoid G EQ ADD ZERO}.
      Context {H eq add zero} {monoidH:@monoid H eq add zero}.
      Local Infix "=" := eq : type_scope. Local Infix "=" := eq : eq_scope.
      Context {MUL} {MUL_is_scalarmult:@is_scalarmult G EQ ADD ZERO MUL }.
      Context {mul} {mul_is_scalarmult:@is_scalarmult H eq add zero mul }.
      Context {phi} {homom:@Monoid.is_homomorphism G EQ ADD H eq add phi}.
      Context (phi_ZERO:phi ZERO = zero).

      Lemma homomorphism_scalarmult : forall n P, phi (MUL n P) = mul n (phi P).
      Proof.
        setoid_rewrite scalarmult_ext.
        induction n; intros; simpl; rewrite ?Monoid.homomorphism, ?IHn; easy.
      Qed.
  End ScalarMultHomomorphism.

  Global Instance scalarmult_ref_is_scalarmult {G eq add zero} `{@monoid G eq add zero}
    : @is_scalarmult G eq add zero (@scalarmult_ref G add zero).
  Proof. split; try exact _; intros; reflexivity. Qed.
End ScalarMult.

Module Group.
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
        { rewrite !scalarmult_0_l, Group.inv_id; reflexivity. }
        { rewrite <-NPeano.Nat.add_1_l, Plus.plus_comm at 1.
          rewrite scalarmult_add_l, scalarmult_1_l, Group.inv_op, scalarmult_S_l, Group.cancel_left; eauto. }
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
End Group.

Require Coq.nsatz.Nsatz.

Ltac dropAlgebraSyntax :=
  cbv beta delta [
      Algebra_syntax.zero
        Algebra_syntax.one
        Algebra_syntax.addition
        Algebra_syntax.multiplication
        Algebra_syntax.subtraction
        Algebra_syntax.opposite
        Algebra_syntax.equality
        Algebra_syntax.bracket
        Algebra_syntax.power
        ] in *.

Ltac dropRingSyntax :=
  dropAlgebraSyntax;
  cbv beta delta [
      Ncring.zero_notation
        Ncring.one_notation
        Ncring.add_notation
        Ncring.mul_notation
        Ncring.sub_notation
        Ncring.opp_notation
        Ncring.eq_notation
    ] in *.

Module Ring.
  Section Ring.
    Context {T eq zero one opp add sub mul} `{@ring T eq zero one opp add sub mul}.
    Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := zero. Local Notation "1" := one.
    Local Infix "+" := add. Local Infix "-" := sub. Local Infix "*" := mul.

    Lemma mul_0_l : forall x, 0 * x = 0.
    Proof.
      intros.
      assert (0*x = 0*x) as Hx by reflexivity.
      rewrite <-(right_identity 0), right_distributive in Hx at 1.
      assert (0*x + 0*x - 0*x = 0*x - 0*x) as Hxx by (f_equiv; exact Hx).
      rewrite !ring_sub_definition, <-associative, right_inverse, right_identity in Hxx; exact Hxx.
    Qed.

    Lemma mul_0_r : forall x, x * 0 = 0.
    Proof.
      intros.
      assert (x*0 = x*0) as Hx by reflexivity.
      rewrite <-(left_identity 0), left_distributive in Hx at 1.
      assert (opp (x*0) + (x*0 + x*0)  = opp (x*0) + x*0) as Hxx by (f_equiv; exact Hx).
      rewrite associative, left_inverse, left_identity in Hxx; exact Hxx.
    Qed.

    Lemma sub_0_l x : 0 - x = opp x.
    Proof. rewrite ring_sub_definition. rewrite left_identity. reflexivity. Qed.

    Lemma mul_opp_r x y : x * opp y = opp (x * y).
    Proof.
      assert (Ho:x*(opp y) + x*y = 0)
        by (rewrite <-left_distributive, left_inverse, mul_0_r; reflexivity).
      rewrite <-(left_identity (opp (x*y))), <-Ho; clear Ho.
      rewrite <-!associative, right_inverse, right_identity; reflexivity.
    Qed.

    Lemma mul_opp_l x y : opp x * y = opp (x * y).
    Proof.
      assert (Ho:opp x*y + x*y = 0)
        by (rewrite <-right_distributive, left_inverse, mul_0_l; reflexivity).
      rewrite <-(left_identity (opp (x*y))), <-Ho; clear Ho.
      rewrite <-!associative, right_inverse, right_identity; reflexivity.
    Qed.

    Definition opp_nonzero_nonzero : forall x, x <> 0 -> opp x <> 0 := Group.inv_nonzero_nonzero.

    Global Instance is_left_distributive_sub : is_left_distributive (eq:=eq)(add:=sub)(mul:=mul).
    Proof.
      split; intros. rewrite !ring_sub_definition, left_distributive.
      eapply Group.cancel_left, mul_opp_r.
    Qed.

    Global Instance is_right_distributive_sub : is_right_distributive (eq:=eq)(add:=sub)(mul:=mul).
    Proof.
      split; intros. rewrite !ring_sub_definition, right_distributive.
      eapply Group.cancel_left, mul_opp_l.
    Qed.

    Lemma neq_sub_neq_zero x y (Hxy:x<>y) : x-y <> 0.
    Proof.
      intro Hsub. apply Hxy. rewrite <-(left_identity y), <-Hsub, ring_sub_definition.
      rewrite <-associative, left_inverse, right_identity. reflexivity.
    Qed.

    Lemma zero_product_iff_zero_factor {Hzpzf:@is_zero_product_zero_factor T eq zero mul} :
      forall x y : T, eq (mul x y) zero <-> eq x zero \/ eq y zero.
    Proof.
      split; eauto using zero_product_zero_factor; [].
      intros [Hz|Hz]; rewrite Hz; eauto using mul_0_l, mul_0_r.
    Qed.

    Lemma nonzero_product_iff_nonzero_factor {Hzpzf:@is_zero_product_zero_factor T eq zero mul} :
      forall x y : T, not (eq (mul x y) zero) <-> (not (eq x zero) /\ not (eq y zero)).
    Proof. intros; rewrite zero_product_iff_zero_factor; tauto. Qed.

    Lemma nonzero_hypothesis_to_goal {Hzpzf:@is_zero_product_zero_factor T eq zero mul} :
      forall x y : T, (not (eq x zero) -> eq y zero) <-> (eq (mul x y) zero).
    Proof. intros; rewrite zero_product_iff_zero_factor; tauto. Qed.

    Global Instance Ncring_Ring_ops : @Ncring.Ring_ops T zero one add mul sub opp eq.
    Global Instance Ncring_Ring : @Ncring.Ring T zero one add mul sub opp eq Ncring_Ring_ops.
    Proof.
      split; dropRingSyntax; eauto using left_identity, right_identity, commutative, associative, right_inverse, left_distributive, right_distributive, ring_sub_definition with core typeclass_instances.
      - (* TODO: why does [eauto using @left_identity with typeclass_instances] not work? *)
        eapply @left_identity; eauto with typeclass_instances.
      - eapply @right_identity; eauto with typeclass_instances.
      - eapply associative.
      - intros; eapply right_distributive.
      - intros; eapply left_distributive.
    Qed.
  End Ring.

  Section Homomorphism.
    Context {R EQ ZERO ONE OPP ADD SUB MUL} `{@ring R EQ ZERO ONE OPP ADD SUB MUL}.
    Context {S eq zero one opp add sub mul} `{@ring S eq zero one opp add sub mul}.
    Context {phi:R->S}.
    Local Infix "=" := eq. Local Infix "=" := eq : type_scope.

    Class is_homomorphism :=
      {
        homomorphism_is_homomorphism : Monoid.is_homomorphism (phi:=phi) (OP:=ADD) (op:=add) (EQ:=EQ) (eq:=eq);
        homomorphism_mul : forall x y, phi (MUL x y) = mul (phi x) (phi y);
        homomorphism_one : phi ONE = one
      }.
    Global Existing Instance homomorphism_is_homomorphism.

    Context `{is_homomorphism}.

    Lemma homomorphism_add : forall x y,  phi (ADD x y) = add (phi x) (phi y).
    Proof. apply Monoid.homomorphism. Qed.

    Definition homomorphism_opp : forall x,  phi (OPP x) = opp (phi x) :=
      (Group.homomorphism_inv (INV:=OPP) (inv:=opp)).

    Lemma homomorphism_sub : forall x y, phi (SUB x y) = sub (phi x) (phi y).
    Proof.
      intros.
      rewrite !ring_sub_definition, Monoid.homomorphism, homomorphism_opp. reflexivity.
    Qed.
  End Homomorphism.

  Lemma isomorphism_to_subring_ring
        {T EQ ZERO ONE OPP ADD SUB MUL}
        {Equivalence_EQ: @Equivalence T EQ} {eq_dec: forall x y, {EQ x y} + {~ EQ x y} }
        {Proper_OPP:Proper(EQ==>EQ)OPP}
        {Proper_ADD:Proper(EQ==>EQ==>EQ)ADD}
        {Proper_SUB:Proper(EQ==>EQ==>EQ)SUB}
        {Proper_MUL:Proper(EQ==>EQ==>EQ)MUL}
        {R eq zero one opp add sub mul} {ringR:@ring R eq zero one opp add sub mul}
        {phi}
        {eq_phi_EQ: forall x y, eq (phi x) (phi y) -> EQ x y}
        {phi_opp : forall a, eq (phi (OPP a)) (opp (phi a))}
        {phi_add : forall a b, eq (phi (ADD a b)) (add (phi a) (phi b))}
        {phi_sub : forall a b, eq (phi (SUB a b)) (sub (phi a) (phi b))}
        {phi_mul : forall a b, eq (phi (MUL a b)) (mul (phi a) (phi b))}
        {phi_zero : eq (phi ZERO) zero}
        {phi_one : eq (phi ONE) one}
    : @ring T EQ ZERO ONE OPP ADD SUB MUL.
  Proof.
    repeat split; eauto with core typeclass_instances; intros;
      eapply eq_phi_EQ;
      repeat rewrite ?phi_opp, ?phi_add, ?phi_sub, ?phi_mul, ?phi_inv, ?phi_zero, ?phi_one;
      auto using (associative (op := add)), (commutative (op := add)), (left_identity (op := add)), (right_identity (op := add)),
                 (associative (op := mul)), (commutative (op := add)), (left_identity (op := mul)), (right_identity (op := mul)),
                 left_inverse, right_inverse, (left_distributive (add := add)), (right_distributive (add := add)), ring_sub_definition.
  Qed.

  Section TacticSupportCommutative.
    Context {T eq zero one opp add sub mul} `{@commutative_ring T eq zero one opp add sub mul}.

    Global Instance Cring_Cring_commutative_ring :
      @Cring.Cring T zero one add mul sub opp eq Ring.Ncring_Ring_ops Ring.Ncring_Ring.
    Proof. unfold Cring.Cring; intros; dropRingSyntax. eapply commutative. Qed.

   Lemma ring_theory_for_stdlib_tactic : Ring_theory.ring_theory zero one add mul sub opp eq.
   Proof.
     constructor; intros. (* TODO(automation): make [auto] do this? *)
     - apply left_identity.
     - apply commutative.
     - apply associative.
     - apply left_identity.
     - apply commutative.
     - apply associative.
     - apply right_distributive.
     - apply ring_sub_definition.
     - apply right_inverse.
   Qed.
  End TacticSupportCommutative.
End Ring.

Module IntegralDomain.
  Section IntegralDomain.
    Context {T eq zero one opp add sub mul} `{@integral_domain T eq zero one opp add sub mul}.

    Lemma nonzero_product_iff_nonzero_factors :
      forall x y : T, ~ eq (mul x y) zero <-> ~ eq x zero /\ ~ eq y zero.
    Proof. setoid_rewrite Ring.zero_product_iff_zero_factor; intuition. Qed.

    Global Instance Integral_domain :
      @Integral_domain.Integral_domain T zero one add mul sub opp eq Ring.Ncring_Ring_ops
                                       Ring.Ncring_Ring Ring.Cring_Cring_commutative_ring.
    Proof. split; dropRingSyntax; eauto using zero_product_zero_factor, one_neq_zero. Qed.
  End IntegralDomain.
End IntegralDomain.

Require Coq.setoid_ring.Field_theory.
Module Field.
  Section Field.
    Context {T eq zero one opp add mul sub inv div} `{@field T eq zero one opp add sub mul inv div}.
    Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := zero. Local Notation "1" := one.
    Local Infix "+" := add. Local Infix "*" := mul.

    Lemma right_multiplicative_inverse : forall x : T, ~ eq x zero -> eq (mul x (inv x)) one.
    Proof.
      intros. rewrite commutative. auto using left_multiplicative_inverse.
    Qed.

    Lemma inv_unique x ix : ix * x = one -> ix = inv x.
    Proof.
      intro Hix.
      assert (ix*x*inv x = inv x).
      - rewrite Hix, left_identity; reflexivity.
      - rewrite <-associative, right_multiplicative_inverse, right_identity in H0; trivial.
        intro eq_x_0. rewrite eq_x_0, Ring.mul_0_r in Hix.
        apply zero_neq_one. assumption.
    Qed.

    Lemma div_one x : div x one = x.
    Proof.
      rewrite field_div_definition.
      rewrite <-(inv_unique 1 1); apply monoid_is_right_identity.
    Qed.

    Lemma mul_cancel_l_iff : forall x y, y <> 0 ->
                                         (x * y = y <-> x = one).
    Proof.
      intros.
      split; intros.
      + rewrite <-(right_multiplicative_inverse y) by assumption.
        rewrite <-H1 at 1; rewrite <-associative.
        rewrite right_multiplicative_inverse by assumption.
        rewrite right_identity.
        reflexivity.
      + rewrite H1; apply left_identity.
    Qed.

    Lemma field_theory_for_stdlib_tactic : Field_theory.field_theory 0 1 add mul sub opp div inv eq.
    Proof.
      constructor.
      { apply Ring.ring_theory_for_stdlib_tactic. }
      { intro H01. symmetry in H01. auto using zero_neq_one. }
      { apply field_div_definition. }
      { apply left_multiplicative_inverse. }
    Qed.

    Context (eq_dec:DecidableRel eq).

    Global Instance is_mul_nonzero_nonzero : @is_zero_product_zero_factor T eq 0 mul.
    Proof.
      split. intros x y Hxy.
      eapply not_not; try typeclasses eauto; []; intuition idtac; eapply zero_neq_one.
      transitivity ((inv y * (inv x * x)) * y).
      - rewrite <-!associative, Hxy, !Ring.mul_0_r; reflexivity.
      - rewrite left_multiplicative_inverse, right_identity, left_multiplicative_inverse by trivial.
        reflexivity.
    Qed.

    Global Instance integral_domain : @integral_domain T eq zero one opp add sub mul.
    Proof.
      split; auto using field_commutative_ring, field_is_zero_neq_one, is_mul_nonzero_nonzero.
    Qed.
  End Field.

  Lemma isomorphism_to_subfield_field
        {T EQ ZERO ONE OPP ADD SUB MUL INV DIV}
        {Equivalence_EQ: @Equivalence T EQ}
        {Proper_OPP:Proper(EQ==>EQ)OPP}
        {Proper_ADD:Proper(EQ==>EQ==>EQ)ADD}
        {Proper_SUB:Proper(EQ==>EQ==>EQ)SUB}
        {Proper_MUL:Proper(EQ==>EQ==>EQ)MUL}
        {Proper_INV:Proper(EQ==>EQ)INV}
        {Proper_DIV:Proper(EQ==>EQ==>EQ)DIV}
        {R eq zero one opp add sub mul inv div} {fieldR:@field R eq zero one opp add sub mul inv div}
        {phi}
        {eq_phi_EQ: forall x y, eq (phi x) (phi y) -> EQ x y}
        {neq_zero_one : (not (EQ ZERO ONE))}
        {phi_opp : forall a, eq (phi (OPP a)) (opp (phi a))}
        {phi_add : forall a b, eq (phi (ADD a b)) (add (phi a) (phi b))}
        {phi_sub : forall a b, eq (phi (SUB a b)) (sub (phi a) (phi b))}
        {phi_mul : forall a b, eq (phi (MUL a b)) (mul (phi a) (phi b))}
        {phi_inv : forall a, eq (phi (INV a)) (inv (phi a))}
        {phi_div : forall a b, eq (phi (DIV a b)) (div (phi a) (phi b))}
        {phi_zero : eq (phi ZERO) zero}
        {phi_one : eq (phi ONE) one}
    : @field T EQ ZERO ONE OPP ADD SUB MUL INV DIV.
  Proof.
    repeat split; eauto with core typeclass_instances; intros;
      eapply eq_phi_EQ;
      repeat rewrite ?phi_opp, ?phi_add, ?phi_sub, ?phi_mul, ?phi_inv, ?phi_zero, ?phi_one, ?phi_inv, ?phi_div;
      auto using (associative (op := add)), (commutative (op := add)), (left_identity (op := add)), (right_identity (op := add)),
                 (associative (op := mul)), (commutative (op := mul)), (left_identity (op := mul)), (right_identity (op := mul)),
                 left_inverse, right_inverse, (left_distributive (add := add)), (right_distributive (add := add)),
                 ring_sub_definition, field_div_definition.
      apply left_multiplicative_inverse; rewrite <-phi_zero; auto.
  Qed.

  Lemma Proper_ext : forall {A} (f g : A -> A) eq, Equivalence eq ->
    (forall x, eq (g x) (f x)) -> Proper (eq==>eq) f -> Proper (eq==>eq) g.
  Proof.
    repeat intro.
    transitivity (f x); auto.
    transitivity (f y); auto.
    symmetry; auto.
  Qed.

  Lemma Proper_ext2 : forall {A} (f g : A -> A -> A) eq, Equivalence eq ->
    (forall x y, eq (g x y) (f x y)) -> Proper (eq==>eq ==>eq) f -> Proper (eq==>eq==>eq) g.
  Proof.
    repeat intro.
    transitivity (f x x0); auto.
    transitivity (f y y0); match goal with H : Proper _ f |- _=> try apply H end; auto.
    symmetry; auto.
  Qed.

  Lemma equivalent_operations_field
        {T EQ ZERO ONE OPP ADD SUB MUL INV DIV}
        {EQ_equivalence : Equivalence EQ}
        {zero one opp add sub mul inv div}
        {fieldR:@field T EQ zero one opp add sub mul inv div}
        {EQ_opp : forall a, EQ (OPP a) (opp a)}
        {EQ_inv : forall a, EQ (INV a) (inv a)}
        {EQ_add : forall a b, EQ (ADD a b) (add a b)}
        {EQ_sub : forall a b, EQ (SUB a b) (sub a b)}
        {EQ_mul : forall a b, EQ (MUL a b) (mul a b)}
        {EQ_div : forall a b, EQ (DIV a b) (div a b)}
        {EQ_zero : EQ ZERO zero}
        {EQ_one : EQ ONE one}
    : @field T EQ ZERO ONE OPP ADD SUB MUL INV DIV.
  Proof.
    repeat split; eauto with core typeclass_instances; intros;
      repeat rewrite ?EQ_opp, ?EQ_inv, ?EQ_add, ?EQ_sub, ?EQ_mul, ?EQ_div, ?EQ_zero, ?EQ_one;
      auto using (associative (op := add)), (commutative (op := add)), (left_identity (op := add)), (right_identity (op := add)),
                 (associative (op := mul)), (commutative (op := mul)), (left_identity (op := mul)), (right_identity (op := mul)),
                 left_inverse, right_inverse, (left_distributive (add := add)), (right_distributive (add := add)),
                 ring_sub_definition, field_div_definition;
      try solve [(eapply Proper_ext2 || eapply Proper_ext);
        eauto using group_inv_Proper, monoid_op_Proper, ring_mul_Proper, ring_sub_Proper,
          field_inv_Proper, field_div_Proper].
      + apply left_multiplicative_inverse.
        symmetry in EQ_zero. rewrite EQ_zero. assumption.
      + eapply field_is_zero_neq_one; eauto.
  Qed.

  Section Homomorphism.
    Context {F EQ ZERO ONE OPP ADD MUL SUB INV DIV} `{@field F EQ ZERO ONE OPP ADD SUB MUL INV DIV}.
    Context {K eq zero one opp add mul sub inv div} `{@field K eq zero one opp add sub mul inv div}.
    Context {phi:F->K}.
    Local Infix "=" := eq. Local Infix "=" := eq : type_scope.
    Context `{@Ring.is_homomorphism F EQ ONE ADD MUL K eq one add mul phi}.

    Lemma homomorphism_multiplicative_inverse
      : forall x, not (EQ x ZERO)
      -> phi (INV x) = inv (phi x).
    Proof.
      intros.
      eapply inv_unique.
      rewrite <-Ring.homomorphism_mul.
      rewrite left_multiplicative_inverse; auto using Ring.homomorphism_one.
    Qed.

    Lemma homomorphism_multiplicative_inverse_complete
          { EQ_dec : DecidableRel EQ }
       : forall x, (EQ x ZERO -> phi (INV x) = inv (phi x))
       -> phi (INV x) = inv (phi x).
    Proof.
      intros x ?; destruct (dec (EQ x ZERO)); auto using homomorphism_multiplicative_inverse.
    Qed.

    Lemma homomorphism_div
      : forall x y, not (EQ y ZERO)
      -> phi (DIV x y) = div (phi x) (phi y).
    Proof.
      intros. rewrite !field_div_definition.
      rewrite Ring.homomorphism_mul, homomorphism_multiplicative_inverse;
        (eauto || reflexivity).
    Qed.

    Lemma homomorphism_div_complete
          { EQ_dec : DecidableRel EQ }
      : forall x y, (EQ y ZERO -> phi (INV y) = inv (phi y))
      -> phi (DIV x y) = div (phi x) (phi y).
    Proof.
      intros. rewrite !field_div_definition.
      rewrite Ring.homomorphism_mul, homomorphism_multiplicative_inverse_complete;
        (eauto || reflexivity).
    Qed.
  End Homomorphism.

  Section Homomorphism_rev.
    Context {F EQ ZERO ONE OPP ADD SUB MUL INV DIV} {fieldF:@field F EQ ZERO ONE OPP ADD SUB MUL INV DIV}.
    Context {H} {eq : H -> H -> Prop} {zero one : H} {opp : H -> H} {add sub mul : H -> H -> H} {inv : H -> H} {div : H -> H -> H}.
    Context {phi:F->H} {phi':H->F}.
    Local Infix "=" := EQ. Local Infix "=" := EQ : type_scope.
    Context (phi'_phi_id : forall A, phi' (phi A) = A)
            (phi'_eq : forall a b, EQ (phi' a) (phi' b) <-> eq a b)
            {phi'_zero : phi' zero = ZERO}
            {phi'_one : phi' one = ONE}
            {phi'_opp : forall a, phi' (opp a) = OPP (phi' a)}
            (phi'_add : forall a b, phi' (add a b) = ADD (phi' a) (phi' b))
            (phi'_sub : forall a b, phi' (sub a b) = SUB (phi' a) (phi' b))
            (phi'_mul : forall a b, phi' (mul a b) = MUL (phi' a) (phi' b))
            {phi'_inv : forall a, phi' (inv a) = INV (phi' a)}
            (phi'_div : forall a b, phi' (div a b) = DIV (phi' a) (phi' b)).

    Lemma field_and_homomorphism_from_redundant_representation
      : @field H eq zero one opp add sub mul inv div
        /\ @Ring.is_homomorphism F EQ ONE ADD MUL H eq one add mul phi
        /\ @Ring.is_homomorphism H eq one add mul F EQ ONE ADD MUL phi'.
    Proof.
      repeat match goal with
             | [ H : field |- _ ] => destruct H; try clear H
             | [ H : commutative_ring |- _ ] => destruct H; try clear H
             | [ H : ring |- _ ] => destruct H; try clear H
             | [ H : abelian_group |- _ ] => destruct H; try clear H
             | [ H : group |- _ ] => destruct H; try clear H
             | [ H : monoid |- _ ] => destruct H; try clear H
             | [ H : is_commutative |- _ ] => destruct H; try clear H
             | [ H : is_left_multiplicative_inverse |- _ ] => destruct H; try clear H
             | [ H : is_left_distributive |- _ ] => destruct H; try clear H
             | [ H : is_right_distributive |- _ ] => destruct H; try clear H
             | [ H : is_zero_neq_one |- _ ] => destruct H; try clear H
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
             | [ H : (~eq _ _)%type |- _ ] => pose proof (fun pf => H (proj1 (@phi'_eq _ _) pf)); clear H
             | [ H : EQ _ _ |- _ ] => rewrite H
             | _ => progress erewrite ?phi'_zero, ?phi'_one, ?phi'_opp, ?phi'_add, ?phi'_sub, ?phi'_mul, ?phi'_inv, ?phi'_div, ?phi'_phi_id by reflexivity
             | [ H : _ |- _ ] => progress erewrite ?phi'_zero, ?phi'_one, ?phi'_opp, ?phi'_add, ?phi'_sub, ?phi'_mul, ?phi'_inv, ?phi'_div, ?phi'_phi_id in H by reflexivity
             | _ => solve [ eauto ]
             end.
    Qed.
  End Homomorphism_rev.
End Field.

(** Tactics *)

Ltac nsatz := Algebra_syntax.Nsatz.nsatz; dropRingSyntax.
Ltac nsatz_contradict := Algebra_syntax.Nsatz.nsatz_contradict; dropRingSyntax.

(*** Tactics for manipulating field equations *)
Require Import Coq.setoid_ring.Field_tac.

(** Convention: These tactics put the original goal first, and all
    goals for non-zero side-conditions after that.  (Exception:
    [field_simplify_eq in], which is silly.  *)

Ltac guess_field :=
  match goal with
  | |- ?eq _ _ =>  constr:(_:field (eq:=eq))
  | |- not (?eq _ _) =>  constr:(_:field (eq:=eq))
  | [H: ?eq _ _ |- _ ] =>  constr:(_:field (eq:=eq))
  | [H: not (?eq _ _) |- _] =>  constr:(_:field (eq:=eq))
  end.

Ltac field_nonzero_mul_split :=
  repeat match goal with
         | [ H : ?R (?mul ?x ?y) ?zero |- _ ]
           => apply zero_product_zero_factor in H; destruct H
         | [ |- not (?R (?mul ?x ?y) ?zero) ]
           => apply IntegralDomain.nonzero_product_iff_nonzero_factors; split
         | [ H : not (?R (?mul ?x ?y) ?zero) |- _ ]
           => apply IntegralDomain.nonzero_product_iff_nonzero_factors in H; destruct H
         end.

Ltac field_simplify_eq_if_div :=
  let fld := guess_field in
  lazymatch type of fld with
    field (div:=?div) =>
    lazymatch goal with
    | |- appcontext[div] => field_simplify_eq
    | |- _ => idtac
    end
  end.

(** We jump through some hoops to ensure that the side-conditions come late *)
Ltac field_simplify_eq_if_div_in_cycled_side_condition_order H :=
  let fld := guess_field in
  lazymatch type of fld with
    field (div:=?div) =>
    lazymatch type of H with
    | appcontext[div] => field_simplify_eq in H
    | _ => idtac
    end
  end.

Ltac field_simplify_eq_if_div_in H :=
  side_conditions_before_to_side_conditions_after
    field_simplify_eq_if_div_in_cycled_side_condition_order
    H.

(** Now we have more conservative versions that don't simplify non-division structure. *)
Ltac deduplicate_nonfraction_pieces mul :=
  repeat match goal with
         | [ x0 := ?v, x1 := context[?v] |- _ ]
             => progress change v with x0 in x1
         | [ x := mul ?a ?b |- _ ]
           => not is_var a;
              let a' := fresh x in
              pose a as a'; change a with a' in x
         | [ x := mul ?a ?b |- _ ]
           => not is_var b;
              let b' := fresh x in
              pose b as b'; change b with b' in x
         | [ x0 := ?v, x1 := ?v |- _ ]
           => change x1 with x0 in *; clear x1
         | [ x := ?v |- _ ]
           => is_var v; subst x
         | [ x0 := mul ?a ?b, x1 := mul ?a ?b' |- _ ]
           => subst x0 x1
         | [ x0 := mul ?a ?b, x1 := mul ?a' ?b |- _ ]
           => subst x0 x1
         end.

Ltac set_nonfraction_pieces_on T eq zero opp add sub mul inv div cont :=
  idtac;
  let one_arg_recr :=
      fun op v
      => set_nonfraction_pieces_on
           v eq zero opp add sub mul inv div
           ltac:(fun x => cont (op x)) in
  let two_arg_recr :=
      fun op v0 v1
      => set_nonfraction_pieces_on
           v0 eq zero opp add sub mul inv div
           ltac:(fun x
                 =>
                   set_nonfraction_pieces_on
                     v1 eq zero opp add sub mul inv div
                     ltac:(fun y => cont (op x y))) in
  lazymatch T with
  | eq ?x ?y => two_arg_recr eq x y
  | appcontext[div]
    => lazymatch T with
       | opp ?x => one_arg_recr opp x
       | inv ?x => one_arg_recr inv x
       | add ?x ?y => two_arg_recr add x y
       | sub ?x ?y => two_arg_recr sub x y
       | mul ?x ?y => two_arg_recr mul x y
       | div ?x ?y => two_arg_recr div x y
       | _ => idtac
       end
  | _ => let x := fresh "x" in
         pose T as x;
         cont x
  end.
Ltac set_nonfraction_pieces_in H :=
  idtac;
  let fld := guess_field in
  lazymatch type of fld with
  | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => let T := type of H in
       set_nonfraction_pieces_on
         T eq zero opp add sub mul inv div
         ltac:(fun T' => change T' in H);
       deduplicate_nonfraction_pieces mul
  end.
Ltac set_nonfraction_pieces :=
  idtac;
  let fld := guess_field in
  lazymatch type of fld with
  | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => let T := get_goal in
       set_nonfraction_pieces_on
         T eq zero opp add sub mul inv div
         ltac:(fun T' => change T');
       deduplicate_nonfraction_pieces mul
  end.
Ltac default_common_denominator_nonzero_tac :=
  repeat apply conj;
  try first [ assumption
            | intro; field_nonzero_mul_split; tauto ].
Ltac common_denominator_in H :=
  idtac;
  let fld := guess_field in
  let div := lazymatch type of fld with
             | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
               => div
             end in
  lazymatch type of H with
  | appcontext[div]
    => set_nonfraction_pieces_in H;
       field_simplify_eq_if_div_in H;
       [
       | default_common_denominator_nonzero_tac.. ];
       repeat match goal with H := _ |- _ => subst H end
  | ?T => fail 0 "no division in" H ":" T
  end.
Ltac common_denominator :=
  idtac;
  let fld := guess_field in
  let div := lazymatch type of fld with
             | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
               => div
             end in
  lazymatch goal with
  | |- appcontext[div]
    => set_nonfraction_pieces;
       field_simplify_eq_if_div;
       [
       | default_common_denominator_nonzero_tac.. ];
       repeat match goal with H := _ |- _ => subst H end
  | |- ?G
    => fail 0 "no division in goal" G
  end.
Ltac common_denominator_inequality_in H :=
  let HT := type of H in
  lazymatch HT with
  | not (?R _ _) => idtac
  | (?R _ _ -> False)%type => idtac
  | _ => fail 0 "Not an inequality" H ":" HT
  end;
  let HTT := type of HT in
  let HT' := fresh in
  evar (HT' : HTT);
  let H' := fresh in
  rename H into H';
  cut (not HT'); subst HT';
  [ intro H; clear H'
  | let H'' := fresh in
    intro H''; apply H'; common_denominator; [ eexact H'' | .. ] ].
Ltac common_denominator_inequality :=
  let G := get_goal in
  lazymatch G with
  | not (?R _ _) => idtac
  | (?R _ _ -> False)%type => idtac
  | _ => fail 0 "Not an inequality (goal):" G
  end;
  let GT := type of G in
  let HT' := fresh in
  evar (HT' : GT);
  let H' := fresh in
  assert (H' : not HT'); subst HT';
  [
  | let HG := fresh in
    intros HG; apply H'; common_denominator_in HG; [ eexact HG | .. ] ].

Ltac common_denominator_hyps :=
  try match goal with
      | [H: _ |- _ ]
        => progress common_denominator_in H;
           [ common_denominator_hyps
           | .. ]
      end.

Ltac common_denominator_inequality_hyps :=
  try match goal with
      | [H: _ |- _ ]
        => progress common_denominator_inequality_in H;
           [ common_denominator_inequality_hyps
           | .. ]
      end.

Ltac common_denominator_all :=
  try common_denominator;
  [ try common_denominator_hyps
  | .. ].

Ltac common_denominator_inequality_all :=
  try common_denominator_inequality;
  [ try common_denominator_inequality_hyps
  | .. ].

Ltac common_denominator_equality_inequality_all :=
  common_denominator_all;
  [ common_denominator_inequality_all
  | .. ].

(** [nsatz] for fields *)
Ltac _field_nsatz_prep_goal fld eq :=
  repeat match goal with
         | [ |- not (eq ?x ?y) ] => intro
         | [ |- eq _ _] => idtac
         | _ => exfalso; apply (field_is_zero_neq_one(field:=fld))
         end.
         
Ltac _field_nsatz_prep_inequalities fld eq zero :=
  repeat match goal with
         | [H: not (eq _ _) |- _ ] =>
           lazymatch type of H with
             | not (eq _ zero) => unique pose proof (Field.right_multiplicative_inverse(H:=fld) _ H)
             | not (eq zero _) => unique pose proof (Field.right_multiplicative_inverse(H:=fld) _ (symmetry _ _ H))
             | _ => unique pose proof (Field.right_multiplicative_inverse(H:=fld) _ (Ring.neq_sub_neq_zero _ _ H))
           end
         end.

(* solves all implications between field equalities and field inequalities that are true in all fields (including those without decidable equality) *)
Ltac field_nsatz :=
  let fld := guess_field in 
  let eq := match type of fld with field(eq:=?eq) => eq end in
  let zero := match type of fld with field(zero:=?zero) => zero end in
  _field_nsatz_prep_goal fld eq;
  common_denominator_equality_inequality_all; [|_field_nsatz_prep_goal fld eq..];
  _field_nsatz_prep_inequalities fld eq zero;
  nsatz;
  repeat eapply (proj2 (Ring.nonzero_product_iff_nonzero_factor _ _)); auto. (* nsatz coefficients *)

Inductive field_simplify_done {T} : T -> Type :=
  Field_simplify_done : forall H, field_simplify_done H.

Ltac field_simplify_eq_hyps :=
  repeat match goal with
           [ H: _ |- _ ] =>
           match goal with
           | [ Ha : field_simplify_done H |- _ ] => fail
           | _ => idtac
           end;
           field_simplify_eq in H;
           unique pose proof (Field_simplify_done H)
         end;
  repeat match goal with [ H: field_simplify_done _ |- _] => clear H end.

Ltac field_simplify_eq_all := field_simplify_eq_hyps; try field_simplify_eq.

(** *** Tactics that remove division by rewriting *)
Ltac rewrite_field_div_definition inv :=
  let lem := constr:(field_div_definition (inv:=inv)) in
  let div := lazymatch lem with field_div_definition (div:=?div) => div end in
  repeat match goal with
         | [ |- context[div _ _] ] => rewrite !lem
         | [ H : context[div _ _] |- _ ] => rewrite !lem in H
         end.
Ltac generalize_inv inv :=
  let lem := constr:(left_multiplicative_inverse (inv:=inv)) in
  repeat match goal with
         | [ |- context[inv ?x] ]
           => pose proof (lem x); generalize dependent (inv x); intros
         | [ H : context[inv ?x] |- _ ]
           => pose proof (lem x); generalize dependent (inv x); intros
         end.
Ltac nsatz_strip_fractions_on inv :=
  rewrite_field_div_definition inv; generalize_inv inv; specialize_by_assumption.

Ltac nsatz_strip_fractions_with_eq eq :=
  let F := constr:(_ : field (eq:=eq)) in
  lazymatch type of F with
  | field (inv:=?inv) => nsatz_strip_fractions_on inv
  end.
Ltac nsatz_strip_fractions :=
  match goal with
  | [ |- ?eq ?x ?y ] => nsatz_strip_fractions_with_eq eq
  | [ |- not (?eq ?x ?y) ] => nsatz_strip_fractions_with_eq eq
  | [ |- (?eq ?x ?y -> False)%type ] => nsatz_strip_fractions_with_eq eq
  | [ H : ?eq ?x ?y |- _ ] => nsatz_strip_fractions_with_eq eq
  | [ H : not (?eq ?x ?y) |- _ ] => nsatz_strip_fractions_with_eq eq
  | [ H : (?eq ?x ?y -> False)%type |- _ ] => nsatz_strip_fractions_with_eq eq
  end.

Ltac nsatz_fold_or_intro_not :=
  repeat match goal with
         | [ |- not _ ] => intro
         | [ |- (_ -> _)%type ] => intro
         | [ H : (?X -> False)%type |- _ ]
           => change (not X) in H
         | [ H : ((?X -> False) -> ?T)%type |- _ ]
           => change (not X -> T)%type in H
         end.

Ltac nsatz_final_inequality_to_goal :=
  nsatz_fold_or_intro_not;
  try match goal with
      | [ H : not (?eq ?x ?zero) |- ?eq ?y ?zero ]
        => generalize H; apply (proj2 (Ring.nonzero_hypothesis_to_goal x y))
      | [ H : not (?eq ?x ?zero) |- False ]
        => apply H
      end.

Ltac nsatz_goal_to_canonical :=
  nsatz_fold_or_intro_not;
  try match goal with
      | [ |- ?eq ?x ?y ]
        => apply (Group.move_leftR (eq:=eq)); rewrite <- ring_sub_definition;
           lazymatch goal with
           | [ |- eq _ y ] => fail 0 "should not subtract 0"
           | _ => idtac
           end
      end.

Ltac nsatz_specialize_by_cut_using cont H eq x zero a b :=
  change (not (eq x zero) -> eq a b)%type in H;
  cut (not (eq x zero));
  [ intro; specialize_by_assumption; cont ()
  | clear H ].

Ltac nsatz_specialize_by_cut :=
  specialize_by_assumption;
  match goal with
  | [ H : ((?eq ?x ?zero -> False) -> ?eq ?a ?b)%type |- ?eq _ ?zero ]
    => nsatz_specialize_by_cut_using ltac:(fun _ => nsatz_specialize_by_cut) H eq x zero a b
  | [ H : (not (?eq ?x ?zero) -> ?eq ?a ?b)%type |- ?eq _ ?zero ]
    => nsatz_specialize_by_cut_using ltac:(fun _ => nsatz_specialize_by_cut) H eq x zero a b
  | [ H : ((?eq ?x ?zero -> False) -> ?eq ?a ?b)%type |- False ]
    => nsatz_specialize_by_cut_using ltac:(fun _ => nsatz_specialize_by_cut) H eq x zero a b
  | [ H : (not (?eq ?x ?zero) -> ?eq ?a ?b)%type |- False ]
    => nsatz_specialize_by_cut_using ltac:(fun _ => nsatz_specialize_by_cut) H eq x zero a b
  | _ => idtac
  end.

(** Clear duplicate hypotheses, and hypotheses of the form [R x x] for a reflexive relation [R], and similarly for symmetric relations *)
Ltac clear_algebraic_duplicates_step R :=
  match goal with
  | [ H : R ?x ?x |- _ ]
    => clear H
  end.
Ltac clear_algebraic_duplicates_step_S R :=
  match goal with
  | [ H : R ?x ?y, H' : R ?y ?x |- _ ]
    => clear H
  | [ H : not (R ?x ?y), H' : not (R ?y ?x) |- _ ]
    => clear H
  | [ H : (R ?x ?y -> False)%type, H' : (R ?y ?x -> False)%type |- _ ]
    => clear H
  | [ H : not (R ?x ?y), H' : (R ?y ?x -> False)%type |- _ ]
    => clear H
  end.
Ltac clear_algebraic_duplicates_guarded R :=
  let test_reflexive := constr:(_ : Reflexive R) in
  repeat clear_algebraic_duplicates_step R.
Ltac clear_algebraic_duplicates_guarded_S R :=
  let test_symmetric := constr:(_ : Symmetric R) in
  repeat clear_algebraic_duplicates_step_S R.
Ltac clear_algebraic_duplicates :=
  clear_duplicates;
  repeat match goal with
         | [ H : ?R ?x ?x |- _ ] => progress clear_algebraic_duplicates_guarded R
         | [ H : ?R ?x ?y, H' : ?R ?y ?x |- _ ]
           => progress clear_algebraic_duplicates_guarded_S R
         | [ H : not (?R ?x ?y), H' : not (?R ?y ?x) |- _ ]
           => progress clear_algebraic_duplicates_guarded_S R
         | [ H : not (?R ?x ?y), H' : (?R ?y ?x -> False)%type |- _ ]
           => progress clear_algebraic_duplicates_guarded_S R
         | [ H : (?R ?x ?y -> False)%type, H' : (?R ?y ?x -> False)%type |- _ ]
           => progress clear_algebraic_duplicates_guarded_S R
         end.

(*** Inequalities over fields *)
Ltac assert_expr_by_nsatz H ty :=
  let H' := fresh in
  rename H into H'; assert (H : ty)
    by (try (intro; apply H'); nsatz);
  clear H'.
Ltac test_not_constr_eq_assert_expr_by_nsatz y zero H ty :=
  first [ constr_eq y zero; fail 1 y "is already" zero
        | assert_expr_by_nsatz H ty ].
Ltac canonicalize_field_inequalities_step' eq zero opp add sub :=
  match goal with
  |  [ H : not (eq ?x (opp ?y)) |- _ ]
     => test_not_constr_eq_assert_expr_by_nsatz y zero H (not (eq (add x y) zero))
  |  [ H : (eq ?x (opp ?y) -> False)%type |- _ ]
     => test_not_constr_eq_assert_expr_by_nsatz y zero H (eq (add x y) zero -> False)%type
  |  [ H : not (eq ?x ?y) |- _ ]
     => test_not_constr_eq_assert_expr_by_nsatz y zero H (not (eq (sub x y) zero))
  |  [ H : (eq ?x ?y -> False)%type |- _ ]
     => test_not_constr_eq_assert_expr_by_nsatz y zero H (not (eq (sub x y) zero))
  end.
Ltac canonicalize_field_inequalities' eq zero opp add sub := repeat canonicalize_field_inequalities_step' eq zero opp add sub.
Ltac canonicalize_field_equalities_step' eq zero opp add sub :=
  lazymatch goal with
  |  [ H : eq ?x (opp ?y) |- _ ]
     => test_not_constr_eq_assert_expr_by_nsatz y zero H (eq (add x y) zero)
  |  [ H : eq ?x ?y |- _ ]
     => test_not_constr_eq_assert_expr_by_nsatz y zero H (eq (sub x y) zero)
  end.
Ltac canonicalize_field_equalities' eq zero opp add sub := repeat canonicalize_field_equalities_step' eq zero opp add sub.

(** These are the two user-facing tactics.  They put (in)equalities
    into the form [_ <> 0] / [_ = 0]. *)
Ltac canonicalize_field_inequalities :=
  let fld := guess_field in
  lazymatch type of fld with
  | @field ?F ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => canonicalize_field_inequalities' eq zero opp add sub
  end.
Ltac canonicalize_field_equalities :=
  let fld := guess_field in
  lazymatch type of fld with
  | @field ?F ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => canonicalize_field_equalities' eq zero opp add sub
  end.


(*** Polynomial equations over fields *)

Ltac neq01 :=
  try solve
      [apply zero_neq_one
      |apply Group.zero_neq_opp_one
      |apply one_neq_zero
      |apply Group.opp_one_neq_zero].

Ltac combine_field_inequalities_step :=
  match goal with
  | [ H : not (?R ?x ?zero), H' : not (?R ?x' ?zero) |- _ ]
    => pose proof (proj2 (IntegralDomain.nonzero_product_iff_nonzero_factors x x') (conj H H')); clear H H'
  | [ H : (?X -> False)%type |- _ ]
    => change (not X) in H
  end.

(** First we split apart the equalities so that we can clear
    duplicates; it's easier for us to do this than to give [nsatz] the
    extra work. *)

Ltac split_field_inequalities_step :=
  match goal with
  | [ H : not (?R (?mul ?x ?y) ?zero) |- _ ]
    => apply IntegralDomain.nonzero_product_iff_nonzero_factors in H; destruct H
  end.
Ltac split_field_inequalities :=
  canonicalize_field_inequalities;
  repeat split_field_inequalities_step;
  clear_duplicates.

Ltac combine_field_inequalities :=
  split_field_inequalities;
  repeat combine_field_inequalities_step.
(** Handles field inequalities which can be made by splitting multiplications in the goal and the assumptions *)
Ltac solve_simple_field_inequalities :=
  repeat (apply conj || split_field_inequalities);
  try assumption.
Ltac nsatz_strip_fractions_and_aggregate_inequalities :=
  nsatz_strip_fractions;
  nsatz_goal_to_canonical;
  split_field_inequalities (* this will make solving side conditions easier *);
  nsatz_specialize_by_cut;
  [ combine_field_inequalities; nsatz_final_inequality_to_goal | .. ].
Ltac prensatz_contradict :=
  solve_simple_field_inequalities;
  combine_field_inequalities.
Ltac nsatz_inequality_to_equality :=
  repeat intro;
  match goal with
  | [ H : not (?R ?x ?zero) |- False ] => apply H
  | [ H : (?R ?x ?zero -> False)%type |- False ] => apply H
  end.
(** Clean up tactic handling side-conditions *)
Ltac super_nsatz_post_clean_inequalities :=
  repeat (apply conj || split_field_inequalities);
  try assumption;
  prensatz_contradict; nsatz_inequality_to_equality;
  try nsatz.
Ltac nsatz_equality_to_inequality_by_decide_equality :=
  lazymatch goal with
  | [ H : not (?R _ _) |- ?R _ _ ] => idtac
  | [ H : (?R _ _ -> False)%type |- ?R _ _ ] => idtac
  | [ |- ?R _ _ ] => fail 0 "No hypothesis exists which negates the relation" R
  | [ |- ?G ] => fail 0 "The goal is not a binary relation:" G
  end;
  lazymatch goal with
  | [ |- ?R ?x ?y ]
    => destruct (@dec (R x y) _); [ assumption | exfalso ]
  end.
(** Handles inequalities and fractions *)
Ltac super_nsatz_internal nsatz_alternative :=
  (* [nsatz] gives anomalies on duplicate hypotheses, so we strip them *)
  clear_algebraic_duplicates;
  prensatz_contradict;
  (* Each goal left over by [prensatz_contradict] is separate (and
     there might not be any), so we handle them all separately *)
  [ try common_denominator_equality_inequality_all;
    [ try nsatz_inequality_to_equality;
      try first [ nsatz;
                  (* [nstaz] might leave over side-conditions; we handle them if they are inequalities *)
                  try super_nsatz_post_clean_inequalities
                | nsatz_alternative ]
    | super_nsatz_post_clean_inequalities.. ].. ].

Ltac super_nsatz :=
  super_nsatz_internal
    (* if [nsatz] fails, we try turning the goal equality into an inequality and trying again *)
    ltac:(nsatz_equality_to_inequality_by_decide_equality;
          super_nsatz_internal idtac).

Section ExtraLemmas.
  Context {F eq zero one opp add sub mul inv div} `{F_field:field F eq zero one opp add sub mul inv div} {eq_dec:DecidableRel eq}.
  Local Infix "+" := add. Local Infix "*" := mul. Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "0" := zero. Local Notation "1" := one.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.

  Example _only_two_square_roots_test x y : x * x = y * y -> x <> opp y -> x = y.
  Proof. intros; super_nsatz. Qed.

  Lemma only_two_square_roots' x y : x * x = y * y -> x <> y -> x <> opp y -> False.
  Proof. intros; super_nsatz. Qed.

  Lemma only_two_square_roots x y z : x * x = z -> y * y = z -> x <> y -> x <> opp y -> False.
  Proof.
    intros; setoid_subst z; eauto using only_two_square_roots'.
  Qed.

  Lemma only_two_square_roots'_choice x y : x * x = y * y -> x = y \/ x = opp y.
  Proof.
    intro H.
    destruct (dec (eq x y)); [ left; assumption | right ].
    destruct (dec (eq x (opp y))); [ assumption | exfalso ].
    eapply only_two_square_roots'; eassumption.
  Qed.

  Lemma only_two_square_roots_choice x y z : x * x = z -> y * y = z -> x = y \/ x = opp y.
  Proof.
    intros; setoid_subst z; eauto using only_two_square_roots'_choice.
  Qed.
End ExtraLemmas.

(** We look for hypotheses of the form [x^2 = y^2] and [x^2 = z] together with [y^2 = z], and prove that [x = y] or [x = opp y] *)
Ltac pose_proof_only_two_square_roots x y H eq opp mul :=
  not constr_eq x y;
  lazymatch x with
  | opp ?x' => pose_proof_only_two_square_roots x' y H eq opp mul
  | _
    => lazymatch y with
       | opp ?y' => pose_proof_only_two_square_roots x y' H eq opp mul
       | _
         => match goal with
            | [ H' : eq x y |- _ ]
              => let T := type of H' in fail 1 "The hypothesis" H' "already proves" T
            | [ H' : eq y x |- _ ]
              => let T := type of H' in fail 1 "The hypothesis" H' "already proves" T
            | [ H' : eq x (opp y) |- _ ]
              => let T := type of H' in fail 1 "The hypothesis" H' "already proves" T
            | [ H' : eq y (opp x) |- _ ]
              => let T := type of H' in fail 1 "The hypothesis" H' "already proves" T
            | [ H' : eq (opp x) y |- _ ]
              => let T := type of H' in fail 1 "The hypothesis" H' "already proves" T
            | [ H' : eq (opp y) x |- _ ]
              => let T := type of H' in fail 1 "The hypothesis" H' "already proves" T
            | [ H' : eq (mul x x) (mul y y) |- _ ]
              => pose proof (only_two_square_roots'_choice x y H') as H
            | [ H0 : eq (mul x x) ?z, H1 : eq (mul y y) ?z |- _ ]
              => pose proof (only_two_square_roots_choice x y z H0 H1) as H
            end
       end
  end.
Ltac reduce_only_two_square_roots x y eq opp mul :=
  let H := fresh in
  pose_proof_only_two_square_roots x y H eq opp mul;
  destruct H;
  try setoid_subst y.
Ltac pre_clean_only_two_square_roots :=
  clear_algebraic_duplicates.
(** Remove duplicates; solve goals by contradiction, and, if goals still remain, substitute the square roots *)
Ltac post_clean_only_two_square_roots x y :=
  clear_algebraic_duplicates;
  try (unfold not in *;
       match goal with
       | [ H : (?T -> False)%type, H' : ?T |- _ ] => exfalso; apply H; exact H'
       | [ H : (?R ?x ?x -> False)%type |- _ ] => exfalso; apply H; reflexivity
       end);
  try setoid_subst x; try setoid_subst y.
Ltac only_two_square_roots_step eq opp mul :=
  match goal with
  | [ H : not (eq ?x (opp ?y)) |- _ ]
    (* this one comes first, because it the procedure is asymmetric
       with respect to [x] and [y], and this order is more likely to
       lead to solving goals by contradiction. *)
    => is_var x; is_var y; reduce_only_two_square_roots x y eq opp mul; post_clean_only_two_square_roots x y
  | [ H : eq (mul ?x ?x) (mul ?y ?y) |- _ ]
    => reduce_only_two_square_roots x y eq opp mul; post_clean_only_two_square_roots x y
  | [ H : eq (mul ?x ?x) ?z, H' : eq (mul ?y ?y) ?z |- _ ]
    => reduce_only_two_square_roots x y eq opp mul; post_clean_only_two_square_roots x y
  end.
Ltac only_two_square_roots :=
  pre_clean_only_two_square_roots;
  let fld := guess_field in
  lazymatch type of fld with
  | @field ?F ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => repeat only_two_square_roots_step eq opp mul
  end.

(*** Tactics for ring equations *)
Require Export Coq.setoid_ring.Ring_tac.
Ltac ring_simplify_subterms := tac_on_subterms ltac:(fun t => ring_simplify t).

Ltac ring_simplify_subterms_in_all :=
  reverse_nondep; ring_simplify_subterms; intros.

Create HintDb ring_simplify discriminated.
Create HintDb ring_simplify_subterms discriminated.
Create HintDb ring_simplify_subterms_in_all discriminated.
Hint Extern 1 => progress ring_simplify : ring_simplify.
Hint Extern 1 => progress ring_simplify_subterms : ring_simplify_subterms.
Hint Extern 1 => progress ring_simplify_subterms_in_all : ring_simplify_subterms_in_all.


Section Example.
  Context {F zero one opp add sub mul inv div} {F_field:@field F eq zero one opp add sub mul inv div} {eq_dec : DecidableRel (@eq F)}.
  Local Infix "+" := add. Local Infix "*" := mul. Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "0" := zero. Local Notation "1" := one.

  Add Field _ExampleField : (Field.field_theory_for_stdlib_tactic (T:=F)).

  Example _example_nsatz x y : 1+1 <> 0 -> x + y = 0 -> x - y = 0 -> x = 0.
  Proof. intros. nsatz. Qed.

  Example _example_field_nsatz x y z : y <> 0 -> x/y = z -> z*y + y = x + y.
  Proof. intros. super_nsatz. Qed.

  Example _example_nonzero_nsatz_contradict x y : x * y = 1 -> not (x = 0).
  Proof. intros. intro. nsatz_contradict. Qed.
End Example.

Require Coq.ZArith.ZArith.
Section Z.
  Import ZArith.
  Global Instance ring_Z : @ring Z Logic.eq 0%Z 1%Z Z.opp Z.add Z.sub Z.mul.
  Proof. repeat split; auto using Z.eq_dec with zarith typeclass_instances. Qed.

  Global Instance commutative_ring_Z : @commutative_ring Z Logic.eq 0%Z 1%Z Z.opp Z.add Z.sub Z.mul.
  Proof. eauto using @commutative_ring, @is_commutative, ring_Z with zarith. Qed.

  Global Instance integral_domain_Z : @integral_domain Z Logic.eq 0%Z 1%Z Z.opp Z.add Z.sub Z.mul.
  Proof.
    split.
    { apply commutative_ring_Z. }
    { split. intros. eapply Z.eq_mul_0; assumption. }
    { split. discriminate. }
  Qed.

  Example _example_nonzero_nsatz_contradict_Z x y : Z.mul x y = (Zpos xH) -> not (x = Z0).
  Proof. intros. intro. nsatz_contradict. Qed.
End Z.
