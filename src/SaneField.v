Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Close Scope nat_scope. Close Scope type_scope. Close Scope core_scope.

Section Algebra.
  Context {T:Type} {eq:T->T->Prop}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.

  Class is_eq_dec := { eq_dec : forall x y : T, {x=y} + {x<>y} }.

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
        monoid_is_right_identity : is_right_identity
      }.
    Global Existing Instance monoid_is_associative.
    Global Existing Instance monoid_is_left_identity.
    Global Existing Instance monoid_is_right_identity.

    Context {inv:T->T}.
    Class is_left_inverse := { left_inverse : forall x, op (inv x) x = id }.
    Class is_right_inverse := { right_inverse : forall x, op x (inv x) = id }.

    Class group :=
      {
        group_monoid : monoid;
        group_is_left_inverse : is_left_inverse;
        group_is_right_inverse : is_right_inverse;

        group_Equivalence : Equivalence eq;
        group_is_eq_dec : is_eq_dec;
        group_op_Proper: Proper (respectful eq (respectful eq eq)) op;
        group_inv_Proper: Proper (respectful eq eq) inv
      }.
    Global Existing Instance group_monoid.
    Global Existing Instance group_is_left_inverse.
    Global Existing Instance group_is_right_inverse.
    Global Existing Instance group_Equivalence.
    Global Existing Instance group_is_eq_dec.
    Global Existing Instance group_op_Proper.
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

    Class is_mul_nonzero_nonzero := { mul_nonzero_nonzero : forall x y, x<>0 -> y<>0 -> x*y<>0 }.

    Class is_zero_neq_one := { zero_neq_one : zero <> one }.
    
    Class integral_domain :=
      {
        integral_domain_commutative_ring : commutative_ring;
        integral_domain_is_mul_nonzero_nonzero : is_mul_nonzero_nonzero;
        integral_domain_is_zero_neq_one : is_zero_neq_one
      }.
    Global Existing Instance integral_domain_commutative_ring.
    Global Existing Instance integral_domain_is_mul_nonzero_nonzero.
    Global Existing Instance integral_domain_is_zero_neq_one.

    Context {inv:T->T} {div:T->T->T}.
    Class is_left_multiplicative_inverse := { left_multiplicative_inverse : forall x, x<>0 -> (inv x) * x = 1 }.

    Class field :=
      {
        field_commutative_ring : commutative_ring;
        field_is_left_multiplicative_inverse : is_left_multiplicative_inverse;
        field_domain_is_zero_neq_one : is_zero_neq_one;

        field_div_definition : forall x y , div x y = x * inv y;

        field_inv_Proper : Proper (respectful eq eq) inv;
        field_div_Proper : Proper (respectful eq (respectful eq eq)) div
      }.
    Global Existing Instance field_commutative_ring.
    Global Existing Instance field_is_left_multiplicative_inverse.
    Global Existing Instance field_domain_is_zero_neq_one.
    Global Existing Instance field_inv_Proper.
    Global Existing Instance field_div_Proper.
  End AddMul.
End Algebra.


Section GenericCancellation.
  Context {T:Type} {eq:T->T->Prop} {Equivalence_eq : Equivalence eq}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Context {op:T->T->T} {Proper_op : Proper(respectful eq (respectful eq eq)) op}.
  Context {id:T}.
  
  Context {Hassoc: is_associative (op:=op) (eq:=eq)}.
  Context {Hrid: is_right_identity (op:=op) (eq:=eq) (id := id)}.
  Context {Hlid: is_left_identity (op:=op) (eq:=eq) (id:=id) }.

  Lemma cancel_right z iz (Hinv:op z iz = id) :
    forall x y, op x z = op y z <-> x = y.
  Proof.
    split; intros.
    { assert (op (op x z) iz = op (op y z) iz) as Hcut by (f_equiv; assumption).
      rewrite <-associative in Hcut.
      rewrite <-!associative, !Hinv, !right_identity in Hcut; exact Hcut. }
    { f_equiv; assumption. }
  Qed.

  Lemma cancel_left z iz (Hinv:op iz z = id) :
    forall x y, op z x = op z y <-> x = y.
  Proof.
    split; intros.
    { assert (op iz (op z x) = op iz (op z y)) as Hcut by (f_equiv; assumption).
      rewrite !associative, !Hinv, !left_identity in Hcut; exact Hcut. }
    { f_equiv; assumption. }
  Qed.
End GenericCancellation.

Module Group.
  Section BasicProperties.
    Context {T eq op id inv} `{@group T eq op id inv}.
    Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.

    Lemma cancel_left : forall z x y, op z x = op z y <-> x = y.
    Proof. eauto using cancel_left, left_inverse. Qed.
    Lemma cancel_right : forall z x y, op x z = op y z <-> x = y.
    Proof. eauto using cancel_right, right_inverse. Qed.
  End BasicProperties.
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

    Lemma mul_0_r : forall x, x * 0 = 0.
    Proof.
      intros.
      assert (x*0 = x*0) as Hx by reflexivity.
      rewrite <-(left_identity 0), left_distributive in Hx at 1.
      assert (x*0 + x*0 - x*0 = x*0 - x*0) as Hxx by (f_equiv; exact Hx).
      rewrite !ring_sub_definition, <-associative, right_inverse, right_identity in Hxx; exact Hxx.
    Qed.

    Lemma mul_0_l : forall x, x * 0 = 0.
    Proof.
      intros.
      assert (x*0 = x*0) as Hx by reflexivity.
      rewrite <-(left_identity 0), left_distributive in Hx at 1.
      assert (opp (x*0) + (x*0 + x*0)  = opp (x*0) + x*0) as Hxx by (f_equiv; exact Hx).
      rewrite associative, left_inverse, left_identity in Hxx; exact Hxx.
    Qed.

    Global Instance Ncring_Ring_ops : @Ncring.Ring_ops T zero one add mul sub opp eq. 
    Global Instance Ncring_Ring : @Ncring.Ring T zero one add mul sub opp eq Ncring_Ring_ops.
    Proof.
      split; dropRingSyntax; eauto using left_identity, right_identity, commutative, associative, right_inverse, left_distributive, right_distributive, ring_sub_definition with core typeclass_instances.
      - (* TODO: why does [eauto using @left_identity with typeclass_instances] not work? *)
        eapply @left_identity; eauto with typeclass_instances.
      - eapply @right_identity; eauto with typeclass_instances.
      - eapply associative.
    Qed.
  End Ring.
  
  Section TacticSupportCommutative.
    Context {T eq zero one opp add sub mul} `{@commutative_ring T eq zero one opp add sub mul}.
  
    Global Instance Cring_Cring_commutative_ring :
      @Cring.Cring T zero one add mul sub opp eq Ring.Ncring_Ring_ops Ring.Ncring_Ring.
    Proof. unfold Cring.Cring; intros; dropRingSyntax. eapply commutative. Qed.
  End TacticSupportCommutative.
End Ring.

Module IntegralDomain.
  Section CommutativeRing.
    Context {T eq zero one opp add sub mul} `{@integral_domain T eq zero one opp add sub mul}.
    
    Lemma mul_nonzero_nonzero_cases (x y : T)
      : eq (mul x  y) zero -> eq x zero \/ eq y zero.
    Proof.
      pose proof mul_nonzero_nonzero x y.
      destruct (eq_dec x zero); destruct (eq_dec y zero); intuition.
    Qed.
    
    Global Instance Integral_domain :
      @Integral_domain.Integral_domain T zero one add mul sub opp eq Ring.Ncring_Ring_ops
                                       Ring.Ncring_Ring Ring.Cring_Cring_commutative_ring.
    Proof.
      split; dropRingSyntax.
      - auto using mul_nonzero_nonzero_cases.
      - intro bad; symmetry in bad; auto using zero_neq_one.
    Qed.
  End CommutativeRing.
End IntegralDomain.

Module Field.
  Section Field.
    Context {T eq zero one opp add mul sub inv div} `{@field T eq zero one opp add sub mul inv div}.
    Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := zero. Local Notation "1" := one.
    Local Infix "+" := add. Local Infix "*" := mul.

    Global Instance is_mul_nonzero_nonzero : @is_mul_nonzero_nonzero T eq 0 mul.
    Proof.
      constructor. intros x y Hx Hy Hxy.
      assert (0 = (inv y * (inv x * x)) * y) as H00 by (rewrite <-!associative, Hxy, !Ring.mul_0_r; reflexivity).
      rewrite left_multiplicative_inverse in H00 by assumption.
      rewrite right_identity in H00.
      rewrite left_multiplicative_inverse in H00 by assumption.
      auto using zero_neq_one.
    Qed.

    Global Instance integral_domain : @integral_domain T eq zero one opp add sub mul.
    Proof.
      split; auto using field_commutative_ring, field_domain_is_zero_neq_one, is_mul_nonzero_nonzero.
    Qed.

    Require Coq.setoid_ring.Field_theory.
    Lemma field_theory_for_stdlib_tactic : Field_theory.field_theory 0 1 add mul sub opp div inv eq.
    Proof.
      constructor.
      admit.
      { intro H01. symmetry in H01. auto using zero_neq_one. }
      { apply field_div_definition. }
      { apply left_multiplicative_inverse. }
    Qed.
  End Field.
End Field.