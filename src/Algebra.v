Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Require Import Crypto.Util.Tactics Crypto.Tactics.Nsatz.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Notations.
Require Coq.Numbers.Natural.Peano.NPeano.
Local Close Scope nat_scope. Local Close Scope type_scope. Local Close Scope core_scope.

Module Import ModuloCoq8485.
  Import NPeano Nat.
  Infix "mod" := modulo (at level 40, no associativity).
End ModuloCoq8485.

Notation is_eq_dec := (DecidableRel _) (only parsing).
Notation "@ 'is_eq_dec' T R" := (DecidableRel (R:T->T->Prop))
                                  (at level 10, T at level 8, R at level 8, only parsing).
Notation eq_dec x y := (@dec (_ x y) _) (only parsing).
Notation "x =? y" := (eq_dec x y) : type_scope.

Section Algebra.
  Context {T:Type} {eq:T->T->Prop}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.

  Local Notation is_eq_dec := (@is_eq_dec T eq).

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
        monoid_Equivalence : Equivalence eq;
        monoid_is_eq_dec : is_eq_dec
      }.
    Global Existing Instance monoid_is_associative.
    Global Existing Instance monoid_is_left_identity.
    Global Existing Instance monoid_is_right_identity.
    Global Existing Instance monoid_Equivalence.
    Global Existing Instance monoid_is_eq_dec.
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
End Monoid.

Section ZeroNeqOne.
  Context {T eq zero one} `{@is_zero_neq_one T eq zero one} `{Equivalence T eq}.

  Lemma one_neq_zero : not (eq one zero).
  Proof.
    intro HH; symmetry in HH. auto using zero_neq_one.
  Qed.
End ZeroNeqOne.

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
    Context {phi:G->H}.
    Local Infix "=" := eq. Local Infix "=" := eq : type_scope.

    Class is_homomorphism :=
      {
        homomorphism : forall a b,  phi (OP a b) = op (phi a) (phi b);

        is_homomorphism_phi_proper : Proper (respectful EQ eq) phi
      }.
    Global Existing Instance is_homomorphism_phi_proper.
    Context `{is_homomorphism}.

    Lemma homomorphism_id : phi ID = id.
    Proof.
      assert (Hii: op (phi ID) (phi ID) = op (phi ID) id) by
        (rewrite <- homomorphism, left_identity, right_identity; reflexivity).
      rewrite cancel_left in Hii; exact Hii.
    Qed.

    Lemma homomorphism_inv : forall x, phi (INV x) = inv (phi x).
    Proof.
    Admitted.
  End Homomorphism.

  Section GroupByHomomorphism.
    Lemma surjective_homomorphism_from_group
          {G EQ OP ID INV} {groupG:@group G EQ OP ID INV}
          {H eq op id inv}
          {Equivalence_eq: @Equivalence H eq} {eq_dec: forall x y, {eq x y} + {~ eq x y}}
          {Proper_op:Proper(eq==>eq==>eq)op}
          {Proper_inv:Proper(eq==>eq)inv}
          {phi iph} {Proper_phi:Proper(EQ==>eq)phi} {Proper_iph:Proper(eq==>EQ)iph}
          {surj:forall h, phi (iph h) = h}
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
          {Equivalence_EQ: @Equivalence G EQ} {eq_dec: forall x y, {EQ x y} + {~ EQ x y}}
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

  Section ScalarMult.
    Context {G eq add zero opp} `{@group G eq add zero opp}.
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
    Context `{is_scalarmult}.

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
      { rewrite scalarmult_S_l, <-mult_n_Sm, <-Plus.plus_comm, scalarmult_add_l. apply cancel_left, IHn. }
    Qed.

    Lemma opp_mul : forall n P, opp (n * P) = n * (opp P).
      induction n; intros.
      { rewrite !scalarmult_0_l, inv_id; reflexivity. }
      { rewrite <-NPeano.Nat.add_1_l, Plus.plus_comm at 1.
        rewrite scalarmult_add_l, scalarmult_1_l, inv_op, scalarmult_S_l, cancel_left; eauto. }
    Qed.

    Lemma scalarmult_times_order : forall l B, l*B = zero -> forall n, (l * n) * B = zero.
    Proof. intros ? ? Hl ?. rewrite <-scalarmult_assoc, Hl, scalarmult_zero_r. reflexivity. Qed.

    Lemma scalarmult_mod_order : forall l B, l <> 0%nat -> l*B = zero -> forall n, n mod l * B = n * B.
    Proof.
      intros ? ? Hnz Hmod ?.
      rewrite (NPeano.Nat.div_mod n l Hnz) at 2.
      rewrite scalarmult_add_l, scalarmult_times_order, left_identity by auto. reflexivity.
    Qed.
  End ScalarMult.
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

    Lemma mul_0_r : forall x, 0 * x = 0.
    Proof.
      intros.
      assert (0*x = 0*x) as Hx by reflexivity.
      rewrite <-(right_identity 0), right_distributive in Hx at 1.
      assert (0*x + 0*x - 0*x = 0*x - 0*x) as Hxx by (f_equiv; exact Hx).
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

    Lemma sub_0_l x : 0 - x = opp x.
    Proof. rewrite ring_sub_definition. rewrite left_identity. reflexivity. Qed.

    Lemma mul_opp_r x y : x * opp y = opp (x * y).
    Proof.
      assert (Ho:x*(opp y) + x*y = 0)
        by (rewrite <-left_distributive, left_inverse, mul_0_l; reflexivity).
      rewrite <-(left_identity (opp (x*y))), <-Ho; clear Ho.
      rewrite <-!associative, right_inverse, right_identity; reflexivity.
    Qed.

    Lemma mul_opp_l x y : opp x * y = opp (x * y).
    Proof.
      assert (Ho:opp x*y + x*y = 0)
        by (rewrite <-right_distributive, left_inverse, mul_0_r; reflexivity).
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
        homomorphism_is_homomorphism : Group.is_homomorphism (phi:=phi) (OP:=ADD) (op:=add) (EQ:=EQ) (eq:=eq);
        homomorphism_mul : forall x y, phi (MUL x y) = mul (phi x) (phi y);
        homomorphism_one : phi ONE = one
      }.
    Global Existing Instance homomorphism_is_homomorphism.

    Context `{is_homomorphism}.

    Lemma homomorphism_add : forall x y,  phi (ADD x y) = add (phi x) (phi y).
    Proof. apply Group.homomorphism. Qed.

    Definition homomorphism_opp : forall x,  phi (OPP x) = opp (phi x) :=
      (Group.homomorphism_inv (INV:=OPP) (inv:=opp)).

    Lemma homomorphism_sub : forall x y, phi (SUB x y) = sub (phi x) (phi y).
    Proof.
      intros.
      rewrite !ring_sub_definition, Group.homomorphism, homomorphism_opp. reflexivity.
    Qed.

  End Homomorphism.

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

    Lemma mul_nonzero_nonzero_cases (x y : T)
      : eq (mul x y) zero -> eq x zero \/ eq y zero.
    Proof.
      pose proof mul_nonzero_nonzero x y.
      destruct (eq_dec x zero); destruct (eq_dec y zero); intuition.
    Qed.

    Lemma mul_nonzero_nonzero_iff (x y : T)
      : ~eq (mul x y) zero <-> ~eq x zero /\ ~eq y zero.
    Proof.
      split.
      { intro H0; split; intro H1; apply H0; rewrite H1.
        { apply Ring.mul_0_r. }
        { apply Ring.mul_0_l. } }
      { intros [? ?] ?; edestruct mul_nonzero_nonzero_cases; eauto with nocore. }
    Qed.

    Global Instance Integral_domain :
      @Integral_domain.Integral_domain T zero one add mul sub opp eq Ring.Ncring_Ring_ops
                                       Ring.Ncring_Ring Ring.Cring_Cring_commutative_ring.
    Proof.
      split; dropRingSyntax.
      - auto using mul_nonzero_nonzero_cases.
      - intro bad; symmetry in bad; auto using zero_neq_one.
    Qed.
  End IntegralDomain.
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
      assert (0 = (inv y * (inv x * x)) * y) as H00. (rewrite <-!associative, Hxy, !Ring.mul_0_l; reflexivity).
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
      { apply Ring.ring_theory_for_stdlib_tactic. }
      { intro H01. symmetry in H01. auto using zero_neq_one. }
      { apply field_div_definition. }
      { apply left_multiplicative_inverse. }
    Qed.

  End Field.

  Section Homomorphism.
    Context {F EQ ZERO ONE OPP ADD MUL SUB INV DIV} `{@field F EQ ZERO ONE OPP ADD SUB MUL INV DIV}.
    Context {K eq zero one opp add mul sub inv div} `{@field K eq zero one opp add sub mul inv div}.
    Context {phi:F->K}.
    Local Infix "=" := eq. Local Infix "=" := eq : type_scope.
    Context `{@Ring.is_homomorphism F EQ ONE ADD MUL K eq one add mul phi}.

    Lemma homomorphism_multiplicative_inverse : forall x, phi (INV x) = inv (phi x). Admitted.

    Lemma homomorphism_div : forall x y, phi (DIV x y) = div (phi x) (phi y).
    Proof.
      intros. rewrite !field_div_definition.
      rewrite Ring.homomorphism_mul, homomorphism_multiplicative_inverse. reflexivity.
    Qed.
  End Homomorphism.
End Field.

(*** Tactics for manipulating field equations *)
Require Import Coq.setoid_ring.Field_tac.

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
           => apply IntegralDomain.mul_nonzero_nonzero_cases in H; destruct H
         | [ |- not (?R (?mul ?x ?y) ?zero) ]
           => apply IntegralDomain.mul_nonzero_nonzero_iff; split
         | [ H : not (?R (?mul ?x ?y) ?zero) |- _ ]
           => apply IntegralDomain.mul_nonzero_nonzero_iff in H; destruct H
         end.

Ltac common_denominator :=
  let fld := guess_field in
  lazymatch type of fld with
    field (div:=?div) =>
    lazymatch goal with
    | |- appcontext[div] => field_simplify_eq
    | |- _ => idtac
    end
  end.

Ltac common_denominator_in H :=
  let fld := guess_field in
  lazymatch type of fld with
    field (div:=?div) =>
    lazymatch type of H with
    | appcontext[div] => field_simplify_eq in H
    | _ => idtac
    end
  end.

Ltac common_denominator_all :=
  common_denominator;
  repeat match goal with [H: _ |- _ _ _ ] => progress common_denominator_in H end.

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

Ltac set_nonfraction_pieces_on T eq zero opp add sub mul inv div nonzero_tac cont :=
  idtac;
  let one_arg_recr :=
      fun op v
      => set_nonfraction_pieces_on
           v eq zero opp add sub mul inv div nonzero_tac
           ltac:(fun x => cont (op x)) in
  let two_arg_recr :=
      fun op v0 v1
      => set_nonfraction_pieces_on
           v0 eq zero opp add sub mul inv div nonzero_tac
           ltac:(fun x
                 =>
                   set_nonfraction_pieces_on
                     v1 eq zero opp add sub mul inv div nonzero_tac
                     ltac:(fun y => cont (op x y))) in
  lazymatch T with
  | eq ?x ?y => two_arg_recr eq x y
  | appcontext[div]
    => lazymatch T with
       | div ?numerator ?denominator
         => let d := fresh "d" in
            pose denominator as d;
            assert (~eq d zero);
            [ subst d; nonzero_tac
            | set_nonfraction_pieces_on
                numerator eq zero opp add sub mul inv div nonzero_tac
                ltac:(fun numerator'
                      => cont (div numerator' d)) ]
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
Ltac set_nonfraction_pieces_in_by H nonzero_tac :=
  idtac;
  let fld := guess_field in
  lazymatch type of fld with
  | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => let T := type of H in
       set_nonfraction_pieces_on
         T eq zero opp add sub mul inv div nonzero_tac
         ltac:(fun T' => change T' in H);
       deduplicate_nonfraction_pieces mul
  end.
Ltac set_nonfraction_pieces_by nonzero_tac :=
  idtac;
  let fld := guess_field in
  lazymatch type of fld with
  | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
    => let T := get_goal in
       set_nonfraction_pieces_on
         T eq zero opp add sub mul inv div nonzero_tac
         ltac:(fun T' => change T');
       deduplicate_nonfraction_pieces mul
  end.
Ltac set_nonfraction_pieces_in H :=
  set_nonfraction_pieces_in_by H ltac:(try (intro; field_nonzero_mul_split; try tauto)).
Ltac set_nonfraction_pieces :=
  set_nonfraction_pieces_by ltac:(try (intro; field_nonzero_mul_split; tauto)).
Ltac conservative_common_denominator_in H :=
  idtac;
  let fld := guess_field in
  let div := lazymatch type of fld with
             | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
               => div
             end in
  lazymatch type of H with
  | appcontext[div]
    => set_nonfraction_pieces_in H;
       [ ..
       | common_denominator_in H;
         [ repeat split; try assumption..
         | ] ];
       repeat match goal with H := _ |- _ => subst H end
  | ?T => fail 0 "no division in" H ":" T
  end.
Ltac conservative_common_denominator :=
  idtac;
  let fld := guess_field in
  let div := lazymatch type of fld with
             | @field ?T ?eq ?zero ?one ?opp ?add ?sub ?mul ?inv ?div
               => div
             end in
  lazymatch goal with
  | |- appcontext[div]
    => set_nonfraction_pieces;
       [ ..
       | common_denominator;
         [ repeat split; try assumption..
         | ] ];
       repeat match goal with H := _ |- _ => subst H end
  | |- ?G
    => fail 0 "no division in goal" G
  end.

Ltac conservative_common_denominator_all :=
  try conservative_common_denominator;
  [ ..
  | repeat match goal with [H: _ |- _ ] => progress conservative_common_denominator_in H; [] end ].

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

(** Clear duplicate hypotheses, and hypotheses of the form [R x x] for a reflexive relation [R] *)
Ltac clear_algebraic_duplicates_step R :=
  match goal with
  | [ H : R ?x ?x |- _ ]
    => clear H
  end.
Ltac clear_algebraic_duplicates_guarded R :=
  let test_reflexive := constr:(_ : Reflexive R) in
  repeat clear_algebraic_duplicates_step R.
Ltac clear_algebraic_duplicates :=
  clear_duplicates;
  repeat match goal with
         | [ H : ?R ?x ?x |- _ ] => clear_algebraic_duplicates_guarded R
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

Ltac conservative_field_algebra :=
  intros;
  conservative_common_denominator_all;
  try (nsatz; dropRingSyntax);
  repeat (apply conj);
  try solve
      [neq01
      |trivial
      |apply Ring.opp_nonzero_nonzero;trivial].

Ltac field_algebra :=
  intros;
  common_denominator_all;
  try (nsatz; dropRingSyntax);
  repeat (apply conj);
  try solve
      [neq01
      |trivial
      |apply Ring.opp_nonzero_nonzero;trivial].

Ltac split_field_inequalities_step :=
  match goal with
  | [ H : not (?R (?mul ?x ?y) ?zero) |- _ ]
    => apply IntegralDomain.mul_nonzero_nonzero_iff in H; destruct H
  end.
Ltac split_field_inequalities :=
  canonicalize_field_inequalities;
  repeat split_field_inequalities_step;
  clear_duplicates.

Ltac combine_field_inequalities_step :=
  match goal with
  | [ H : not (?R ?x ?zero), H' : not (?R ?x' ?zero) |- _ ]
    => pose proof (mul_nonzero_nonzero x x' H H'); clear H H'
  | [ H : (?X -> False)%type |- _ ]
    => change (not X) in H
  end.

(** First we split apart the equalities so that we can clear
    duplicates; it's easier for us to do this than to give [nsatz] the
    extra work. *)
Ltac combine_field_inequalities :=
  split_field_inequalities;
  repeat combine_field_inequalities_step.
Ltac prensatz_contradict :=
  combine_field_inequalities;
  repeat intro;
  match goal with
  | [ H : not (?R ?x ?zero) |- False ] => apply H
  | [ H : (?R ?x ?zero -> False)%type |- False ] => apply H
  end.
(** Handles inequalities and fractions *)
Ltac super_nsatz :=
  try prensatz_contradict;
  try conservative_common_denominator_all;
  [ try nsatz
  | repeat (apply conj || split_field_inequalities); try assumption; prensatz_contradict; try nsatz.. ].

Section ExtraLemmas.
  Context {F eq zero one opp add sub mul inv div} `{F_field:field F eq zero one opp add sub mul inv div}.
  Local Infix "+" := add. Local Infix "*" := mul. Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "0" := zero. Local Notation "1" := one.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.

  Lemma only_two_square_roots' x y : x * x = y * y -> x <> y -> x <> opp y -> False.
  Proof.
    intros.
    canonicalize_field_equalities; canonicalize_field_inequalities.
    assert (H' : (x + y) * (x - y) <> 0) by (apply mul_nonzero_nonzero; assumption).
    apply H'; nsatz.
  Qed.

  Lemma only_two_square_roots x y z : x * x = z -> y * y = z -> x <> y -> x <> opp y -> False.
  Proof.
    intros; setoid_subst z; eauto using only_two_square_roots'.
  Qed.

  Lemma only_two_square_roots'_choice x y : x * x = y * y -> x = y \/ x = opp y.
  Proof.
    intro H.
    destruct (eq_dec x y); [ left; assumption | right ].
    destruct (eq_dec x (opp y)); [ assumption | exfalso ].
    eapply only_two_square_roots'; eassumption.
  Qed.

  Lemma only_two_square_roots_choice x y z : x * x = z -> y * y = z -> x = y \/ x = opp y.
  Proof.
    intros; setoid_subst z; eauto using only_two_square_roots'_choice.
  Qed.
End ExtraLemmas.

(** We look for hypotheses of the form [x^2 = y^2] and [x^2 = z] together with [y^2 = z], and prove that [x = y] or [x = opp y] *)
Ltac pose_proof_only_two_square_roots x y H :=
  not constr_eq x y;
  match goal with
  | [ H' : ?eq (?mul x x) (?mul y y) |- _ ]
    => pose proof (only_two_square_roots'_choice x y H') as H
  | [ H0 : ?eq (?mul x x) ?z, H1 : ?eq (?mul y y) ?z |- _ ]
    => pose proof (only_two_square_roots_choice x y z H0 H1) as H
  end.
Ltac reduce_only_two_square_roots x y :=
  let H := fresh in
  pose_proof_only_two_square_roots x y H;
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
Ltac only_two_square_roots_step :=
  match goal with
  | [ H : not (?eq ?x (?opp ?y)) |- _ ]
    (* this one comes first, because it the procedure is asymmetric
       with respect to [x] and [y], and this order is more likely to
       lead to solving goals by contradiction. *)
    => is_var x; is_var y; reduce_only_two_square_roots x y; post_clean_only_two_square_roots x y
  | [ H : ?eq (?mul ?x ?x) (?mul ?y ?y) |- _ ]
    => reduce_only_two_square_roots x y; post_clean_only_two_square_roots x y
  | [ H : ?eq (?mul ?x ?x) ?z, H' : ?eq (?mul ?y ?y) ?z |- _ ]
    => reduce_only_two_square_roots x y; post_clean_only_two_square_roots x y
  end.
Ltac only_two_square_roots :=
  pre_clean_only_two_square_roots;
  repeat only_two_square_roots_step.

Section Example.
  Context {F zero one opp add sub mul inv div} `{F_field:field F eq zero one opp add sub mul inv div}.
  Local Infix "+" := add. Local Infix "*" := mul. Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "0" := zero. Local Notation "1" := one.

  Add Field _ExampleField : (Field.field_theory_for_stdlib_tactic (T:=F)).

  Example _example_nsatz x y : 1+1 <> 0 -> x + y = 0 -> x - y = 0 -> x = 0.
  Proof. field_algebra. Qed.

  Example _example_field_nsatz x y z : y <> 0 -> x/y = z -> z*y + y = x + y.
  Proof. intros; subst; field_algebra. Qed.

  Example _example_nonzero_nsatz_contradict x y : x * y = 1 -> not (x = 0).
  Proof. intros. intro. nsatz_contradict. Qed.
End Example.

Section Z.
  Require Import ZArith.
  Global Instance ring_Z : @ring Z Logic.eq 0%Z 1%Z Z.opp Z.add Z.sub Z.mul.
  Proof. repeat split; auto using Z.eq_dec with zarith typeclass_instances. Qed.

  Global Instance commutative_ring_Z : @commutative_ring Z Logic.eq 0%Z 1%Z Z.opp Z.add Z.sub Z.mul.
  Proof. eauto using @commutative_ring, @is_commutative, ring_Z with zarith. Qed.

  Global Instance integral_domain_Z : @integral_domain Z Logic.eq 0%Z 1%Z Z.opp Z.add Z.sub Z.mul.
  Proof.
    split.
    { apply commutative_ring_Z. }
    { constructor. intros. apply Z.neq_mul_0; auto. }
    { constructor. discriminate. }
  Qed.

  Example _example_nonzero_nsatz_contradict_Z x y : Z.mul x y = (Zpos xH) -> not (x = Z0).
  Proof. intros. intro. nsatz_contradict. Qed.
End Z.
