Require Import Crypto.Util.Relations Crypto.Util.Tactics Crypto.Util.Notations.
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Crypto.Algebra Crypto.Algebra.Ring Crypto.Algebra.IntegralDomain.
Require Coq.setoid_ring.Field_theory.

Section Field.
  Context {T eq zero one opp add mul sub inv div} `{@field T eq zero one opp add sub mul inv div}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero. Local Notation "1" := one.
  Local Infix "+" := add. Local Infix "*" := mul.

  Lemma right_multiplicative_inverse : forall x : T, ~ eq x zero -> eq (mul x (inv x)) one.
  Proof.
    intros. rewrite commutative. auto using left_multiplicative_inverse.
  Qed.

  Lemma left_inv_unique x ix : ix * x = one -> ix = inv x.
  Proof.
    intro Hix.
    assert (ix*x*inv x = inv x).
    - rewrite Hix, left_identity; reflexivity.
    - rewrite <-associative, right_multiplicative_inverse, right_identity in H0; trivial.
      intro eq_x_0. rewrite eq_x_0, Ring.mul_0_r in Hix.
      apply (zero_neq_one(eq:=eq)). assumption.
  Qed.
  Definition inv_unique := left_inv_unique.

  Lemma right_inv_unique x ix : x * ix = one -> ix = inv x.
  Proof. rewrite commutative. apply left_inv_unique. Qed.

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
    { intro H01. symmetry in H01. auto using (zero_neq_one(eq:=eq)). }
    { apply field_div_definition. }
    { apply left_multiplicative_inverse. }
  Qed.

  Context {eq_dec:DecidableRel eq}.

  Global Instance is_mul_nonzero_nonzero : @is_zero_product_zero_factor T eq 0 mul.
  Proof.
    split. intros x y Hxy.
    eapply not_not; try typeclasses eauto; []; intuition idtac; eapply (zero_neq_one(eq:=eq)).
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
Admitted. (* TODO: remove all uses of this theorem *)

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
Proof. Admitted. (* TODO: remove all uses of this theorem *)

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

Ltac guess_field :=
  match goal with
  | |- ?eq _ _ =>  constr:(_:Algebra.field (eq:=eq))
  | |- not (?eq _ _) =>  constr:(_:Algebra.field (eq:=eq))
  | [H: ?eq _ _ |- _ ] =>  constr:(_:Algebra.field (eq:=eq))
  | [H: not (?eq _ _) |- _] =>  constr:(_:Algebra.field (eq:=eq))
  end.

Ltac goal_to_field_equality fld :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  match goal with
  | [ |- eq _ _] => idtac
  | [ |- not (eq ?x ?y) ] => apply not_exfalso; intro; goal_to_field_equality fld
  | _ => exfalso;
         match goal with
         | H: not (eq _ _) |- _ => apply not_exfalso in H; apply H
         | _ => apply (field_is_zero_neq_one(field:=fld))
         end
  end.

Ltac _introduce_inverse fld d d_nz :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let mul := match type of fld with Algebra.field(mul:=?mul) => mul end in
  let one := match type of fld with Algebra.field(one:=?one) => one end in
  let inv := match type of fld with Algebra.field(inv:=?inv) => inv end in
  match goal with [H: eq (mul d _) one |- _ ] => fail 1 | _ => idtac end;
  let d_i := fresh "i" in
  unique pose proof (right_multiplicative_inverse(H:=fld) _ d_nz);
  set (inv d) as d_i in *;
  clearbody d_i.

Ltac inequalities_to_inverse_equations fld :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let zero := match type of fld with Algebra.field(zero:=?zero) => zero end in
  let div := match type of fld with Algebra.field(div:=?div) => div end in
  let sub := match type of fld with Algebra.field(sub:=?sub) => sub end in
  repeat match goal with
         | [H: not (eq _ _) |- _ ] =>
           lazymatch type of H with
           | not (eq ?d zero) => _introduce_inverse fld d H
           | not (eq zero ?d) => _introduce_inverse fld d (symmetry(R:=fun a b => not (eq a b)) H)
           | not (eq ?x ?y) => _introduce_inverse fld (sub x y) (Ring.neq_sub_neq_zero _ _ H)
           end
         end.

Ltac _nonzero_tac fld :=
  solve [trivial | IntegralDomain.solve_constant_nonzero | goal_to_field_equality fld; nsatz; IntegralDomain.solve_constant_nonzero].

Ltac _inverse_to_equation_by fld d tac :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let zero := match type of fld with Algebra.field(zero:=?zero) => zero end in
  let one := match type of fld with Algebra.field(one:=?one) => one end in
  let mul := match type of fld with Algebra.field(mul:=?mul) => mul end in
  let div := match type of fld with Algebra.field(div:=?div) => div end in
  let inv := match type of fld with Algebra.field(inv:=?inv) => inv end in
  let d_nz := fresh "nz" in
  assert (not (eq d zero)) as d_nz by tac;
  lazymatch goal with
  | H: eq (mul ?di d) one |- _ => rewrite <-!(left_inv_unique(H:=fld) _ _ H) in *
  | H: eq (mul d ?di) one |- _ => rewrite <-!(right_inv_unique(H:=fld) _ _ H) in *
  | _ => _introduce_inverse constr:(fld) constr:(d) d_nz
  end;
  clear d_nz.

Ltac inverses_to_equations_by fld tac :=
  let eq := match type of fld with Algebra.field(eq:=?eq) => eq end in
  let zero := match type of fld with Algebra.field(zero:=?zero) => zero end in
  let inv := match type of fld with Algebra.field(inv:=?inv) => inv end in
  repeat match goal with
         | |- context[inv ?d] => _inverse_to_equation_by fld d tac
         | H: context[inv ?d] |- _ => _inverse_to_equation_by fld d tac
         end.

Ltac divisions_to_inverses fld :=
  rewrite ?(field_div_definition(field:=fld)) in *.

Ltac fsatz :=
  let fld := guess_field in
  goal_to_field_equality fld;
  inequalities_to_inverse_equations fld;
  divisions_to_inverses fld;
  inverses_to_equations_by fld ltac:(solve_debugfail ltac:(_nonzero_tac fld));
  nsatz;
  solve_debugfail ltac:(IntegralDomain.solve_constant_nonzero).

Section FieldSquareRoot.
  Context {T eq zero one opp add mul sub inv div} `{@field T eq zero one opp add sub mul inv div} {eq_dec:DecidableRel eq}.
  Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "+" := add. Local Infix "*" := mul.
  Lemma only_two_square_roots_choice x y z : x * x = z -> y * y = z -> x = y \/ x = opp y.
  Proof.
    intros.
    setoid_rewrite <-sub_zero_iff.
    eapply zero_product_zero_factor.
    fsatz.
  Qed.
End FieldSquareRoot.