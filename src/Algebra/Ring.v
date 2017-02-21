Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Algebra Crypto.Algebra.Group Crypto.Algebra.Monoid.
Require Coq.ZArith.ZArith Coq.PArith.PArith.

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
    assert (0*x + 0*x - 0*x = 0*x - 0*x) as Hxx by (rewrite Hx; reflexivity).
    rewrite !ring_sub_definition, <-associative, right_inverse, right_identity in Hxx; exact Hxx.
  Qed.

  Lemma mul_0_r : forall x, x * 0 = 0.
  Proof.
    intros.
    assert (x*0 = x*0) as Hx by reflexivity.
    rewrite <-(left_identity 0), left_distributive in Hx at 1.
    assert (opp (x*0) + (x*0 + x*0)  = opp (x*0) + x*0) as Hxx by (rewrite Hx; reflexivity).
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

  Definition opp_zero_iff : forall x, opp x = 0 <-> x = 0 := Group.inv_id_iff.

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

  Lemma sub_zero_iff x y : x - y = 0 <-> x = y.
  Proof.
    split; intro E.
    { rewrite <-(right_identity y), <- E, ring_sub_definition.
      rewrite commutative, <-associative, commutative.
      rewrite left_inverse, left_identity. reflexivity. }
    { rewrite E, ring_sub_definition, right_inverse; reflexivity. }
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
    split; exact _ || cbv; intros; eauto using left_identity, right_identity, commutative, associative, right_inverse, left_distributive, right_distributive, ring_sub_definition with core typeclass_instances.
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

  Context `{phi_homom:is_homomorphism}.

  Lemma homomorphism_zero : phi ZERO = zero.
  Proof. apply Group.homomorphism_id. Qed.

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

(* TODO: file a Coq bug for rewrite_strat -- it should accept ltac variables *)
Ltac push_homomorphism phi :=
  let H := constr:(_ : @Ring.is_homomorphism _ _ _ _ _ _ _ _ _ _ phi) in
  pose proof (@homomorphism_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
    as _push_homomrphism_0;
  pose proof (@homomorphism_one _ _ _ _ _ _ _ _ _ _ _ H)
    as _push_homomrphism_1;
  pose proof (@homomorphism_add _ _ _ _ _ _ _ _ _ _ _ H)
    as _push_homomrphism_p;
  pose proof (@homomorphism_opp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
    as _push_homomrphism_o;
  pose proof (@homomorphism_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
    as _push_homomrphism_s;
  pose proof (@homomorphism_mul _ _ _ _ _ _ _ _ _ _ _ H)
    as _push_homomrphism_m;
  (rewrite_strat bottomup (terms _push_homomrphism_0 _push_homomrphism_1 _push_homomrphism_p _push_homomrphism_o _push_homomrphism_s _push_homomrphism_m));
  clear _push_homomrphism_0 _push_homomrphism_1 _push_homomrphism_p _push_homomrphism_o _push_homomrphism_s _push_homomrphism_m.

Ltac pull_homomorphism phi :=
  let H := constr:(_ : @Ring.is_homomorphism _ _ _ _ _ _ _ _ _ _ phi) in
  pose proof (@homomorphism_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
    as _pull_homomrphism_0;
  pose proof (@homomorphism_one _ _ _ _ _ _ _ _ _ _ _ H)
    as _pull_homomrphism_1;
  pose proof (@homomorphism_add _ _ _ _ _ _ _ _ _ _ _ H)
    as _pull_homomrphism_p;
  pose proof (@homomorphism_opp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
    as _pull_homomrphism_o;
  pose proof (@homomorphism_sub _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H)
    as _pull_homomrphism_s;
  pose proof (@homomorphism_mul _ _ _ _ _ _ _ _ _ _ _ H)
    as _pull_homomrphism_m;
  symmetry in _pull_homomrphism_0;
  symmetry in _pull_homomrphism_1;
  symmetry in _pull_homomrphism_p;
  symmetry in _pull_homomrphism_o;
  symmetry in _pull_homomrphism_s;
  symmetry in _pull_homomrphism_m;
  (rewrite_strat bottomup (terms _pull_homomrphism_0 _pull_homomrphism_1 _pull_homomrphism_p _pull_homomrphism_o _pull_homomrphism_s _pull_homomrphism_m));
  clear _pull_homomrphism_0 _pull_homomrphism_1 _pull_homomrphism_p _pull_homomrphism_o _pull_homomrphism_s _pull_homomrphism_m.

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
    @Cring.Cring T zero one add mul sub opp eq Ncring_Ring_ops Ncring_Ring.
  Proof. unfold Cring.Cring; intros; cbv. eapply commutative. Qed.

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
End Z.

Section of_Z.
  Import ZArith PArith. Local Open Scope Z_scope.
  Context {R Req Rzero Rone Ropp Radd Rsub Rmul}
          {Rring : @ring R Req Rzero Rone Ropp Radd Rsub Rmul}.
  Local Infix "=" := Req. Local Infix "=" := Req : type_scope.

  Fixpoint of_nat (n:nat) : R :=
    match n with
    | O => Rzero
    | S n' => Radd (of_nat n') Rone
    end.
  Definition of_Z (x:Z) : R :=
    match x with
    | Z0 => Rzero
    | Zpos p => of_nat (Pos.to_nat p)
    | Zneg p => Ropp (of_nat (Pos.to_nat p))
    end.

  Lemma of_Z_0 : of_Z 0 = Rzero.
  Proof. reflexivity. Qed.

  Lemma of_nat_add x :
    of_nat (Nat.add x 1) = Radd (of_nat x) Rone.
  Proof. destruct x; rewrite ?Nat.add_1_r; reflexivity. Qed.

  Lemma of_nat_sub x (H: (0 < x)%nat):
    of_nat (Nat.sub x 1) = Rsub (of_nat x) Rone.
  Proof.
    induction x; [omega|simpl].
    rewrite <-of_nat_add.
    rewrite Nat.sub_0_r, Nat.add_1_r.
    simpl of_nat.
    rewrite ring_sub_definition, <-associative.
    rewrite right_inverse, right_identity.
    reflexivity.
  Qed.

  Lemma of_Z_add_1_r :
    forall x, of_Z (Z.add x 1) = Radd (of_Z x) Rone.
  Proof.
    destruct x; [reflexivity| | ]; simpl of_Z.
    { rewrite Pos2Nat.inj_add, of_nat_add.
      reflexivity. }
    { rewrite Z.pos_sub_spec; break_match;
        match goal with
        | H : _ |- _ => rewrite Pos.compare_eq_iff in H
        | H : _ |- _ => rewrite Pos.compare_lt_iff in H
        | H : _ |- _ => rewrite Pos.compare_gt_iff in H;
                          apply Pos.nlt_1_r in H; tauto
        end;
        subst; simpl of_Z; simpl of_nat.
      { rewrite left_identity, left_inverse; reflexivity. }
      { rewrite Pos2Nat.inj_sub by assumption.
        rewrite of_nat_sub by apply Pos2Nat.is_pos.
        rewrite ring_sub_definition, Group.inv_op, Group.inv_inv.
        rewrite commutative; reflexivity. } }
  Qed.

  Lemma of_Z_sub_1_r :
    forall x, of_Z (Z.sub x 1) = Rsub (of_Z x) Rone.
  Proof.
    induction x.
    { simpl; rewrite ring_sub_definition, !left_identity;
        reflexivity. }
    { case_eq (1 ?= p)%positive; intros;
        match goal with
        | H : _ |- _ => rewrite Pos.compare_eq_iff in H
        | H : _ |- _ => rewrite Pos.compare_lt_iff in H
        | H : _ |- _ => rewrite Pos.compare_gt_iff in H;
                          apply Pos.nlt_1_r in H; tauto
        end.
      { subst. simpl; rewrite ring_sub_definition, !left_identity,
                      right_inverse; reflexivity. }
      { rewrite <-Pos2Z.inj_sub by assumption; simpl of_Z.
        rewrite Pos2Nat.inj_sub by assumption.
        rewrite of_nat_sub by apply Pos2Nat.is_pos.
        reflexivity. } }
    { simpl. rewrite Pos2Nat.inj_add, of_nat_add.
      rewrite ring_sub_definition, Group.inv_op, commutative.
      reflexivity. }
  Qed.

  Lemma of_Z_opp : forall a,
      of_Z (Z.opp a) = Ropp (of_Z a).
  Proof.
    destruct a; simpl; rewrite ?Group.inv_id, ?Group.inv_inv;
      reflexivity.
  Qed.

  Lemma of_Z_add : forall a b,
      of_Z (Z.add a b) = Radd (of_Z a) (of_Z b).
  Proof.
    intros.
    let x := match goal with |- ?x => x end in
    let f := match (eval pattern b in x) with ?f _ => f end in
    apply (Z.peano_ind f); intros.
    { rewrite !right_identity. reflexivity. }
    { replace (a + Z.succ x) with ((a + x) + 1) by ring.
      replace (Z.succ x) with (x+1) by ring.
      rewrite !of_Z_add_1_r, H.
      rewrite associative; reflexivity. }
    { replace (a + Z.pred x) with ((a+x)-1)
        by (rewrite <-Z.sub_1_r; ring).
      replace (Z.pred x) with (x-1) by apply Z.sub_1_r.
      rewrite !of_Z_sub_1_r, H.
      rewrite !ring_sub_definition.
      rewrite associative; reflexivity. }
  Qed.

  Lemma of_Z_mul : forall a b,
      of_Z (Z.mul a b) = Rmul (of_Z a) (of_Z b).
  Proof.
    intros.
    let x := match goal with |- ?x => x end in
    let f := match (eval pattern b in x) with ?f _ => f end in
    apply (Z.peano_ind f); intros until 0; try intro IHb.
    { rewrite !mul_0_r; reflexivity. }
    { rewrite Z.mul_succ_r, <-Z.add_1_r.
      rewrite of_Z_add, of_Z_add_1_r.
      rewrite IHb.
      rewrite left_distributive, right_identity.
      reflexivity. }
    { rewrite Z.mul_pred_r, <-Z.sub_1_r.
      rewrite of_Z_sub_1_r.
      rewrite <-Z.add_opp_r.
      rewrite of_Z_add, of_Z_opp.
      rewrite IHb.
      rewrite ring_sub_definition, left_distributive.
      rewrite mul_opp_r,right_identity.
      reflexivity. }
  Qed.


  Global Instance homomorphism_of_Z :
    @is_homomorphism
      Z Logic.eq Z.one Z.add Z.mul
      R Req  Rone  Radd  Rmul
      of_Z.
  Proof.
    repeat constructor; intros.
    { apply of_Z_add. }
    { repeat intro; subst; reflexivity. }
    { apply of_Z_mul. }
    { simpl. rewrite left_identity; reflexivity. }
  Qed.
End of_Z.

Definition char_gt
           {R eq zero one opp add} {sub:R->R->R} {mul:R->R->R}
           C :=
  @Algebra.char_gt R eq zero (fun p => (@of_Z R zero one opp add) (BinInt.Z.pos p)) C.
Existing Class char_gt.

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