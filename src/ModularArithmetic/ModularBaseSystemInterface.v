Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.Util.Tuple Crypto.Util.CaseUtil.
Require Import ZArith.
Require Import Crypto.Algebra.
Import Group.
Import PseudoMersenneBaseParams PseudoMersenneBaseParamProofs.

Generalizable All Variables.
Section s.
  Context `{prm:PseudoMersenneBaseParams m} {sc : SubtractionCoefficient m prm}.
  Context {k_ c_} (pfk : k = k_) (pfc:c = c_).
  Local Notation base := (Pow2Base.base_from_limb_widths limb_widths).

  Definition fe := tuple Z (length base).

  Arguments to_list {_ _} _.

  Definition mul  (x y:fe) : fe :=
    carry_mul_opt_cps k_ c_ (from_list_default 0%Z (length base))
      (to_list x) (to_list y).

  Definition add (x y : fe) : fe :=
    from_list_default 0%Z (length base) (add_opt (to_list x) (to_list y)).

  Definition sub : fe -> fe -> fe.
    refine (on_tuple2 sub_opt _).
    abstract (intros; rewrite sub_opt_correct; apply length_sub; rewrite ?coeff_length; auto).
  Defined.

  Definition phi (a : fe) : ModularArithmetic.F m := decode (to_list a).
  Definition phi_inv (a : ModularArithmetic.F m) : fe :=
    from_list_default 0%Z _ (encode a).

  Lemma phi_inv_spec : forall a, phi (phi_inv a) = a.
  Proof.
    intros; cbv [phi_inv phi].
    erewrite from_list_default_eq.
    rewrite to_list_from_list.
    apply ModularBaseSystemProofs.encode_rep.
    Grab Existential Variables.
    apply ModularBaseSystemProofs.encode_rep.
  Qed.

  Definition eq (x y : fe) : Prop := phi x = phi y.

  Import Morphisms.
  Global Instance eq_Equivalence : Equivalence eq.
  Proof.
    split; cbv [eq]; repeat intro; congruence.
  Qed.

  Lemma phi_inv_spec_reverse : forall a, eq (phi_inv (phi a)) a.
  Proof.
    intros. unfold eq. rewrite phi_inv_spec; reflexivity.
  Qed.

  Definition zero : fe := phi_inv (ModularArithmetic.ZToField 0).

  Definition opp (x : fe) : fe := phi_inv (ModularArithmetic.opp (phi x)).

  Definition one : fe := phi_inv (ModularArithmetic.ZToField 1).

  Definition inv (x : fe) : fe := phi_inv (ModularArithmetic.inv (phi x)).

  Definition div (x y : fe) : fe := phi_inv (ModularArithmetic.div (phi x) (phi y)).

  Lemma add_correct : forall a b,
    to_list (add a b) = BaseSystem.add (to_list a) (to_list b).
  Proof.
    intros; cbv [add].
    rewrite add_opt_correct.
    erewrite from_list_default_eq.
    apply to_list_from_list.
    Grab Existential Variables.
    apply add_same_length; auto using length_to_list.
  Qed.

  Lemma add_phi : forall a b : fe,
    phi (add a b) = ModularArithmetic.add (phi a) (phi b).
  Proof.
    intros; cbv [phi].
    rewrite add_correct.
    apply ModularBaseSystemProofs.add_rep; auto using decode_rep, length_to_list.
  Qed.

  Lemma sub_correct : forall a b,
    to_list (sub a b) = ModularBaseSystem.sub coeff (to_list a) (to_list b).
  Proof.
    intros; cbv [sub on_tuple2].
    rewrite to_list_from_list.
    apply sub_opt_correct.
  Qed.

  Lemma sub_phi : forall a b : fe,
    phi (sub a b) = ModularArithmetic.sub (phi a) (phi b).
  Proof.
    intros; cbv [phi].
    rewrite sub_correct.
    apply ModularBaseSystemProofs.sub_rep; auto using decode_rep, length_to_list,
      coeff_length, coeff_mod.
  Qed.

  Lemma mul_correct : forall a b,
    to_list (mul a b) = carry_mul (to_list a) (to_list b).
  Proof.
    intros; cbv [mul].
    rewrite carry_mul_opt_cps_correct by assumption.
    erewrite from_list_default_eq.
    apply to_list_from_list.
    Grab Existential Variables.
    apply carry_mul_length; apply length_to_list.
  Qed.

  Lemma mul_phi : forall a b : fe,
    phi (mul a b) = ModularArithmetic.mul (phi a) (phi b).
  Proof.
    intros; cbv beta delta [phi].
    rewrite mul_correct.
    apply carry_mul_rep; auto using decode_rep, length_to_list.
  Qed.

  Lemma modular_base_system_field : @field fe eq zero one opp add sub mul inv div.
  Proof.
    eapply (Field.isomorphism_to_subfield_field (phi := phi) (fieldR := PrimeFieldTheorems.field_modulo  (prime_q := prime_modulus))).
    Grab Existential Variables.
    + intros; eapply phi_inv_spec.
    + intros; eapply phi_inv_spec.
    + intros; eapply phi_inv_spec.
    + intros; eapply phi_inv_spec.
    + intros; eapply mul_phi.
    + intros; eapply sub_phi.
    + intros; eapply add_phi.
    + intros; eapply phi_inv_spec.
    + cbv [eq zero one]. erewrite !phi_inv_spec. intro A.
      eapply (PrimeFieldTheorems.Fq_1_neq_0 (prime_q := prime_modulus)). congruence.
    + trivial.
    + repeat intro. cbv [div]. congruence.
    + repeat intro. cbv [inv]. congruence.
    + repeat intro. cbv [eq]. erewrite !mul_phi. congruence.
    + repeat intro. cbv [eq]. erewrite !sub_phi. congruence.
    + repeat intro. cbv [eq]. erewrite !add_phi. congruence.
    + repeat intro. cbv [opp]. congruence.
    + cbv [eq]. auto using ModularArithmeticTheorems.F_eq_dec.
  Qed.

End s.