Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Algebra. Import Field.
Require Import Crypto.Util.Tuple Crypto.Util.Notations.
Local Open Scope Z_scope.

Section ModularBaseSystemField.
  Context `{prm : PseudoMersenneBaseParams} {sc : SubtractionCoefficient modulus prm} {cc : CarryChain limb_widths}
    (k_ c_ : Z) (k_subst : k = k_) (c_subst : c = c_).
  Local Existing Instance prime_modulus.
  Local Notation base := (Pow2Base.base_from_limb_widths limb_widths).
  Local Notation digits := (tuple Z (length limb_widths)).

  Lemma add_decode : forall a b : digits,
    decode (add_opt a b) = (decode a + decode b)%F.
  Proof.
    intros; rewrite add_opt_correct by assumption.
    apply add_rep; apply decode_rep.
  Qed.

  Lemma sub_decode : forall a b : digits,
    decode (sub_opt a b) = (decode a - decode b)%F.
  Proof.
    intros; rewrite sub_opt_correct by assumption.
    apply sub_rep; auto using coeff_mod, decode_rep.
  Qed.

  Lemma mul_decode : forall a b : digits,
    decode (carry_mul_opt k_ c_ a b) = (decode a * decode b)%F.
  Proof.
    intros; rewrite carry_mul_opt_correct by assumption.
    apply carry_mul_rep; apply decode_rep.
  Qed.

  Lemma _zero_neq_one : not (eq zero one).
  Proof. cbv [eq zero one]. erewrite !encode_rep; apply zero_neq_one. Qed.

  Lemma encode_Proper : 
    Morphisms.Proper
      (Morphisms.respectful Logic.eq eq) encode.
  Proof.
    repeat intro.
    cbv [eq].
    rewrite !encode_rep.
    assumption.
  Qed.

  Lemma modular_base_system_field_homomorphism :
    @Ring.is_homomorphism
      (F modulus) Logic.eq F.one F.add F.mul
      digits eq one add_opt (carry_mul_opt k_ c_)
      encode.
  Proof.
    econstructor.
    + econstructor; [ | apply encode_Proper].
      intros; cbv [eq].
      rewrite add_opt_correct, add_rep; apply encode_rep.
    + intros; cbv [eq].
      rewrite carry_mul_opt_correct by auto.
      rewrite carry_mul_rep; apply encode_rep.
    + reflexivity.
  Qed.

  Lemma modular_base_system_field :
    @field digits eq zero one opp add_opt sub_opt (carry_mul_opt k_ c_) inv div.
  Proof.
    eapply (Field.isomorphism_to_subfield_field (phi := decode)).
    Grab Existential Variables.
    + intros; eapply encode_rep.
    + intros; eapply encode_rep.
    + intros; eapply encode_rep.
    + intros; eapply encode_rep.
    + intros; eapply mul_decode.
    + intros; eapply sub_decode.
    + intros; eapply add_decode.
    + intros; eapply encode_rep.
    + eapply _zero_neq_one.
    + trivial.
    + repeat intro. cbv [div]. congruence.
    + repeat intro. cbv [inv]. congruence.
    + repeat intro. cbv [eq]. erewrite !mul_decode. congruence.
    + repeat intro. cbv [eq]. erewrite !sub_decode. congruence.
    + repeat intro. cbv [eq]. erewrite !add_decode. congruence.
    + repeat intro. cbv [opp]. congruence.
  Qed.

End ModularBaseSystemField.