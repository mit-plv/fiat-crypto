Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.Algebra.
Require Import Crypto.Util.Relations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.

Require Import Crypto.Specific.GF25519.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.

Definition edwards_extended_add_coordinates td P Q :=
    (@ExtendedCoordinates.Extended.add_coordinates _ add sub mul td P Q).
Definition edwards_extended_carry_add_coordinates td P Q :=
    (@ExtendedCoordinates.Extended.add_coordinates _ carry_add carry_sub mul td P Q).

Create HintDb edwards_extended_add_coordinates_correct discriminated.
Local Existing Instance field25519.
Hint Rewrite
     (Ring.homomorphism_mul(is_homomorphism:=homomorphism_F25519_decode))
     (Ring.homomorphism_add(H1             :=homomorphism_F25519_decode))
     (Ring.homomorphism_sub(H1             :=homomorphism_F25519_decode))
  : edwards_extended_add_coordinates_correct.
Lemma edwards_extended_add_coordinates_correct td P Q :
  Tuple.map (n:=4) decode (edwards_extended_add_coordinates td P Q)
  = (@ExtendedCoordinates.Extended.add_coordinates _ F.add F.sub F.mul (decode td) (Tuple.map (n:=4) decode P) (Tuple.map (n:=4) decode Q)).
Proof.
  change (edwards_extended_add_coordinates td P Q)
  with (@ExtendedCoordinates.Extended.add_coordinates _ add sub mul td P Q).
  destruct_head' prod.
  simpl.
  rewrite_strat topdown hints edwards_extended_add_coordinates_correct.
  reflexivity.
Qed.
Local Existing Instance carry_field25519.
Hint Rewrite
     (Ring.homomorphism_mul(is_homomorphism:=homomorphism_carry_F25519_decode))
     (Ring.homomorphism_add(H1             :=homomorphism_carry_F25519_decode))
     (Ring.homomorphism_sub(H1             :=homomorphism_carry_F25519_decode))
  : edwards_extended_add_coordinates_correct.
Lemma edwards_extended_carry_add_coordinates_correct td P Q :
  Tuple.map (n:=4) decode (edwards_extended_carry_add_coordinates td P Q)
  = (@ExtendedCoordinates.Extended.add_coordinates _ F.add F.sub F.mul (decode td) (Tuple.map (n:=4) decode P) (Tuple.map (n:=4) decode Q)).
Proof.
  change (edwards_extended_carry_add_coordinates td P Q)
  with (@ExtendedCoordinates.Extended.add_coordinates _ carry_add carry_sub mul td P Q).
  destruct_head' prod.
  simpl.
  rewrite_strat topdown hints edwards_extended_add_coordinates_correct.
  reflexivity.
Qed.

Lemma fieldwise_eq_edwards_extended_add_coordinates_carry_nocarry td P Q :
  Tuple.fieldwise
    (n:=4) eq
    (edwards_extended_carry_add_coordinates td P Q)
    (edwards_extended_add_coordinates td P Q).
Proof.
  pose proof (edwards_extended_carry_add_coordinates_correct td P Q) as H0.
  pose proof (edwards_extended_add_coordinates_correct td P Q) as H1.
  rewrite <- H0 in H1; clear H0.
  assert (Tuple.fieldwise
            (fun x y => x = y)
            (Tuple.map (n:=4) decode (edwards_extended_carry_add_coordinates td P Q))
            (Tuple.map (n:=4) decode (edwards_extended_add_coordinates td P Q)))
    by (rewrite H1; reflexivity).
  clear H1.
  destruct (edwards_extended_carry_add_coordinates td P Q), (edwards_extended_add_coordinates td P Q).
  destruct_head' prod; simpl; unfold eq; trivial.
Qed.
