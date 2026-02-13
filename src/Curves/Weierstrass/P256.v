From Coq Require Import ZArith Znumtheory.
Require Import Crypto.Algebra.Field.
From Crypto Require Import PrimeFieldTheorems ModInv.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.

Local Open Scope positive_scope.

Definition p256 := 2^256 - 2^224 + 2^192 + 2^96 - 1.

From Coq Require Import List. Import ListNotations.
From Coqprime Require Import PocklingtonCertificat(Pocklington_refl,singleCertif(..)).

#[export] Instance prime_p256 : prime p256.
Proof.
  remember prime; vm_compute; subst.
  simple refine (Pocklington_refl
    (Pock_certif _ 6 [(6700417,1);(490463,1);(65537,1);(641,1);(257,1);(17,1);(5,2);(3,1);(2,1)] 0x6f199ff1e192ee086c186e)
    [ Pock_certif 6700417 5 [(3,1);(2,7)] 552;
      Pock_certif 490463 7 [(53,1);(2,1)] 174;
      Pock_certif 65537 3 [(2,16)] 1;
      Pock_certif 641 3 [(2,7)] 1;
      Pock_certif 257 3 [(2,8)] 1;
      Pock_certif 53 2 [(2,2)] 4;
      Pock_certif 17 3 [(2,4)] 1;
      Pock_certif 5 2 [(2,2)] 1;
      Proof_certif 3 prime_3;
      Proof_certif 2 prime_2] _)%positive.
  native_cast_no_check (@eq_refl bool true).
Qed.

Add Field Private_field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F p256)).

#[local] Definition a : F p256 := F.opp (1+1+1).
#[local] Definition b : F p256 := F.of_Z _ 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b.

#[export] Instance p256_char_ge_3 : @Ring.char_ge (F p256) eq F.zero F.one F.opp F.add F.sub F.mul 3.
Proof. intros n Hn. apply (@F.char_gt p256). cbv [p256]. Lia.lia. Qed.
#[export] Instance p256_char_ge_12 : @Ring.char_ge (F p256) eq F.zero F.one F.opp F.add F.sub F.mul 12.
Proof. intros n Hn. apply (@F.char_gt p256). cbv [p256]. Lia.lia. Qed.

#[local] Notation Wpoint := (@W.point (F p256) eq F.add F.mul a b).

#[refine, export] Instance curve_commutative_group : Hierarchy.commutative_group (T:=Wpoint) :=
  (W.commutative_group p256_char_ge_3 (a:=a)(b:=b)).
Proof. cbv [id]. Decidable.vm_decide. Defined.

(* Intentionally overloading W.mul from WeierstrassCurve.v here, cause they are the same thing. *)
Module W.
  Definition mul := ScalarMult.scalarmult_ref
    (G := Wpoint)
    (add := W.add)
    (zero := W.zero)
    (opp := W.opp).
End W.

Definition p256_group_order := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.

#[export] Instance prime_order : prime p256_group_order.
Proof.
  simple refine (Pocklington_refl
    (Pock_certif _ 7 [(187019741,1);(38189,1);(17449,1);(3407,1);(131,1);(71,1);(2,4)] 0xf72444b78fa654e632d4b)
    [ Pock_certif 187019741 2 [(9350987,1);(2,2)] 1;
      Pock_certif 9350987 2 [(229,1);(2,1)] 264;
      Pock_certif 38189 2 [(9547,1);(2,2)] 1;
      Pock_certif 17449 14 [(3,1);(2,3)] 1;
      Pock_certif 9547 2 [(37,1);(2,1)] 1;
      Pock_certif 3407 5 [(13,1);(2,1)] 26;
      Pock_certif 229 6 [(3,1);(2,2)] 1;
      Pock_certif 131 2 [(5,1);(2,1)] 1;
      Pock_certif 71 7 [(5,1);(2,1)] 1;
      Pock_certif 37 2 [(2,2)] 1;
      Pock_certif 13 2 [(2,2)] 1;
      Pock_certif 5 2 [(2,2)] 1;
      Proof_certif 3 prime_3;
      Proof_certif 2 prime_2] _)%positive.
  native_cast_no_check (@eq_refl bool true).
Qed.

Lemma p256_mul_mod_n (a b : Z) (P : Wpoint) :
  W.eq (W.mul a P) (W.mul b P) <->
  a mod p256_group_order = b mod p256_group_order.
Proof. Admitted.
