From Coq Require Import ZArith Znumtheory.
Require Import Crypto.Algebra.Field.
From Crypto Require Import PrimeFieldTheorems ModInv.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.

Local Open Scope positive_scope.

Definition p256 := 2^256 - 2^224 + 2^192 + 2^96 - 1.

#[export] Instance prime_p256 : prime p256. Admitted.

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

Lemma p256_mul_mod_n (a b : Z) (P : Wpoint) :
  W.eq (W.mul a P) (W.mul b P) <->
  a mod p256_group_order = b mod p256_group_order.
Proof. Admitted.
