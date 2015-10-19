
Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory.
Require Import Crypto.Galois.ComputationalGaloisField.
Require Import Crypto.Galois.AbstractGaloisField.

Definition two_5_1 := (two_p 5) - 1.
Lemma two_5_1_prime : prime two_5_1.
Admitted.

Definition two_127_1 := (two_p 127) - 1.
Lemma two_127_1_prime : prime two_127_1.
Admitted.

Module Modulus31 <: Modulus.
  Definition modulus := exist _ two_5_1 two_5_1_prime.
End Modulus31.

Module Modulus127_1 <: Modulus.
  Definition modulus := exist _ two_127_1 two_127_1_prime.
End Modulus127_1.

Module Example31.
  Module Field := Galois Modulus31.
  Module Theory := ComputationalGaloisField Modulus31.
  Import Modulus31 Theory Field.
  Local Open Scope GF_scope.

  Lemma example1: forall x y z: GF, z <> 0 -> x * (y / z) / z = x * y / (z ^ 2).
  Proof.
    intros; simpl.
    field; trivial.
  Qed.

  Lemma example2: forall x: GF, x * (ZToGF 2) = x + x.
  Proof.
    intros; simpl.
    field.
  Qed.

  Lemma example3: forall x: GF, x ^ 2 + (ZToGF 2) * x + (ZToGF 1) = (x + (ZToGF 1)) ^ 2.
  Proof.
    intros; simpl.
    field; trivial.
  Qed.

End Example31.

Module TimesZeroTransparentTestModule.
  Module Theory := ComputationalGaloisField Modulus127_1.
  Import Modulus127_1 Theory Theory.Field.
  Local Open Scope GF_scope.

  Lemma timesZero : forall a, a*0 = 0.
    intros.
    field.
  Qed.
End TimesZeroTransparentTestModule.

Module TimesZeroParametricTestModule (M: Modulus).
  Module Theory := AbstractGaloisField M.
  Import M Theory Theory.Field.
  Local Open Scope GF_scope.

  Lemma timesZero : forall a, a*0 = 0.
    intros.
    field.
    ring. (* field doesn't work but ring does :) *)
  Qed.
End TimesZeroParametricTestModule.
