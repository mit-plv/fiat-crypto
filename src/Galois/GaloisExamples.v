
Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.GaloisField Crypto.Galois.GaloisFieldTheory.

Definition two_5_1 := (two_p 5) - 1.
Lemma two_5_1_prime : prime two_5_1.
Admitted.

Definition prime31 := exist _ two_5_1 two_5_1_prime.
Local Notation p := two_5_1.

Module Modulus31 <: Modulus.
  Definition modulus := prime31.
End Modulus31.

Module Theory31 := GaloisFieldTheory Modulus31.

Module Example31.
  Import Modulus31 Theory31 Theory31.Field.
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

