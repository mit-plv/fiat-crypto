
Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory.
Require Import Crypto.Galois.GaloisField.

(* First, we define our prime in Z*)
Definition two_5_1 := (two_p 5) - 1.
Definition two_127_1 := (two_p 127) - 1.

(* Then proofs of their primality *)
Lemma two_5_1_prime : prime two_5_1.
Admitted.

Lemma two_127_1_prime : prime two_127_1.
Admitted.

(* And use those to make modulus modules *)
Module Modulus31 <: Modulus.
  Definition modulus := exist _ two_5_1 two_5_1_prime.
End Modulus31.

Module Modulus127_1 <: Modulus.
  Definition modulus := exist _ two_127_1 two_127_1_prime.
End Modulus127_1.

Module Example31.
  (* Then we can construct a field with that modulus *)
  Module Field := GaloisField Modulus31.
  Import Field.

  (* And pull in the appropriate notations *)
  Local Open Scope GF_scope.

  (* First, let's solve a ring example*)
  Lemma ring_example: forall x: GF, x * 2 = x + x.
  Proof.
    intros.
    ring.
  Qed.

  (* Then a field example (we have to know we can't divide by zero!) *)
  Lemma field_example: forall x y z: GF, z <> 0 ->
    x * (y / z) / z = x * y / (z ^ 2).
  Proof.
    intros; simpl.
    field; trivial.
  Qed.

  (* Then an example with exponentiation *)
  Lemma exp_example: forall x: GF, x ^ 2 + 2 * x + 1 = (x + 1) ^ 2.
  Proof.
    intros; simpl.
    field; trivial.
  Qed.

End Example31.

(* Notice that the field tactics work whether we know what the modulus is *)
Module TimesZeroTransparentTestModule.
  Module Theory := GaloisField Modulus127_1.
  Import Theory.
  Local Open Scope GF_scope.

  Lemma timesZero : forall a, a*0 = 0.
    intros.
    field.
  Qed.
End TimesZeroTransparentTestModule.

(* Or if we don't (i.e. it's opaque) *)
Module TimesZeroParametricTestModule (M: Modulus).
  Module Theory := GaloisField M.
  Import Theory.
  Local Open Scope GF_scope.

  Lemma timesZero : forall a, a*0 = 0.
    intros.
    field.
  Qed.
End TimesZeroParametricTestModule.

