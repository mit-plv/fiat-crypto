Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.GaloisField Crypto.Galois.GaloisFieldTheory.


Definition two_127_1 := (two_p 127) - 1.
Lemma two_127_1_prime : prime two_127_1.
Admitted.

Module Modulus127_1 <: Modulus.
  Definition modulus := exist _ two_127_1 two_127_1_prime.
End Modulus127_1.

Module TimesZeroTransparentTestModule.
  Module Theory := GaloisFieldTheory Modulus127_1.
  Import Modulus127_1 Theory Theory.Field.
  Local Open Scope GF_scope.

  Lemma timesZero : forall a, a*0 = 0.
    intros.
    field.
  Qed.
End TimesZeroTransparentTestModule.

Module TimesZeroParametricTestModule (M: Modulus).
  Module Theory := GaloisFieldTheory M.
  Import M Theory Theory.Field.
  Local Open Scope GF_scope.

  Lemma timesZero : forall a, a*0 = 0.
    intros.
    (*
    field. (*not a valid field equation*)
    *)
  Abort.
End TimesZeroParametricTestModule .
