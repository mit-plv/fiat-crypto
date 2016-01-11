
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

  (* In general, the rule I've been using is:

     - If our goal looks like x = y:

        + If we need to use assumptions to prove the goal, then before
          we apply field,

          * Perform all relevant substitutions (especially subst)

          * If we have something more complex, we're probably going
            to have to performe some sequence of "replace X with Y"
            and solve out the subgoals manually before we can use
            field.

        + Else, just use field directly

     - If we just want to simplify terms and put them into a canonical
       form, then field_simplify or ring_simplify should do the trick.
       Note, however, that the canonical form has lots of annoying "/1"s

     - Otherwise, do a "replace X with Y" to generate an equality
       so that we can use field in the above case

     *)

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

