Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.GaloisField.
Require Import Crypto.Curves.PointFormats.

Definition two_255_19 := 2^255 - 19. (* <http://safecurves.cr.yp.to/primeproofs.html> *)
Fact two_255_19_prime : prime two_255_19. Admitted.
Module Modulus25519 <: Modulus.
  Definition modulus := exist _ two_255_19 two_255_19_prime.
End Modulus25519.

Module Curve25519Params <: TwistedEdwardsParams Modulus25519 <: Minus1Params Modulus25519.
  Module Import GFDefs := GaloisField Modulus25519.
  Local Open Scope GF_scope.

  Definition a : GF := -1.
  Definition d : GF := -121665 / 121666.

  Lemma a_nonzero : a <> 0.
  Proof.
    discriminate.
  Qed.

  Definition sqrt_a: GF := 19681161376707505956807079304988542015446066515923890162744021073123829784752.

  Lemma a_square : sqrt_a^2 = a.
  Proof.
    (* vm_compute runs out of memory. *) 
  Admitted.

  Lemma  d_nonsquare : forall x, x * x <> d.
    (* <https://en.wikipedia.org/wiki/Euler%27s_criterion> *)
  Admitted.

  Definition A : GF := 486662.
  (* Definition montgomeryOnCurve25519 := montgomeryOnCurve 1 A. *)

  (* Module-izing Twisted was a breaking change
  Definition m1TwistedOnCurve25519 := twistedOnCurve (0 -1) d.

  Definition identityTwisted : twisted := mkTwisted 0 1.

  Lemma identityTwistedOnCurve : m1TwistedOnCurve25519 identityTwisted.
    unfold m1TwistedOnCurve25519, twistedOnCurve.
    simpl; field.
  Qed.

  *)

  Definition basepointY := 4 / 5.

  Definition char_gt_2: (1+1) <> 0.
  Admitted.
End Curve25519Params.

Module Edwards25519 := CompleteTwistedEdwardsCurve Modulus25519 Curve25519Params.
Module Edwards25519Minus1Twisted := Minus1Format Modulus25519 Curve25519Params.
