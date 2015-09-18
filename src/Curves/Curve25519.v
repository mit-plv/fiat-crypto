Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.GaloisField Crypto.Galois.GaloisFieldTheory.
Require Import Crypto.Curves.PointFormats.

Definition two_255_19 := (two_p 255) - 19.
Lemma two_255_19_prime : prime two_255_19.
  (* <http://safecurves.cr.yp.to/proof/57896044618658097711785492504343953926634992332820282019728792003956564819949.html>,
  * <https://github.com/sipa/Coin25519/blob/master/spec/primeCerts/prime57896044618658097711785492504343953926634992332820282019728792003956564819949.v#L16> *)
Admitted.

Definition prime25519 := exist _ two_255_19 two_255_19_prime.
Local Notation p := two_255_19.

Module Modulus25519 <: Modulus.
  Definition modulus := prime25519.
End Modulus25519.

Module Curve25519.
  Module PointFormats25519 := PointFormats Modulus25519.
  Import Modulus25519 PointFormats25519 PointFormats25519.Theory PointFormats25519.Field.
  Local Open Scope GF_scope.

  Definition A : GF := ZToGF 486662.
  Definition d : GF := ((0 -ZToGF 121665) / (ZToGF 121666))%GF.


  Definition montgomeryOnCurve25519 := montgomeryOnCurve 1 A.
  Definition m1TwistedOnCurve25519 := twistedOnCurve (0 -1) d.

  Definition identityTwisted : twisted := mkTwisted 0 1.

  Lemma identityTwistedOnCurve : m1TwistedOnCurve25519 identityTwisted.
    unfold m1TwistedOnCurve25519, twistedOnCurve, identityTwisted.
    simpl; field.
  Qed.

  Definition basepointY := ZToGF 4 / ZToGF 5.
  (* TODO(andreser): implement (in PointFormats) recoverX from <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
End Curve25519.

