Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory Crypto.Galois.ComputationalGaloisField.
Require Import Crypto.Curves.PointFormats.

Module Curve25519.
  Import M.
  Module Import GT := GaloisTheory M.
  Local Open Scope GF_scope.

  Definition A : GF := ZToGF 486662.
  Definition d : GF := ((0 -ZToGF 121665) / (ZToGF 121666))%GF.

  (* Definition montgomeryOnCurve25519 := montgomeryOnCurve 1 A. *)

  (* Module-izing Twisted was a breaking change
  Definition m1TwistedOnCurve25519 := twistedOnCurve (0 -1) d.

  Definition identityTwisted : twisted := mkTwisted 0 1.

  Lemma identityTwistedOnCurve : m1TwistedOnCurve25519 identityTwisted.
    unfold m1TwistedOnCurve25519, twistedOnCurve.
    simpl; field.
  Qed.

  *)

  Definition basepointY := ZToGF 4 / ZToGF 5.
  (* TODO(andreser): implement (in PointFormats) recoverX from <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
End Curve25519.

