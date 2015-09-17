
Require Import Zpower ZArith Znumtheory.
Require Import Crypto.Galois.GaloisField Crypto.Galois.GaloisFieldTheory.

Definition prime25519 : Prime.
  exists ((two_p 255) - 19).
  (* <http://safecurves.cr.yp.to/proof/57896044618658097711785492504343953926634992332820282019728792003956564819949.html> *)
Admitted.

Module Modulus25519 <: Modulus.
  Definition modulus := prime25519.
End Modulus25519.

Declare Module GaloisField25519 : GaloisField Modulus25519.

Declare Module GaloisTheory25519 : GaloisFieldTheory Modulus25519 GaloisField25519.

Module Curve25519.
  Import Modulus25519 GaloisField25519 GaloisTheory25519.

  (* Prove some theorems! *)
End Curve25519.

