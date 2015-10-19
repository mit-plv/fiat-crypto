
Require Export Crypto.Galois.Galois Crypto.Galois.GaloisTheory.
Require Import Crypto.Galois.AbstractGaloisField.

Module ECRep (M: Modulus).
  Module G := Galois M.
  Module F := AbstractGaloisField M.
  Import M G F.
  Local Open Scope GF_scope.

  Definition ECSig : ADTSig :=
    ADTsignature {
        Constructor "FromTwistedXY"
               : GF x GF -> rep,
        Method "Add"
               : rep x rep -> rep,
      }.
End ECRep.
