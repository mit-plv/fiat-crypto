
Require Export Crypto.Galois.GaloisField.

Module ECRep (M: Modulus).
  Module F := GaloisField M.
  Import F.
  Local Open Scope GF_scope.

  (* Definition ECSig : ADTSig :=
    ADTsignature {
        Constructor "FromTwistedXY"
               : GF x GF -> rep,
        Method "Add"
               : rep x rep -> rep,
      }.*)
End ECRep.
