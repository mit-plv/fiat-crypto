
Require Export Crypto.Galois.Galois Crypto.Galois.GaloisTheory.
Require Import Crypto.Galois.GaloisField.

Module GaloisRep (M: Modulus).
  Module G := Galois M.
  Module F := GaloisField M.
  Import M G F.
  Local Open Scope GF_scope.

  (* Definition GFSig : ADTSig :=
    ADTsignature {
        Constructor "FromGF"
               : GF -> rep,
        Method "ToGF"
               : rep -> GF,
        Method "Add"
               : rep x rep -> rep,
        Method "Mult"
               : rep x rep -> rep,
        Method "Sub"
               : rep x rep -> rep,
        Method "Div"
               : rep x rep -> rep
      }. *)
End GaloisRep.
