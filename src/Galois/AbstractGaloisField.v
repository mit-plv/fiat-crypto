
Require Import BinInt BinNat ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import Tactics.VerdiTactics.
Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory.

Module AbstractGaloisField (M: Modulus).
  Module G := Galois M.
  Module T := GaloisTheory M.
  Export M G T.

  Add Field GFfield_computational : GFfield_theory
    (power_tac GFpower_theory [GFexp_tac]).
End AbstractGaloisField.
