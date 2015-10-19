
Require Import BinInt BinNat ZArith Znumtheory.
Require Import Eqdep_dec.
Require Import Tactics.VerdiTactics.
Require Import Galois GaloisTheory.

Module ComputationalGaloisField (M: Modulus).
  Module G := Galois M.
  Module T := GaloisTheory M.
  Export M G T.

  Ltac isModulusConstant :=
    let hnfModulus := eval hnf in (proj1_sig modulus)
    in match (isZcst hnfModulus) with
    | NotConstant => NotConstant
    | _ => match hnfModulus with
      | Z.pos _ => true
      | _ => false
      end
    end.

  Ltac isGFconstant t :=
    match t with
    | GFzero => true
    | GFone => true
    | ZToGF _ => isModulusConstant
    | exist _ ?z _ => match (isZcst z) with
      | NotConstant => NotConstant
      | _ => isModulusConstant
      end
    | _ => NotConstant
    end.

  Ltac GFconstants t :=
    match isGFconstant t with
    | NotConstant => NotConstant
    | _ => t
    end.

  Add Field GFfield_computational : GFfield_theory
    (decidable GFdecidable,
     completeness GFcomplete,
     constants [GFconstants],
     div GFdiv_theory,
     power_tac GFpower_theory [GFexp_tac]).
End ComputationalGaloisField.
