Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.MapCastByDeBruijn.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.Z.Bounds.Interpretation.

Section language.
  Context (round_up : nat -> option nat)
          {t : type base_type}.

  Definition MapCastCompile := @MapCastCompile t.
  Definition MapCastDoCast
    := @MapCastDoCast
         (@Bounds.interp_base_type) (@Bounds.interp_op)
         (@Bounds.bounds_to_base_type round_up)
         (fun _ _ opc _ => @genericize_op _ _ _ opc _ _ _)
         t.
  Definition MapCastDoInterp
    := @MapCastDoInterp
         (@Bounds.interp_base_type) (@Bounds.bounds_to_base_type round_up)
         t.
  Definition MapCast e input_bounds
    := MapCastDoInterp input_bounds (MapCastDoCast input_bounds (MapCastCompile e)).
End language.
