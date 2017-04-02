Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Z.MapCastByDeBruijn.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.
Require Import Crypto.Reflection.Z.Bounds.Interpretation.

Section language.
  Context (genericize_op : forall t tR (opc : op t tR)
                                  (args_bs : interp_flat_type Bounds.interp_base_type t),
              op (SmartMap.SmartFlatTypeMap (fun _ => Bounds.bounds_to_base_type) args_bs)
                 (SmartMap.SmartFlatTypeMap (fun _ => Bounds.bounds_to_base_type) (Bounds.interp_op opc args_bs))).
  Context {t : type base_type}.

  Definition MapCastCompile := @MapCastCompile t.
  Definition MapCastDoCast
    := @MapCastDoCast
         (@Bounds.interp_base_type) (@Bounds.interp_op)
         (fun _ => @Bounds.bounds_to_base_type)
         (fun _ _ opc _ => @genericize_op _ _ opc _)
         t.
  Definition MapCastDoInterp
    := @MapCastDoInterp
         (@Bounds.interp_base_type) (fun _ => @Bounds.bounds_to_base_type)
         t.
  Definition MapCast e input_bounds
    := MapCastDoInterp input_bounds (MapCastDoCast input_bounds (MapCastCompile e)).
End language.
