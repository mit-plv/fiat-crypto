Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.ZExtended.Syntax.
Require Import Crypto.Compilers.ZExtended.Syntax.Util.
Require Import Crypto.Compilers.MapBaseType.

Definition MapBaseType' {t} (e : Expr t)
  : Z.Syntax.Expr (Arrow (lift_flat_type unextend_base_type (domain t))
                         (lift_flat_type unextend_base_type (codomain t)))
  := @MapBaseType' _ _ _ _ unextend_base_type (fun _ s d opc _ => unextend_op opc)
                   (fun _ t => Op (make_const t (ZToInterp 0)) TT)
                   t e.

Definition MapBaseType {t} (e : Expr t)
  : option (Z.Syntax.Expr (Arrow (lift_flat_type unextend_base_type (domain t))
                                 (lift_flat_type unextend_base_type (codomain t))))
  := @MapBaseType _ _ _ _ unextend_base_type (fun _ s d opc _ => unextend_op opc)
                  (fun _ t => Op (make_const t (ZToInterp 0)) TT)
                  t e.
