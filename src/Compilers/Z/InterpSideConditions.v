Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.InterpSideConditions.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Notations.

Definition InterpSideConditions {t} (e : Expr base_type op t) : interp_flat_type interp_base_type (domain t) -> pointed_Prop
    := InterpSideConditions interp_op (@interped_op_side_conditions) e.
