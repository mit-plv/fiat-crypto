Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.MapCastByDeBruijn.
Require Import Crypto.Reflection.Z.Syntax.

Section language.
  Context {interp_base_type_bounds : base_type -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).
  Context (cast_op : forall t tR (opc : op t tR) args_bs,
              op (pick_type args_bs) (pick_type (interp_op_bounds t tR opc args_bs))).
  Context {t : type base_type}.

  Definition MapCastCompile := @MapCastCompile base_type op t.
  Definition MapCastDoCast
    := @MapCastDoCast
         base_type op base_type_beq internal_base_type_dec_bl
         interp_base_type_bounds interp_op_bounds pick_typeb cast_op t.
  Definition MapCastDoInterp
    := @MapCastDoInterp
         base_type op base_type_beq internal_base_type_dec_bl
         (fun _ t => Op (OpConst 0%Z) TT)
         interp_base_type_bounds pick_typeb t.
  Definition MapCast e input_bounds
    := MapCastDoInterp input_bounds (MapCastDoCast input_bounds (MapCastCompile e)).
End language.
