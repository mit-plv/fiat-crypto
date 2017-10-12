Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.MapCastByDeBruijnWf.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.MapCastByDeBruijn.

Section language.
  Context {interp_base_type_bounds : base_type -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).
  Context (cast_op : forall t tR (opc : op t tR) args_bs,
              op (pick_type args_bs) (pick_type (interp_op_bounds t tR opc args_bs)))
          (cast_backb: forall t b, interp_base_type (pick_typeb t b) -> interp_base_type t).
  Let cast_back : forall t b, interp_flat_type interp_base_type (pick_type b) -> interp_flat_type interp_base_type t
    := fun t b => SmartFlatTypeMapUnInterp cast_backb.
  Context (inboundsb : forall t, interp_base_type_bounds t -> interp_base_type t -> Prop).
  Let inbounds : forall t, interp_flat_type interp_base_type_bounds t -> interp_flat_type interp_base_type t -> Prop
    := fun t => interp_flat_type_rel_pointwise inboundsb (t:=t).
  Context (interp_op_bounds_correct
           : forall t tR opc bs
                    (v : interp_flat_type interp_base_type t)
                    (H : inbounds t bs v),
              inbounds tR (interp_op_bounds t tR opc bs) (interp_op t tR opc v))
          (pull_cast_back
           : forall t tR opc bs
                    (v : interp_flat_type interp_base_type (pick_type bs))
                    (H : inbounds t bs (cast_back t bs v)),
              interp_op t tR opc (cast_back t bs v)
              =
              cast_back _ _ (interp_op _ _ (cast_op _ _ opc bs) v)).

  Local Notation MapCast
    := (@MapCast interp_base_type_bounds interp_op_bounds pick_typeb cast_op).

  Definition Wf_MapCast
             {t} (e : Expr t)
             (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
             {b} e' (He' : MapCast e input_bounds = Some (existT _ b e'))
             (Hwf : Wf e)
    : Wf e'
    := @Wf_MapCast
         _ _ _ internal_base_type_dec_bl internal_base_type_dec_lb _ _ _ _ _
         t e input_bounds b e' He' Hwf.
  Definition Wf_MapCast_arrow
             {s d} (e : Expr (Arrow s d))
             (input_bounds : interp_flat_type interp_base_type_bounds s)
             {b} e' (He' : MapCast e input_bounds = Some (existT _ b e'))
             (Hwf : Wf e)
    : Wf e'
    := @Wf_MapCast_arrow
         _ _ _ internal_base_type_dec_bl internal_base_type_dec_lb _ _ _ _ _
         s d e input_bounds b e' He' Hwf.
End language.
