Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartBound.
Require Import Crypto.Reflection.InlineCast.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Reflection.MapCast.
Require Import Crypto.Reflection.Eta.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_base_type_bounds : base_type_code -> Type)
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (bound_base_type : forall t, interp_base_type_bounds t -> base_type_code)
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (is_cast : forall src dst, op src dst -> bool)
          (is_const : forall src dst, op src dst -> bool)
          (genericize_op : forall src dst (opc : op src dst) (new_bounded_type_in new_bounded_type_out : base_type_code),
              option { src'dst' : _ & op (fst src'dst') (snd src'dst') })
          (failf : forall var t, @exprf base_type_code op var (Tbase t)).

  Local Notation Expr := (@Expr base_type_code op).

  Definition Boundify {t1} (e1 : Expr t1) args2
    : Expr _
    := ExprEta
         (InlineConstGen
            (@push_cast _ _ _ base_type_bl_transparent base_type_leb Cast is_cast is_const)
            (Linearize
               (SmartBound
                  _
                  interp_op_bounds
                  bound_base_type
                  Cast
                  (@MapInterpCast
                     base_type_code interp_base_type_bounds
                     op (@interp_op_bounds)
                     (@failf)
                     (@bound_op _ _ _ interp_op_bounds bound_base_type _ base_type_bl_transparent base_type_leb Cast genericize_op)
                     t1 e1 (interp_all_binders_for_to' args2))
                  (interp_all_binders_for_to' args2)))).
End language.
