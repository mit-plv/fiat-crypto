Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.BoundByCast.
Require Import Crypto.Reflection.SmartBound.
Require Import Crypto.Reflection.SmartBoundInterp.
Require Import Crypto.Reflection.SmartBoundWf.
Require Import Crypto.Reflection.InlineCastInterp.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.LinearizeWf.
Require Import Crypto.Reflection.MapCastInterp.
Require Import Crypto.Reflection.MapCastWf.
Require Import Crypto.Reflection.EtaInterp.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_base_type interp_base_type_bounds : base_type_code -> Type)
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (bound_base_type : forall t, interp_base_type_bounds t -> base_type_code)
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (cast_val : forall A A', interp_base_type A -> interp_base_type A')
          (is_cast : forall src dst, op src dst -> bool)
          (is_const : forall src dst, op src dst -> bool)
          (genericize_op : forall src dst (opc : op src dst) (new_bounded_type_in new_bounded_type_out : base_type_code),
              option { src'dst' : _ & op (fst src'dst') (snd src'dst') })
          (failf : forall var t, @exprf base_type_code op var (Tbase t))
          (bound_is_good : forall t, interp_base_type_bounds t -> Prop)
          (is_bounded_by_base : forall t, interp_base_type t -> interp_base_type_bounds t -> Prop)
          (interpf_Cast_id : forall A x, interpf interp_op (Cast _ A A x) = interpf interp_op x)
          (interpf_cast : forall A A' e, interpf interp_op (Cast _ A A' e) = cast_val A A' (interpf interp_op e))
          (cast_val_squash : forall a b c v,
              base_type_min base_type_leb b (base_type_min base_type_leb a c) = base_type_min base_type_leb a c
              -> cast_val b c (cast_val a b v) = cast_val a c v)
          (is_cast_correct : forall s d opc e, is_cast (Tbase s) (Tbase d) opc = true
                                               -> interp_op _ _ opc (interpf interp_op e)
                                                  = interpf interp_op (Cast _ s d e))
          (wff_Cast : forall var1 var2 G A A' e1 e2,
              wff G e1 e2 -> wff G (Cast var1 A A' e1) (Cast var2 A A' e2))
          (strip_cast_val
           : forall t x y,
              is_bounded_by_base t y x ->
              cast_val (bound_base_type t x) t (cast_val t (bound_base_type t x) y) = y).
  Local Notation is_bounded_by (*{T} : interp_flat_type interp_base_type T -> interp_flat_type interp_base_type_bounds T -> Prop*)
    := (interp_flat_type_rel_pointwise is_bounded_by_base).
  Context (is_bounded_by_interp_op
           : forall src dst opc sv1 sv2,
              is_bounded_by sv1 sv2 ->
              is_bounded_by (interp_op src dst opc sv1) (interp_op_bounds src dst opc sv2)).
  Local Notation bounds_are_good
    := (@interp_flat_type_rel_pointwise1 _ _ bound_is_good).
  Local Notation bound_op := (@bound_op _ _ _ interp_op_bounds bound_base_type _ base_type_bl_transparent base_type_leb Cast genericize_op).
  Local Notation G_invariant_holds G
    := (forall t x x',
           List.In (existT _ t (x, x')%core) G -> is_bounded_by_base t x x')
         (only parsing).
  Context (interpf_bound_op
           : forall G t tR opc ein eout ebounds,
              wff G ein ebounds
              -> G_invariant_holds G
              -> interpf interp_op ein = interpf interp_op eout
              -> bounds_are_recursively_good interp_op_bounds bound_is_good ebounds
              -> bounds_are_good (interp_op_bounds t tR opc (interpf interp_op_bounds ebounds))
              -> interpf interp_op (@bound_op interp_base_type t tR t tR opc opc eout (interpf interp_op_bounds ebounds))
                 = interpf interp_op (Op opc ein)).

  Context (is_bounded_by_bound_op
           : forall G t tR opc ein eout ebounds,
              wff G ein ebounds
              -> G_invariant_holds G
              -> interpf interp_op ein = interpf interp_op eout
              -> bounds_are_recursively_good interp_op_bounds bound_is_good ebounds
              -> bounds_are_good (interp_op_bounds t tR opc (interpf interp_op_bounds ebounds))
              -> is_bounded_by
                   (interpf interp_op (@bound_op interp_base_type t tR t tR opc opc eout (interpf interp_op_bounds ebounds)))
                   (interpf interp_op_bounds (Op opc ebounds))).

  Local Notation Expr := (@Expr base_type_code op).
  Local Notation Boundify := (@Boundify _ _ _ interp_op_bounds bound_base_type _ base_type_bl_transparent base_type_leb Cast is_cast is_const genericize_op failf).
  Local Notation interpf_smart_unbound := (@interpf_smart_unbound _ interp_base_type_bounds bound_base_type interp_base_type cast_val).

  Lemma InterpBoundifyAndRel {t}
        (e : Expr t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
        (output_bounds := Interp interp_op_bounds e input_bounds)
        (e' := Boundify e input_bounds)
        (Hgood : bounds_are_recursively_good
                   (@interp_op_bounds) bound_is_good
                   (invert_Abs (e _) input_bounds))
    : forall x,
      is_bounded_by (interpf_smart_unbound input_bounds x) input_bounds
      -> is_bounded_by (Interp interp_op e (interpf_smart_unbound input_bounds x)) output_bounds
         /\ interpf_smart_unbound _ (Interp interp_op e' x)
            = Interp interp_op e (interpf_smart_unbound input_bounds x).
  Proof using cast_val_squash interpf_Cast_id interpf_bound_op interpf_cast is_bounded_by_bound_op is_bounded_by_interp_op is_cast_correct strip_cast_val wff_Cast.
    intros; subst e' output_bounds.
    unfold Boundify.
    erewrite InterpExprEta, InterpInlineCast, InterpLinearize by eauto with wf.
    match goal with |- ?A /\ ?B => cut (A /\ (A -> B)); [ tauto | ] end.
    split.
    { apply interp_wf; auto. }
    { intro Hbounded_out.
      erewrite InterpSmartBound, InterpMapInterpCast by eauto with wf.
      reflexivity. }
  Qed.
End language.
