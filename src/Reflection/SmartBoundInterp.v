Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.InterpWfRel.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.SmartMap.
(*Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.BoundByCast.*)
Require Import Crypto.Reflection.SmartBound.
Require Import Crypto.Reflection.ExprInversion.
(*Require Import Crypto.Reflection.SmartBoundWf.
Require Import Crypto.Reflection.InlineCastInterp.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.LinearizeWf.
Require Import Crypto.Reflection.MapCastInterp.
Require Import Crypto.Reflection.MapCastWf.
Require Import Crypto.Reflection.EtaInterp.*)
Require Import Crypto.Util.Tactics.DestructHead.

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
          (genericize_op : forall src dst (opc : op src dst) (new_bounded_type_in new_bounded_type_out : base_type_code),
              option { src'dst' : _ & op (fst src'dst') (snd src'dst') })
          (failf : forall var t, @exprf base_type_code op var (Tbase t))
          (is_bounded_by_base : forall t, interp_base_type t -> interp_base_type_bounds t -> Prop)
          (interpf_cast : forall A A' e, interpf interp_op (Cast _ A A' e) = cast_val A A' (interpf interp_op e))
          (strip_cast_val
           : forall t x y,
              is_bounded_by_base t y x ->
              cast_val (bound_base_type t x) t (cast_val t (bound_base_type t x) y) = y).
(*
          (wff_Cast : forall var1 var2 G A A' e1 e2,
              wff G e1 e2 -> wff G (Cast var1 A A' e1) (Cast var2 A A' e2)).*)

  Local Notation is_bounded_by (*{T} : interp_flat_type interp_base_type T -> interp_flat_type interp_base_type_bounds T -> Prop*)
    := (interp_flat_type_rel_pointwise is_bounded_by_base).
  Context (is_bounded_by_interp_op
           : forall src dst opc sv1 sv2,
              is_bounded_by sv1 sv2 ->
              is_bounded_by (interp_op src dst opc sv1) (interp_op_bounds src dst opc sv2)).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation SmartBound := (@SmartBound _ _ _ interp_op_bounds bound_base_type Cast).
  Local Notation smart_bound := (@smart_bound _ _ interp_base_type_bounds bound_base_type Cast).
  Local Notation interpf_smart_bound := (@interpf_smart_bound _ interp_base_type_bounds bound_base_type interp_base_type cast_val).
  Local Notation interpf_smart_unbound := (@interpf_smart_unbound _ interp_base_type_bounds bound_base_type interp_base_type cast_val).
  Local Notation interpf_smart_bound_exprf := (@interpf_smart_bound_exprf _ op interp_base_type_bounds bound_base_type Cast).
  Local Notation interpf_smart_unbound_exprf := (@interpf_smart_unbound_exprf _ op interp_base_type_bounds bound_base_type Cast).
  Local Notation bound_op := (@bound_op _ _ _ interp_op_bounds bound_base_type _ base_type_bl_transparent base_type_leb Cast genericize_op).

  Local Ltac t :=
    unfold SmartPairf, SmartBound.interpf_smart_bound, SmartBound.interpf_smart_bound_exprf;
    repeat first [ reflexivity
                 | progress destruct_head' unit
                 | progress simpl in *
                 | rewrite !interpf_cast
                 | match goal with H : _ |- _ => setoid_rewrite H end ].
  Lemma interpf_SmartPairf_interpf_smart_bound_exprf
        {t} e bounds
    : interpf interp_op (SmartPairf (interpf_smart_bound_exprf (t:=t) e bounds))
      = interpf_smart_bound e bounds.
  Proof. clear -interpf_cast; induction t; t. Qed.

  Lemma interpf_SmartPairf_interpf_smart_unbound_exprf
        {t} bounds e
    : interpf interp_op (SmartPairf (interpf_smart_unbound_exprf (t:=t) bounds e))
      = interpf_smart_unbound bounds (SmartVarfMap (fun _ e => interpf interp_op e) e).
  Proof. clear -interpf_cast; induction t; t. Qed.

  Lemma interp_smart_bound_and_rel {t}
        (e : expr t) (ebounds : expr t)
        (Hwf : wf e ebounds)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
        (output_bounds := interp interp_op_bounds ebounds input_bounds)
        (e' := smart_bound e (interp interp_op_bounds ebounds) input_bounds)
    : forall x,
      is_bounded_by (interpf_smart_unbound input_bounds x) input_bounds
      -> is_bounded_by (interp interp_op e (interpf_smart_unbound input_bounds x)) output_bounds
         /\ interpf_smart_unbound _ (interp interp_op e' x)
            = interp interp_op e (interpf_smart_unbound input_bounds x).
  Proof.
    intros; subst e' output_bounds.
    match goal with |- ?A /\ ?B => cut (A /\ (A -> B)); [ tauto | ] end.
    split.
    { apply interp_wf; auto. }
    { intro Hbounded_out.
      unfold smart_bound; simpl.
      cbv [LetIn.Let_In].
      rewrite interpf_invert_Abs, interpf_SmartPairf_interpf_smart_bound_exprf, interpf_SmartPairf_interpf_smart_unbound_exprf, SmartVarfMap_compose; simpl.
      rewrite SmartVarfMap_id.
      setoid_rewrite SmartFlatTypeMapUnInterp2_SmartFlatTypeMap2Interp2.
      etransitivity; [ | eapply SmartVarfMap2_snd_arg ].
      apply lift_interp_flat_type_rel_pointwise_f_eq2.
      eauto using interp_flat_type_rel_pointwise_impl', interp_flat_type_rel_pointwise_always. }
  Qed.

  Lemma InterpSmartBoundAndRel {t}
        (e : Expr t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
        (output_bounds := Interp interp_op_bounds e input_bounds)
        (e' := SmartBound e input_bounds)
        (*(Hgood : bounds_are_recursively_good
                   (@interp_op_bounds) bound_is_good
                   (invert_Abs (e _) input_bounds))*)
    : forall x,
      is_bounded_by (interpf_smart_unbound input_bounds x) input_bounds
      -> is_bounded_by (Interp interp_op e (interpf_smart_unbound input_bounds x)) output_bounds
         /\ interpf_smart_unbound _ (Interp interp_op e' x)
            = Interp interp_op e (interpf_smart_unbound input_bounds x).
  Proof.
    apply interp_smart_bound_and_rel; auto.
  Qed.

  Lemma InterpSmartBound {t}
        (e : Expr t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
        (output_bounds := Interp interp_op_bounds e input_bounds)
        (e' := SmartBound e input_bounds)
        (*(Hgood : bounds_are_recursively_good
                   (@interp_op_bounds) bound_is_good
                   (invert_Abs (e _) input_bounds))*)
    : forall x,
      is_bounded_by (interpf_smart_unbound input_bounds x) input_bounds
      -> interpf_smart_unbound _ (Interp interp_op e' x)
         = Interp interp_op e (interpf_smart_unbound input_bounds x).
  Proof.
    intros; eapply InterpSmartBoundAndRel; auto.
  Qed.
End language.
