Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.TypeUtil.
Require Import Crypto.Reflection.TypeInversion.
Require Import Crypto.Reflection.ExprInversion.
Require Import Crypto.Reflection.InlineCast.
Require Import Crypto.Reflection.InlineInterp.
Require Import Crypto.Reflection.SmartCast.
Require Import Crypto.Reflection.SmartCastInterp.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (is_cast : forall src dst, op src dst -> bool)
          (is_const : forall src dst, op src dst -> bool)
          (interpf_Cast_id : forall A x, interpf interp_op (Cast _ A A x) = interpf interp_op x)
          (cast_val : forall A A', interp_base_type A -> interp_base_type A')
          (interpf_cast : forall A A' e, interpf interp_op (Cast _ A A' e) = cast_val A A' (interpf interp_op e))
          (cast_val_squash : forall a b c v,
              base_type_min base_type_leb b (base_type_min base_type_leb a c) = base_type_min base_type_leb a c
              -> cast_val b c (cast_val a b v) = cast_val a c v)
          (is_cast_correct : forall s d opc e, is_cast (Tbase s) (Tbase d) opc = true
                                               -> interp_op _ _ opc (interpf interp_op e)
                                                  = interpf interp_op (Cast _ s d e)).

  Local Notation SmartCast_base := (@SmartCast_base _ op _ base_type_bl_transparent Cast interp_base_type).
  Local Notation squash_cast := (@squash_cast _ op _ base_type_bl_transparent base_type_leb Cast).
  Local Notation maybe_push_cast := (@maybe_push_cast _ op _ base_type_bl_transparent base_type_leb Cast is_cast is_const).
  Local Notation push_cast := (@push_cast _ op _ base_type_bl_transparent base_type_leb Cast is_cast is_const).
  Local Notation InlineCast := (@InlineCast _ op _ base_type_bl_transparent base_type_leb Cast is_cast is_const).
  Local Notation base_type_min := (base_type_min base_type_leb).

  Lemma cast_val_id A (v : exprf _ _ (Tbase A))
    : cast_val A A (interpf interp_op v) = interpf interp_op v.
  Proof. rewrite <- !interpf_cast, !interpf_Cast_id; reflexivity. Qed.

  Lemma interpf_squash_cast a b c e1
    : interpf interp_op (@squash_cast _ a b c e1) = interpf interp_op (Cast _ b c (Cast _ a b e1)).
  Proof.
    unfold squash_cast;
      repeat first [ progress break_innermost_match
                   | intro
                   | reflexivity
                   | progress subst
                   | match goal with H : base_type_beq _ _ = true |- _ => apply base_type_bl_transparent in H end
                   | rewrite !cast_val_id
                   | rewrite !interpf_SmartCast_base by assumption
                   | rewrite !interpf_Cast_id
                   | rewrite interpf_cast
                   | rewrite cast_val_squash by assumption ].
  Qed.

  Lemma interpf_maybe_push_cast t e e'
    : @maybe_push_cast _ t e = Some e'
      -> interpf interp_op e' = interpf interp_op e.
  Proof.
    revert e'; induction e;
      repeat first [ reflexivity
                   | discriminate
                   | progress subst
                   | progress inversion_option
                   | progress break_innermost_match_step
                   | progress simpl in *
                   | intro
                   | rewrite !interpf_SmartCast_base by assumption
                   | setoid_rewrite interpf_SmartCast_base; [ | assumption.. ]
                   | erewrite is_cast_correct by eassumption
                   | progress change (fun t => interp_base_type t) with interp_base_type in *
                   | rewrite !interpf_cast
                   | rewrite !interpf_squash_cast
                   | match goal with
                     | [ H : forall x, Some _ = Some x -> _ |- _ ]
                       => specialize (H _ eq_refl)
                     | [ |- context[interpf (t:=Unit) interp_op ?e] ]
                       => destruct (interpf interp_op e)
                     | [ H : maybe_push_cast ?e = Some _, H' : _ = interpf interp_op ?e |- _ ]
                       => rewrite <- H'; clear e H H'
                     | [ H : context[match ?e with _ => _ end] |- _ ]
                       => invert_one_expr e
                     end ].
  Qed.

  Lemma interpf_exprf_of_push_cast t e
    : interpf interp_op (exprf_of_inline_directive (@push_cast _ t e))
      = interpf interp_op e.
  Proof.
    unfold push_cast; break_innermost_match; simpl; try reflexivity.
    match goal with H : _ |- _ => apply interpf_maybe_push_cast in H end.
    assumption.
  Qed.

  Local Hint Resolve interpf_exprf_of_push_cast.

  Lemma InterpInlineCast {t} e (Hwf : Wf e)
    : interp_type_gen_rel_pointwise (fun _ => @eq _)
                                    (Interp interp_op (@InlineCast t e))
                                    (Interp interp_op e).
  Proof. apply InterpInlineConstGen; auto. Qed.
End language.
