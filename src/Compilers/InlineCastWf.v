Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.TypeInversion.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.WfInversion.
Require Import Crypto.Compilers.InlineCast.
Require Import Crypto.Compilers.InlineWf.
Require Import Crypto.Compilers.SmartCast.
Require Import Crypto.Compilers.SmartCastWf.
Require Import Crypto.Compilers.Inline.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Local Open Scope expr_scope.
Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (base_type_beq : base_type_code -> base_type_code -> bool)
          (base_type_bl_transparent : forall x y, base_type_beq x y = true -> x = y)
          (base_type_leb : base_type_code -> base_type_code -> bool)
          (Cast : forall var A A', exprf base_type_code op (var:=var) (Tbase A) -> exprf base_type_code op (var:=var) (Tbase A'))
          (is_cast : forall src dst, op src dst -> bool)
          (is_const : forall src dst, op src dst -> bool)
          (wff_Cast : forall var1 var2 G A A' e1 e2,
              wff G e1 e2 -> wff G (Cast var1 A A' e1) (Cast var2 A A' e2)).
  Local Infix "<=?" := base_type_leb : expr_scope.
  Local Infix "=?" := base_type_beq : expr_scope.

  Local Notation SmartCast_base := (@SmartCast_base _ op _ base_type_bl_transparent Cast).
  Local Notation squash_cast := (@squash_cast _ op _ base_type_bl_transparent base_type_leb Cast).
  Local Notation maybe_push_cast := (@maybe_push_cast _ op _ base_type_bl_transparent base_type_leb Cast is_cast is_const).
  Local Notation push_cast := (@push_cast _ op _ base_type_bl_transparent base_type_leb Cast is_cast is_const).
  Local Notation InlineCast := (@InlineCast _ op _ base_type_bl_transparent base_type_leb Cast is_cast is_const).

  Lemma wff_squash_cast var1 var2 a b c e1 e2 G
        (Hwf : wff G e1 e2)
    : wff G (@squash_cast var1 a b c e1) (@squash_cast var2 a b c e2).
  Proof using wff_Cast.
    unfold squash_cast; break_innermost_match; auto with wf.
  Qed.

  Local Opaque InlineCast.squash_cast.

  Lemma wff_maybe_push_cast_match {var1 var2 t e1 e2 G}
        (Hwf : wff G e1 e2)
    : match @maybe_push_cast var1 t e1, @maybe_push_cast var2 t e2 with
      | Some e1', Some e2' => wff G e1' e2'
      | None, None => True
      | Some _, None | None, Some _ => False
      end.
  Proof using wff_Cast.
    induction Hwf;
      repeat match goal with
             | [ |- wff _ (squash_cast _ _ _ _) (squash_cast _ _ _ _) ]
               => apply wff_squash_cast
             | _ => progress subst
             | _ => progress destruct_head' sig
             | _ => progress destruct_head' and
             | _ => progress inversion_option
             | _ => progress simpl in *
             | _ => congruence
             | _ => progress break_innermost_match_step
             | _ => intro
             | [ H : forall e1 e2, Some _ = Some e1 -> _ |- _ ]
               => specialize (fun e2 => H _ e2 eq_refl)
             | [ H : forall e, Some _ = Some e -> _ |- _ ]
               => specialize (H _ eq_refl)
             | _ => solve [ auto with wf ]
             | _ => progress inversion_wf_constr
             | _ => progress inversion_flat_type
             | [ H : context[match ?e with _ => _ end] |- _ ] => invert_one_expr e
             | [ |- context[match ?e with _ => _ end] ] => invert_one_expr e
             end.
  Qed.

  Lemma wff_maybe_push_cast var1 var2 t e1 e2 G e1' e2'
        (Hwf : wff G e1 e2)
    : @maybe_push_cast var1 t e1 = Some e1'
      -> @maybe_push_cast var2 t e2 = Some e2'
      -> wff G e1' e2'.
  Proof using wff_Cast.
    intros H0 H1; eapply wff_maybe_push_cast_match in Hwf.
    rewrite H0, H1 in Hwf; assumption.
  Qed.

  Local Notation wff_inline_directive G x y :=
    (wff G (exprf_of_inline_directive x) (exprf_of_inline_directive y)
     /\ (fun x' y'
         => match x', y' with
            | default_inline _ _, default_inline _ _
            | no_inline _ _, no_inline _ _
            | inline _ _, inline _ _
              => True
            | default_inline _ _, _
            | no_inline _ _, _
            | inline _ _, _
              => False
            end) x y).

  Lemma wff_push_cast var1 var2 t e1 e2 G
        (Hwf : wff G e1 e2)
    : wff_inline_directive G (@push_cast var1 t e1) (@push_cast var2 t e2).
  Proof using wff_Cast.
    pose proof (wff_maybe_push_cast_match Hwf).
    unfold push_cast; destruct t;
      break_innermost_match;
      repeat first [ apply conj
                   | exact I
                   | progress simpl in *
                   | exfalso; assumption
                   | assumption ].
  Qed.

  Lemma wff_exprf_of_push_cast var1 var2 t e1 e2 G
        (Hwf : wff G e1 e2)
    : wff G
          (exprf_of_inline_directive (@push_cast var1 t e1))
          (exprf_of_inline_directive (@push_cast var2 t e2)).
  Proof using wff_Cast. apply wff_push_cast; assumption. Qed.

  Local Hint Resolve wff_push_cast.

  Lemma Wf_InlineCast {t} e (Hwf : Wf e)
    : Wf (@InlineCast t e).
  Proof using wff_Cast. apply Wf_InlineConstGen; auto. Qed.
End language.

Hint Resolve Wf_InlineCast : wf.
