(** * Inline: Remove some [Let] expressions *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.InlineWf.
Require Import Crypto.Reflection.InterpProofs.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.


Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type interp_base_type.
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation wff := (@wff base_type_code interp_base_type op).
  Local Notation wf := (@wf base_type_code interp_base_type op).

  Local Hint Extern 1 => eapply interpf_SmartConst.
  Local Hint Extern 1 => eapply interpf_SmartVarVar.

  Local Ltac t_fin :=
    repeat match goal with
           | _ => reflexivity
           | _ => progress simpl in *
           | _ => progress intros
           | _ => progress inversion_sigma
           | _ => progress inversion_prod
           | _ => solve [ intuition eauto ]
           | _ => apply (f_equal (interp_op _ _ _))
           | _ => apply (f_equal2 (@pair _ _))
           | _ => progress specialize_by assumption
           | _ => progress subst
           | [ H : context[List.In _ (_ ++ _)] |- _ ] => setoid_rewrite List.in_app_iff in H
           | [ H : or _ _ |- _ ] => destruct H
           | _ => progress break_match
           | _ => rewrite <- !surjective_pairing
           | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
           | [ H : _ |- _ ] => apply H
           | [ H : _ |- _ ] => rewrite H
           end.

  Lemma interpf_inline_constf G {t} e1 e2
        (wf : @wff _ _ G t e1 e2)
        (H : forall t x x',
            List.In
              (existT (fun t : base_type_code => (exprf (Syntax.Tbase t) * interp_base_type t)%type) t
                      (x, x')) G
            -> interpf interp_op x = x')
    : interpf interp_op (inline_constf e1) = interpf interp_op e2.
  Proof.
    clear -wf H.
    induction wf; t_fin.
  Qed.

  Local Hint Resolve interpf_inline_constf.

  Lemma interp_inline_const G {t} e1 e2
        (wf : @wf _ _ G t e1 e2)
        (H : forall t x x',
            List.In
              (existT (fun t : base_type_code => (exprf (Syntax.Tbase t) * interp_base_type t)%type) t
                      (x, x')) G
            -> interpf interp_op x = x')
    : interp_type_gen_rel_pointwise interp_flat_type (fun _ => @eq _)
                                    (interp interp_op (inline_const e1))
                                    (interp interp_op e2).
  Proof.
    induction wf.
    { eapply interpf_inline_constf; eauto. }
    { simpl in *; intro.
      match goal with
      | [ H : _ |- _ ]
        => apply H; intuition (inversion_sigma; inversion_prod; subst; eauto)
      end. }
  Qed.

  Lemma Interp_InlineConst {t} (e : Expr t)
        (wf : Wf e)
    : interp_type_gen_rel_pointwise interp_flat_type (fun _ => @eq _)
                                    (Interp interp_op (InlineConst e))
                                    (Interp interp_op e).
  Proof.
    unfold Interp, InlineConst.
    eapply interp_inline_const with (G := nil); simpl; intuition.
  Qed.
End language.
