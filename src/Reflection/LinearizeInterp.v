(** * Linearize: Place all and only operations in let binders *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.LinearizeWf.
Require Import Crypto.Reflection.InterpProofs.
Require Import Crypto.Reflection.Linearize.
Require Import Crypto.Util.Tactics Crypto.Util.Sigma Crypto.Util.Prod.


Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).
  Context (interp_op : forall src dst, op src dst -> interp_flat_type_gen interp_base_type src -> interp_flat_type_gen interp_base_type dst).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type_gen interp_base_type.
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).
  Local Notation wff := (@wff base_type_code interp_base_type op).
  Local Notation wf := (@wf base_type_code interp_base_type op).

  Lemma interpf_SmartConst {t t'} v x x'
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf (Syntax.Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') base_type_code (SmartConst v) v))
    : interpf interp_op x = x'.
  Proof.
    clear -Hin.
    induction t'; simpl in *.
    { intuition (inversion_sigma; inversion_prod; subst; eauto). }
    { apply List.in_app_iff in Hin.
      intuition (inversion_sigma; inversion_prod; subst; eauto). }
  Qed.

  Lemma interpf_SmartVarVar {t t'} v x x'
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf (Syntax.Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') base_type_code (SmartVarVar v) v))
    : interpf interp_op x = x'.
  Proof.
    clear -Hin.
    induction t'; simpl in *.
    { intuition (inversion_sigma; inversion_prod; subst; eauto). }
    { apply List.in_app_iff in Hin.
      intuition (inversion_sigma; inversion_prod; subst; eauto). }
  Qed.

  Lemma interpf_SmartVarVar_eq {t t'} v v' x x'
        (Heq : v = v')
        (Hin : List.In
                 (existT (fun t : base_type_code => (exprf (Syntax.Tbase t) * interp_base_type t)%type)
                         t (x, x'))
                 (flatten_binding_list (t := t') base_type_code (SmartVarVar v') v))
    : interpf interp_op x = x'.
  Proof.
    eapply interpf_SmartVarVar; subst; eassumption.
  Qed.

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

  Lemma interpf_let_bind_const {t tC} ex (eC : _ -> exprf tC)
    : interpf interp_op (let_bind_const (t:=t) ex eC) = interpf interp_op (eC ex).
  Proof.
    clear.
    revert tC eC; induction t; t_fin.
  Qed.

  Lemma interpf_under_letsf {t tC} (ex : exprf t) (eC : _ -> exprf tC)
    : interpf interp_op (under_letsf ex eC) = let x := interpf interp_op ex in interpf interp_op (eC x).
  Proof.
    clear.
    induction ex; t_fin.
    rewrite interpf_let_bind_const; reflexivity.
  Qed.

  Lemma interpf_SmartVar {t} v
    : interpf interp_op (SmartVar (t:=t) v) = v.
  Proof.
    clear.
    unfold SmartVar; induction t; t_fin.
  Qed.

  Lemma interpf_linearizef {t} e
    : interpf interp_op (linearizef (t:=t) e) = interpf interp_op e.
  Proof.
    clear.
    induction e;
      repeat first [ progress rewrite ?interpf_under_letsf, ?interpf_SmartVar
                   | progress simpl
                   | t_fin ].
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

  Local Hint Resolve interpf_linearizef.

  Lemma interp_linearize {t} e
    : interp_type_gen_rel_pointwise interp_flat_type (fun _ => @eq _)
                                    (interp interp_op (linearize (t:=t) e))
                                    (interp interp_op e).
  Proof.
    induction e; eauto.
    eapply interpf_linearizef.
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

  Lemma Interp_Linearize {t} (e : Expr t)
    : interp_type_gen_rel_pointwise interp_flat_type (fun _ => @eq _)
                                    (Interp interp_op (Linearize e))
                                    (Interp interp_op e).
  Proof.
    unfold Interp, Linearize.
    eapply interp_linearize.
  Qed.

  Lemma Interp_InlineConst_Linearize {t} (e : Expr t) (wf : Wf e)
    : interp_type_gen_rel_pointwise interp_flat_type (fun _ => @eq _)
                                    (Interp interp_op (InlineConst (Linearize e)))
                                    (Interp interp_op e).
  Proof.
    etransitivity; [ apply Interp_InlineConst, Wf_Linearize, wf | apply Interp_Linearize ].
  Qed.
End language.
