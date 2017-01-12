Require Import Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Local Open Scope ctype_scope.
Local Open Scope expr_scope.

Section language.
  Context {base_type_code : Type}
          {interp_base_type : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).

  Local Notation exprf := (@exprf base_type_code op interp_base_type).
  Local Notation expr := (@expr base_type_code op interp_base_type).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation interpf := (@interpf base_type_code interp_base_type op interp_op).
  Local Notation interp := (@interp base_type_code interp_base_type op interp_op).
  Local Notation Interp := (@Interp base_type_code interp_base_type op interp_op).

  Lemma eq_in_flatten_binding_list
        {t x x' T e}
        (HIn : List.In (existT (fun t : base_type_code => (interp_base_type t * interp_base_type t)%type) t (x, x')%core)
                       (flatten_binding_list (t:=T) e e))
    : x = x'.
  Proof.
    induction T; simpl in *; [ | | rewrite List.in_app_iff in HIn ];
      repeat first [ progress destruct_head or
                   | progress destruct_head False
                   | progress destruct_head and
                   | progress inversion_sigma
                   | progress inversion_prod
                   | progress subst
                   | solve [ eauto ] ].
  Qed.


  Local Hint Resolve List.in_app_or List.in_or_app eq_in_flatten_binding_list.

  Section wf.
    Lemma interpf_wff
             {t} {e1 e2 : exprf t}
             {G}
             (HG : forall t x x',
                 List.In (existT (fun t : base_type_code => (interp_base_type t * interp_base_type t)%type) t (x, x')%core) G
                 -> x = x')
             (Rwf : wff G e1 e2)
    : interpf e1 = interpf e2.
    Proof.
      induction Rwf; simpl; auto;
        specialize_by auto; try congruence.
      rewrite_hyp !*; auto.
      repeat match goal with
             | [ H : context[List.In _ (_ ++ _)] |- _ ]
               => setoid_rewrite List.in_app_iff in H
             end.
      match goal with
      | [ H : _ |- _ ]
        => apply H; intros; destruct_head' or; solve [ eauto ]
      end.
    Qed.

    Local Hint Resolve interpf_wff.

    Lemma interp_wf
             {t} {e1 e2 : expr t}
             (Rwf : wf e1 e2)
    : forall x, interp e1 x = interp e2 x.
    Proof.
      destruct Rwf; simpl; eauto.
    Qed.
  End wf.
End language.
