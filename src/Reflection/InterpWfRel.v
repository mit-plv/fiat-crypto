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
          {interp_base_type1 interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (interp_op1 : forall src dst, op src dst -> interp_flat_type interp_base_type1 src -> interp_flat_type interp_base_type1 dst)
          (interp_op2 : forall src dst, op src dst -> interp_flat_type interp_base_type2 src -> interp_flat_type interp_base_type2 dst)
          {R : forall t, interp_base_type1 t -> interp_base_type2 t -> Prop}
          (Rop : forall src dst op sv1 sv2, interp_flat_type_rel_pointwise R sv1 sv2
                                            -> interp_flat_type_rel_pointwise
                                                 R (interp_op1 src dst op sv1) (interp_op2 src dst op sv2)).

  Local Notation exprf1 := (@exprf base_type_code op interp_base_type1).
  Local Notation exprf2 := (@exprf base_type_code op interp_base_type2).
  Local Notation expr1 := (@expr base_type_code op interp_base_type1).
  Local Notation expr2 := (@expr base_type_code op interp_base_type2).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation interpf1 := (@interpf base_type_code interp_base_type1 op interp_op1).
  Local Notation interpf2 := (@interpf base_type_code interp_base_type2 op interp_op2).
  Local Notation interp1 := (@interp base_type_code interp_base_type1 op interp_op1).
  Local Notation interp2 := (@interp base_type_code interp_base_type2 op interp_op2).
  Local Notation Interp1 := (@Interp base_type_code interp_base_type1 op interp_op1).
  Local Notation Interp2 := (@Interp base_type_code interp_base_type2 op interp_op2).

  Lemma interp_flat_type_rel_pointwise_flatten_binding_list
        {t x x' T e1 e2}
        (Hpointwise : interp_flat_type_rel_pointwise R e1 e2)
        (HIn : List.In (existT (fun t : base_type_code => (interp_base_type1 t * interp_base_type2 t)%type) t (x, x')%core)
                       (flatten_binding_list (t:=T) e1 e2))
    : R t x x'.
  Proof.
    induction T; simpl in *; try tauto; [ | rewrite List.in_app_iff in HIn ];
      repeat first [ progress destruct_head or
                   | progress destruct_head False
                   | progress destruct_head and
                   | progress inversion_sigma
                   | progress inversion_prod
                   | progress subst
                   | solve [ eauto ] ].
  Qed.

  Local Hint Resolve List.in_app_or List.in_or_app interp_flat_type_rel_pointwise_flatten_binding_list.

  Section wf.
    Lemma interpf_wff
             {t} {e1 : exprf1 t} {e2 : exprf2 t}
             {G}
             (HG : forall t x x',
                 List.In (existT (fun t : base_type_code => (interp_base_type1 t * interp_base_type2 t)%type) t (x, x')%core) G
                 -> R t x x')
             (Rwf : wff G e1 e2)
    : interp_flat_type_rel_pointwise R (interpf1 e1) (interpf2 e2).
    Proof.
      induction Rwf; simpl; auto.
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
             {t} {e1 : expr1 t} {e2 : expr2 t}
             (Rwf : wf e1 e2)
    : interp_type_rel_pointwise R (interp1 e1) (interp2 e2).
    Proof.
      destruct Rwf; simpl; repeat intro; eauto.
    Qed.

    Lemma InterpWf
             {t} {e : Expr t}
             (Rwf : Wf e)
    : interp_type_rel_pointwise R (Interp1 e) (Interp2 e).
    Proof.
      unfold Interp, Wf in *; apply interp_wf; simpl; intuition.
    Qed.
  End wf.
End language.
