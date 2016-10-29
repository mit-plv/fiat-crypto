Require Import Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.WfRel.
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
          (Rop : forall src dst op sv1 sv2, interp_flat_type_rel_pointwise2 R sv1 sv2
                                            -> interp_flat_type_rel_pointwise2
                                                 R (interp_op1 src dst op sv1) (interp_op2 src dst op sv2)).

  Notation exprf1 := (@exprf base_type_code interp_base_type1 op interp_base_type1).
  Notation exprf2 := (@exprf base_type_code interp_base_type2 op interp_base_type2).
  Notation expr1 := (@expr base_type_code interp_base_type1 op interp_base_type1).
  Notation expr2 := (@expr base_type_code interp_base_type2 op interp_base_type2).
  Notation Expr1 := (@Expr base_type_code interp_base_type1 op).
  Notation Expr2 := (@Expr base_type_code interp_base_type2 op).
  Notation interpf1 := (@interpf base_type_code interp_base_type1 op interp_op1).
  Notation interpf2 := (@interpf base_type_code interp_base_type2 op interp_op2).
  Notation interp1 := (@interp base_type_code interp_base_type1 op interp_op1).
  Notation interp2 := (@interp base_type_code interp_base_type2 op interp_op2).
  Notation Interp1 := (@Interp base_type_code interp_base_type1 op interp_op1).
  Notation Interp2 := (@Interp base_type_code interp_base_type2 op interp_op2).

  Lemma interp_flat_type_rel_pointwise2_flatten_binding_list
        {t x x' T e1 e2}
        (Hpointwise : interp_flat_type_rel_pointwise2 R e1 e2)
        (HIn : List.In (existT (fun t : base_type_code => (interp_base_type1 t * interp_base_type2 t)%type) t (x, x')%core)
                       (flatten_binding_list base_type_code (t:=T) e1 e2))
    : R t x x'.
  Proof.
    induction T; simpl in *; [ | rewrite List.in_app_iff in HIn ];
      repeat first [ progress destruct_head or
                   | progress destruct_head False
                   | progress destruct_head and
                   | progress inversion_sigma
                   | progress inversion_prod
                   | progress subst
                   | solve [ eauto ] ].
  Qed.

  Local Hint Resolve List.in_app_or List.in_or_app interp_flat_type_rel_pointwise2_flatten_binding_list.

  Section wf.
    Lemma interpf_rel_wff
             {t} {e1 : exprf1 t} {e2 : exprf2 t}
             {G}
             (HG : forall t x x',
                 List.In (existT (fun t : base_type_code => (interp_base_type1 t * interp_base_type2 t)%type) t (x, x')%core) G
                 -> R t x x')
             (Rwf : rel_wff R G e1 e2)
    : interp_flat_type_rel_pointwise2 R (interpf1 e1) (interpf2 e2).
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

    Local Hint Resolve interpf_rel_wff.

    Lemma interp_rel_wf
             {t} {e1 : expr1 t} {e2 : expr2 t}
             {G}
             (HG : forall t x x',
                 List.In (existT (fun t : base_type_code => (interp_base_type1 t * interp_base_type2 t)%type) t (x, x')%core) G
                 -> R t x x')
             (Rwf : rel_wf R G e1 e2)
    : interp_type_rel_pointwise2 R (interp1 e1) (interp2 e2).
    Proof.
      induction Rwf; simpl; repeat intro; simpl in *; eauto.
      match goal with
      | [ H : _ |- _ ]
        => apply H; intros; progress destruct_head' or; [ | solve [ eauto ] ]
      end.
      inversion_sigma; inversion_prod; repeat subst; simpl; auto.
    Qed.

    Lemma InterpRelWf
             {t} {e1 : Expr1 t} {e2 : Expr2 t}
             (Rwf : RelWf R e1 e2)
    : interp_type_rel_pointwise2 R (Interp1 e1) (Interp2 e2).
    Proof.
      unfold Interp, RelWf in *; apply (interp_rel_wf (G:=nil)); simpl; intuition.
    Qed.
  End wf.
End language.
