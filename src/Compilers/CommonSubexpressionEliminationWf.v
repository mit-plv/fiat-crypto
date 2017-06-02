(** * Common Subexpression Elimination for PHOAS Syntax *)
Require Import Coq.Lists.List.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.AListContext.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Equality.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.WfProofs.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.CommonSubexpressionElimination.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Decidable.

Section symbolic.
  Context (base_type_code : Type)
          (op_code : Type)
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (op_code_beq : op_code -> op_code -> bool)
          (base_type_code_bl : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (op_code_bl : forall x y, op_code_beq x y = true -> x = y)
          (op_code_lb : forall x y, x = y -> op_code_beq x y = true)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (symbolize_op : forall s d, op s d -> op_code).
  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Context (normalize_symbolic_op_arguments : op_code -> symbolic_expr -> symbolic_expr)
          (inline_symbolic_expr_in_lookup : bool).

  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Notation symbolicify_smart_var := (@symbolicify_smart_var base_type_code op_code).
  Local Notation symbolize_exprf := (@symbolize_exprf base_type_code op_code op symbolize_op).
  Local Notation norm_symbolize_exprf := (@norm_symbolize_exprf base_type_code op_code op symbolize_op normalize_symbolic_op_arguments).
  Local Notation csef := (@csef base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation cse := (@cse base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation CSE := (@CSE base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op normalize_symbolic_op_arguments inline_symbolic_expr_in_lookup).
  Local Notation SymbolicExprContext := (@SymbolicExprContext base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl).
  Local Notation SymbolicExprContextOk := (@SymbolicExprContextOk base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl base_type_code_lb op_code_bl op_code_lb).
  Local Notation prepend_prefix := (@prepend_prefix base_type_code op).

  Local Instance base_type_code_dec : DecidableRel (@eq base_type_code)
    := dec_rel_of_bool_dec_rel base_type_code_beq base_type_code_bl base_type_code_lb.
  Local Instance op_code_dec : DecidableRel (@eq op_code)
    := dec_rel_of_bool_dec_rel op_code_beq op_code_bl op_code_lb.

  Section with_var.
    Context {var1 var2 : base_type_code -> Type}.

    Lemma wff_symbolize_exprf G t e1 e2
          (HG : forall t x y, List.In (existT _ t (x, y)) G -> snd x = snd y)
          (Hwf : wff G e1 e2)
      : @symbolize_exprf var1 t e1 = @symbolize_exprf var2 t e2.
    Proof.
      induction Hwf; simpl; erewrite_hyp ?* by eassumption; reflexivity.
    Qed.

    Lemma wff_norm_symbolize_exprf G t e1 e2
          (HG : forall t x y, List.In (existT _ t (x, y)) G -> snd x = snd y)
          (Hwf : wff G e1 e2)
      : @norm_symbolize_exprf var1 t e1 = @norm_symbolize_exprf var2 t e2.
    Proof.
      unfold norm_symbolize_exprf; erewrite wff_symbolize_exprf by eassumption; reflexivity.
    Qed.

    Local Arguments lookupb : simpl never.
    Local Arguments extendb : simpl never.
    Lemma wff_csef G G' t e1 e2
          (m1 : @SymbolicExprContext (interp_flat_type var1))
          (m2 : @SymbolicExprContext (interp_flat_type var2))
          (Hlen : length m1 = length m2)
          (Hm1m2None : forall t v, lookupb t m1 v = None <-> lookupb t m2 v = None)
          (Hm1m2Some : forall t v sv1 sv2,
              lookupb t m1 v = Some sv1
              -> lookupb t m2 v = Some sv2
              -> forall k,
                  List.In k (flatten_binding_list
                               (t:=t)
                               (symbolicify_smart_var sv1 v)
                               (symbolicify_smart_var sv2 v))
                  -> List.In k G)
          (HG : forall t x y, List.In (existT _ t (x, y)) G -> snd x = snd y)
          (HGG' : forall t x x', List.In (existT _ t (x, x')) G -> List.In (existT _ t (fst x, fst x')) G')
          (Hwf : wff G e1 e2)
      : wff G' (@csef var1 t e1 m1) (@csef var2 t e2 m2).
    Proof.
      revert dependent m1; revert m2; revert dependent G'.
      induction Hwf; simpl; intros G' HGG' m2 m1 Hlen Hm1m2None Hm1m2Some; try constructor; auto.
      { erewrite wff_norm_symbolize_exprf by eassumption.
        break_innermost_match;
          try match goal with
              | [ H : lookupb ?m1 ?x = Some ?k, H' : lookupb ?m2 ?x = None |- _ ]
                => apply Hm1m2None in H'; congruence
              end;
          lazymatch goal with
          | [ |- wff _ (LetIn _ _) (LetIn _ _) ]
            => constructor; intros; auto; []
          | _ => idtac
          end;
          match goal with H : _ |- _ => apply H end;
          try solve [ repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | progress destruct_head' or
                       | solve [ eauto ]
                       | progress intros
                       | match goal with
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => solve [ destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H); eauto ]
                         | [ H : List.In _ (flatten_binding_list (symbolicify_smart_var ?x1 ?v) (symbolicify_smart_var ?x2 ?v)) |- _ ]
                           => exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H)
                         | [ H : context[lookupb (extendb _ _ _) _] |- _ ]
                           => rewrite (fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk) in H
                         end
                       | rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk)
                       | break_innermost_match_step
                       | break_innermost_match_hyps_step
                       | progress simpl in *
                       | solve [ intuition (eauto || congruence) ]
                       | match goal with
                         | [ H : forall t x y, _ |- _ ] => specialize (fun t x0 x1 y0 y1 => H t (x0, x1) (y0, y1)); cbn [fst snd] in H
                         | [ H : In (existT _ ?t (?x, ?x')) (flatten_binding_list (symbolicify_smart_var _ _) (symbolicify_smart_var _ _)),
                                 Hm1m2Some : forall t v sv1 sv2, _ -> _ -> forall k', In k' (flatten_binding_list _ _) -> In k' ?G |- _ ]
                           => is_var x; is_var x';
                              lazymatch goal with
                              | [ H : In (existT _ t ((fst x, _), (fst x', _))) G |- _ ] => fail
                              | _ => let H' := fresh in
                                     refine (let H' := flatten_binding_list_SmartVarfMap2_pair_in_generalize2 H _ _ in _);
                                     destruct H' as [? [? H']];
                                     eapply Hm1m2Some in H'; [ | eassumption.. ]
                              end
                         end ] ].
         repeat first [ progress unfold symbolize_var
                       | rewrite Hlen
                       | progress subst
                       | setoid_rewrite length_extendb
                       | setoid_rewrite List.in_app_iff
                       | progress destruct_head' or
                       | solve [ eauto ]
                       | progress intros ].
         (** FIXME: This actually isn't true, because the symbolic
             expr stored in G might not be the same as the one in the
             expression tree, when the one in the expression tree is a
             fresh var *)
         admit. }
    Admitted.

    Lemma wff_prepend_prefix {var1' var2'} prefix1 prefix2 G t e1 e2
          (Hlen : length prefix1 = length prefix2)
          (Hprefix : forall n t1 t2 e1 e2,
              nth_error prefix1 n = Some (existT _ t1 e1)
              -> nth_error prefix2 n = Some (existT _ t2 e2)
              -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)
          (Hwf : wff G e1 e2)
      : wff G (@prepend_prefix var1' t e1 prefix1) (@prepend_prefix var2' t e2 prefix2).
    Proof.
      revert dependent G; revert dependent prefix2; induction prefix1, prefix2; simpl; intros Hlen Hprefix G Hwf; try congruence.
      { pose proof (Hprefix 0) as H0; specialize (fun n => Hprefix (S n)).
        destruct_head sigT; simpl in *.
        specialize (H0 _ _ _ _ eq_refl eq_refl); destruct_head ex; subst; simpl in *.
        constructor.
        { eapply wff_in_impl_Proper; [ eassumption | simpl; tauto ]. }
        { intros.
          apply IHprefix1; try congruence; auto.
          eapply wff_in_impl_Proper; [ eassumption | simpl; intros; rewrite in_app_iff; auto ]. } }
    Qed.

    Lemma wf_cse prefix1 prefix2 t e1 e2 (Hwf : wf e1 e2)
          (Hlen : length prefix1 = length prefix2)
          (Hprefix : forall n t1 t2 e1 e2,
              nth_error prefix1 n = Some (existT _ t1 e1)
              -> nth_error prefix2 n = Some (existT _ t2 e2)
              -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)
      : wf (@cse var1 prefix1 t e1 empty) (@cse var2 prefix2 t e2 empty).
    Proof.
      destruct Hwf; simpl; constructor; intros.
      lazymatch goal with
      | [ |- wff (flatten_binding_list (t:=?src) ?x ?y) (csef _ (extendb _ ?n ?v)) (csef _ (extendb _ ?n' ?v')) ]
        => unify n n';
             apply wff_csef with (G:=flatten_binding_list (t:=src) (symbolicify_smart_var v n) (symbolicify_smart_var v' n'))
      end.
      { setoid_rewrite length_extendb; reflexivity. }
      { intros; rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk).
        break_innermost_match; subst; simpl; intuition (eauto || congruence). }
      { intros *; rewrite !(fun var => @lookupb_extendb_full flat_type _ symbolic_expr _ var _ SymbolicExprContextOk).
        break_innermost_match; subst; simpl; try setoid_rewrite lookupb_empty; eauto using SymbolicExprContextOk; try congruence. }
      { intros *; intro H'; exact (flatten_binding_list_SmartVarfMap2_pair_same_in_eq2 H'). }
      { intros *; intro H'; destruct (flatten_binding_list_SmartVarfMap2_pair_In_split H'); eauto. }
      { apply wff_prepend_prefix; auto. }
    Qed.
  End with_var.

  Lemma Wf_CSE t (e : Expr t)
        (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
        (Hlen : forall var1 var2, length (prefix var1) = length (prefix var2))
        (Hprefix : forall var1 var2 n t1 t2 e1 e2,
            nth_error (prefix var1) n = Some (existT _ t1 e1)
            -> nth_error (prefix var2) n = Some (existT _ t2 e2)
            -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)
        (Hwf : Wf e)
    : Wf (@CSE t e prefix).
  Proof.
    intros var1 var2; apply wf_cse; eauto.
  Qed.
End symbolic.

Hint Resolve Wf_CSE : wf.
