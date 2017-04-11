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
Require Import Crypto.Compilers.CommonSubexpressionEliminationWf.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
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
          (interp_base_type : base_type_code -> Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (interp_op : forall s d (opc : op s d), interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d)
          (symbolize_op : forall s d, op s d -> op_code).

  Local Notation symbolic_expr := (symbolic_expr base_type_code op_code).
  Local Notation symbolic_expr_beq := (@symbolic_expr_beq base_type_code op_code base_type_code_beq op_code_beq).
  Local Notation symbolic_expr_lb := (@internal_symbolic_expr_dec_lb base_type_code op_code base_type_code_beq op_code_beq base_type_code_lb op_code_lb).
  Local Notation symbolic_expr_bl := (@internal_symbolic_expr_dec_bl base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op_code_bl).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation interp_type := (interp_type interp_base_type).
  Local Notation interp_flat_type_gen := interp_flat_type.
  Local Notation interp_flat_type := (interp_flat_type interp_base_type).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Local Notation symbolicify_smart_var := (@symbolicify_smart_var base_type_code op_code).
  Local Notation symbolize_exprf := (@symbolize_exprf base_type_code op_code op symbolize_op).
  Local Notation csef := (@csef base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op).
  Local Notation cse := (@cse base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op).
  Local Notation CSE := (@CSE base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl op symbolize_op).
  Local Notation SymbolicExprContext := (@SymbolicExprContext base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl).
  Local Notation SymbolicExprContextOk := (@SymbolicExprContextOk base_type_code op_code base_type_code_beq op_code_beq base_type_code_bl base_type_code_lb op_code_bl op_code_lb).
  Local Notation prepend_prefix := (@prepend_prefix base_type_code op).

  Local Instance base_type_code_dec : DecidableRel (@eq base_type_code)
    := dec_rel_of_bool_dec_rel base_type_code_beq base_type_code_bl base_type_code_lb.
  Local Instance op_code_dec : DecidableRel (@eq op_code)
    := dec_rel_of_bool_dec_rel op_code_beq op_code_bl op_code_lb.

  Lemma interpf_flatten_binding_list T t x y v s
        (H : List.In (existT _ t (x, y)) (flatten_binding_list (var2:=interp_base_type) (t:=T) (symbolicify_smart_var v s) v))
    : fst x = y.
  Proof.
    revert dependent s; induction T;
      repeat first [ progress simpl in *
                   | reflexivity
                   | tauto
                   | progress destruct_head or
                   | progress inversion_sigma
                   | progress inversion_prod
                   | progress subst
                   | rewrite List.in_app_iff in *
                   | progress intros
                   | solve [ eauto ] ].
  Qed.

  Local Arguments lookupb : simpl never.
  Local Arguments extendb : simpl never.
  Lemma interpf_csef G t e1 e2
        (HG : forall t x y, In (existT _ t (x, y)) G -> fst x = y)
        (m : @SymbolicExprContext (interp_flat_type_gen _))
        (Hwf : wff G e1 e2)
    : interpf interp_op (@csef interp_base_type t e1 m) = interpf interp_op e2.
  Proof.
      revert dependent m;
        induction Hwf; simpl; cbv [LetIn.Let_In symbolize_var]; intros; eauto;
          rewrite_hyp ?* by eauto; try reflexivity; eauto.
      { break_match.
        { break_match_hyps; try congruence; inversion_prod; inversion_option; subst.
          erewrite_hyp *; [ reflexivity | ].
          setoid_rewrite in_app_iff; intros; destruct_head or; eauto; [].
          specialize_by eauto.
          admit. }
        { simpl; unfold LetIn.Let_In.
          rewrite_hyp !* by eauto.
          erewrite_hyp *; [ reflexivity | ].
          setoid_rewrite in_app_iff; intros; destruct_head or; eauto; [].
          eauto using interpf_flatten_binding_list. } }
  Admitted.

  Lemma interpf_prepend_prefix t e prefix
    : interpf interp_op (@prepend_prefix _ t e prefix) = interpf interp_op e.
  Proof.
    induction prefix; simpl; [ reflexivity | unfold LetIn.Let_In; assumption ].
  Qed.

  Lemma interp_cse prefix t e1 e2
        (Hwf : wf e1 e2)
    : forall x, interp interp_op (@cse interp_base_type prefix t e1 empty) x = interp interp_op e2 x.
  Proof.
    destruct Hwf; simpl; intros.
    etransitivity; [ | eapply interpf_prepend_prefix ].
    eapply interpf_csef; eauto;
      [
      | eapply wff_prepend_prefix; [ .. | solve [ eauto ] ] ].
    { intros; eapply interpf_flatten_binding_list; eassumption. }
    { admit. }
    { admit. }
  Admitted.

  Lemma InterpCSE t (e : Expr t)
        (prefix : forall var, list (sigT (fun t : flat_type => @exprf var t)))
        (*(Hlen : forall var1 var2, length (prefix var1) = length (prefix var2))
        (Hprefix : forall var1 var2 n t1 t2 e1 e2,
            nth_error (prefix var1) n = Some (existT _ t1 e1)
            -> nth_error (prefix var2) n = Some (existT _ t2 e2)
            -> exists pf : t1 = t2, wff nil (eq_rect _ exprf e1 _ pf) e2)*)
        (Hwf : Wf e)
    : forall x, Interp interp_op (@CSE t e prefix) x = Interp interp_op e x.
  Proof.
    apply interp_cse; auto.
  Qed.
End symbolic.
